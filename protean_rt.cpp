#include <stdint.h>
#include <assert.h>
#include <dlfcn.h>
#include <sys/user.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <errno.h>
#include <link.h>
#include <elf.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

#include <sstream>
#include <vector>
#include <stack>
#include <unordered_map>
#include <algorithm>
#include <limits>

#include <llvm/CodeGen/MachineCodeInfo.h>
#include <llvm/CodeGen/MachineScheduler.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/ExecutionEngine/JITMemoryManager.h>
#include <llvm/PassManager.h>
#include <llvm/Support/DynamicLibrary.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>

#include "../common/protean_common.hpp"
#include "Optimizer.hpp"

#include <string>
#include <vector>
#include <map>

struct OptimizationManager;
static OptimizationManager* optman = NULL;

static std::ofstream ofs ("proteanBBprof.txt", std::ofstream::out);
static std::map<std::string, std::vector<int>> prof_map;


#define PROTEAN_RT_SELFID (pthread_self())
#define PROTEAN_RT_TIMER (elapsed_time())

#define PROTEAN_IR_BACKING_FILE "tmp.protean.bc" // FIXME: do this with mktemp


static pid_t parent_tid;
static pid_t child_tid;

static double tbegin = 0.0;
double timer(){
    struct timeval timestr;
    struct timezone* tzp = 0;
    gettimeofday(&timestr, tzp);
    return (double)timestr.tv_sec + 1.0E-06*(double)timestr.tv_usec;
}
double elapsed_time(){
    return timer() - tbegin;
}

static int pgsz = 0;
uint64_t align_prev_page(uint64_t a){
    return (a & ~(pgsz-1));
}
uint64_t align_next_page(uint64_t a){
    return align_prev_page(a) + pgsz;
}

// mmap a region of existing memory, keeping the region's contents in tact
void mmap_anon_current_memory(uint64_t begin, uint64_t end){
    assert(0 == child_tid && "Cannot call this function once RT process is fork'ed");
    uint8_t* saveit = new uint8_t[end - begin];
    memcpy((void*)saveit, (void*)begin, end - begin);

    void* ret = mmap((void*)begin, (end - begin), PROT_READ|PROT_WRITE|PROT_EXEC, MAP_ANON|MAP_SHARED|MAP_FIXED, -1, 0);
    DEBUG(PROTEAN_RT_COUT << "mmap'ed region: [" << std::hex << begin << "," << end << ")" << std::endl);
    if (MAP_FAILED == ret){
        perror("mmap failed");
        exit(1);
    }
    assert((uint64_t)ret == begin && "mmap didn't honor FIXED directive?");

    memcpy((void*)begin, (void*)saveit, end - begin);
    delete[] saveit;
}

uint32_t countLoadInstructions(llvm::Function* f){
    // for each BasicBlock
    std::vector<llvm::LoadInst*> allLoads;
    for (llvm::Function::iterator fit = f->getBasicBlockList().begin(); fit != f->getBasicBlockList().end(); fit++){ 
        llvm::BasicBlock* bbl = fit;

        // for each Instruction
        for (llvm::BasicBlock::iterator bit = bbl->begin(); bit != bbl->end(); bit++){
            llvm::Instruction* insn = bit;
            if (insn->getOpcode() == llvm::Instruction::Load && insn->mayReadFromMemory()){
                llvm::LoadInst* li = llvm::dyn_cast<llvm::LoadInst>(insn);
                assert(li);
                allLoads.push_back(li);
            }
        }
    }
    return allLoads.size();
}

template<typename A, typename B> std::pair<B,A> flip_pair(const std::pair<A,B> &p)
{
    return std::pair<B,A>(p.second, p.first);
}

template<typename A, typename B> std::multimap<B,A> flip_map(const std::map<A,B> &src)
{
    std::multimap<B,A> dst;
    std::transform(src.begin(), src.end(), std::inserter(dst, dst.begin()), 
                   flip_pair<A,B>);
    return dst;
}


struct MappedMemBlock {
private:
    uint8_t* Raw;
    uint32_t Size;
    uint32_t Current;
    bool anonMmap() {
        uint64_t ab = align_next_page((uint64_t)Raw);
        uint64_t ae = align_prev_page((uint64_t)Raw + Size);
        void* ret = mmap((void*)ab, (ae - ab), PROT_READ|PROT_WRITE|PROT_EXEC, MAP_ANON|MAP_SHARED|MAP_FIXED, -1, 0);
        DEBUG(PROTEAN_RT_COUT << "mmap'ed region: [" << std::hex << ab << "," << ae << ")" << std::endl);
        if (MAP_FAILED == ret){
            perror("mmap failed");
            exit(1);
        }
        assert((uint64_t)ret == ab && "mmap didn't honor FIXED directive?");
        
        return true;
    }
public:
    MappedMemBlock(uint32_t s):Size(s),Current(0) {
        Raw = new uint8_t[Size]; 
        assert(Raw);
        
        anonMmap();
        // lose space at the beginning and end of the slab to make the mapping safe from overlap
        alignCurrent(pgsz);
        Size -= pgsz;
    }
    ~MappedMemBlock(){ if (Raw) delete[] Raw; }
    uint8_t* stream() const { return &(Raw[Current]); }
    uint32_t size() const { return Size; }
    uint8_t* take(uint32_t amt) {
        uint8_t* c = &(Raw[Current]);
        DEBUG(PROTEAN_RT_COUT << "Allocating memory [0x" << std::hex << (uint64_t)c << "," << (uint64_t)c + amt << ")" << std::endl);
        Current += amt;
        assert(Current < Size && "This MappedMemBlock is out of memory");
        return c;
    }
    void alignCurrent(uint32_t a) {
        uint32_t m = ((uint64_t)(&(Raw[Current]))) % a;
        if (m > 0) take(a - m);
    }
};


struct Symbol {
public:
    Elf64_Sym base;
    std::string name;
    Symbol(std::string n, Elf64_Sym* s) {
        name.append(n);
        memcpy(&base, s, sizeof(Elf64_Sym));
    }
    ~Symbol() {}
    void print(){
        PROTEAN_RT_COUT << "Symbol " << name
                << "\tvalue=" << std::hex << getValue()
                << std::endl;
    }
    uint64_t getValue(){
        return base.st_value;
    }
};

struct SelfElf {
private:
    static const uint32_t __SELFELF_BUF_SIZE = 2048;

    std::unordered_map<std::string, std::vector<Symbol*> > SymbolMap;
    std::string Path;

public:
    uint32_t IRSize;
    uint8_t* IRBytes;
    bool GzippedIR;

    std::string& getPath() { return Path; }
    
    SelfElf(){
        char* buf = new char[__SELFELF_BUF_SIZE];

        int ret = readlink("/proc/self/exe", buf, __SELFELF_BUF_SIZE-1);
        PROTEAN_RT_COUT << "Program executable is in " << buf << std::endl;
        Path.append(buf);

        std::ifstream elffile (buf, std::ios::in | std::ios::binary | std::ios::ate);
        delete[] buf;

        char* fileContents;
        assert(elffile.is_open() && "Problem opening this program's file on disk");
        std::ifstream::pos_type fsize = elffile.tellg();
        char* elfcontent = new char[fsize];

        elffile.seekg(0, std::ios::beg);
        if (0 == elffile.read(elfcontent, fsize)){
            PROTEAN_RT_COUT << "file read operation failed on " << Path << std::endl;
            exit(1);
        }
        elffile.close();

        // FIXME: about to skip a bunch of error checking
        Elf64_Ehdr* ehdr = (Elf64_Ehdr*)(&elfcontent[0]);
        uint32_t shbase = ehdr->e_shoff;
        Elf64_Shdr* shstrh = (Elf64_Shdr*)(&elfcontent[shbase + (ehdr->e_shstrndx * ehdr->e_shentsize)]);
        char* shstrtab = (char*)(&elfcontent[shstrh->sh_offset]);

        // find all symbol tables and the .protean_ir section
        std::vector<Elf64_Shdr*> symtabs;
        Elf64_Shdr* proteanir = NULL;
        GzippedIR = false;
        for (uint32_t i = 0; i < ehdr->e_shnum; i++){
            DEBUG(PROTEAN_RT_COUT << "Section " << std::dec << i << " is at offset " << std::hex << shbase + (i * ehdr->e_shentsize) << std::endl);
            Elf64_Shdr* cur = (Elf64_Shdr*)(&elfcontent[shbase + (i * ehdr->e_shentsize)]);
            char* secname = (shstrtab + cur->sh_name);
            if (cur->sh_type == SHT_DYNSYM || cur->sh_type == SHT_SYMTAB){
                symtabs.push_back(cur);
            }

            if (0 == strcmp(secname, ".protean_ir")){
                DEBUG(PROTEAN_RT_COUT << "\t\tfound protean IR at section " << std::dec << i << std::endl);
                proteanir = cur;
                GzippedIR = false;
            } else if (0 == strcmp(secname, ".protean_ir.gz")){
                DEBUG(PROTEAN_RT_COUT << "\t\tfound protean IR at section " << std::dec << i << std::endl);
                proteanir = cur;
                GzippedIR = true;
            }
        }
            
        for (std::vector<Elf64_Shdr*>::const_iterator it = symtabs.begin(); it != symtabs.end(); it++){
            Elf64_Shdr* cur = *it;
            char* content = (char*)(&elfcontent[cur->sh_offset]);
            Elf64_Shdr* strh = (Elf64_Shdr*)(&elfcontent[shbase + (cur->sh_link * ehdr->e_shentsize)]);
            char* strtab = (char*)(&elfcontent[strh->sh_offset]);

            uint32_t curbyt = 0;
            while (curbyt < cur->sh_size){
                Elf64_Sym* sym = (Elf64_Sym*)(content + curbyt);
                if (0 != sym->st_name){
                    char* name = strtab + sym->st_name;
                    std::string n(name);

                    Symbol* s = new Symbol(n, sym);
                    DEBUG(s->print());
                    if (SymbolMap.count(n) == 0){
                        SymbolMap[n] = std::vector<Symbol*>();
                    }
                    SymbolMap[n].push_back(s);
                }
                curbyt += cur->sh_entsize;
            }
        }

        assert(proteanir && "no .protean_ir section found in this program");
        IRSize = proteanir->sh_size;
        IRBytes = new uint8_t[IRSize];
        memcpy(IRBytes, (void*)(&elfcontent[proteanir->sh_offset]), IRSize);
    }

    ~SelfElf(){
        if (IRBytes) delete[] IRBytes;
        for (std::unordered_map<std::string, std::vector<Symbol*> >::const_iterator it = SymbolMap.begin(); it != SymbolMap.end(); it++){
            std::vector<Symbol*> symlist = it->second;
            for (std::vector<Symbol*>::const_iterator iit = symlist.begin(); iit != symlist.end(); iit++){
                Symbol* sym = *iit;
                if (sym) delete sym;
            }
        }
    }
    uint32_t getMagicSymbols(std::vector<Symbol*>& symlist){
        assert(0 == symlist.size());
        for (std::unordered_map<std::string, std::vector<Symbol*> >::const_iterator it = SymbolMap.begin(); it != SymbolMap.end(); it++){
            std::string name = it->first;
            std::vector<Symbol*> magicsyms = it->second;
            if (name.compare(0, strlen(PROTEAN_MAGIC_PREF), PROTEAN_MAGIC_PREF) == 0){
                std::unordered_map<uint64_t, bool> values;
                for (std::vector<Symbol*>::const_iterator iit = magicsyms.begin(); iit != magicsyms.end(); iit++){
                    Symbol* sym = *iit;
                    if (sym->getValue() != 0){
                        if (values.count(sym->getValue()) == 0){
                            symlist.push_back(magicsyms[0]);
                            values[sym->getValue()] = true;
                        }
                    }
                }
            }
        }
        return symlist.size();
    }

    Symbol* lookupSymbol(std::string name){
        if (SymbolMap.count(name) == 0){
            return NULL;
        }
        std::vector<Symbol*> symlist = SymbolMap[name];
        assert(symlist.size() >= 1);
        // FIXME: search for a "best" symbol? (e.g., value != 0)
        Symbol* sym = symlist[0];
        DEBUG(sym->print());
        return sym;
    }
};

static uint64_t unq_tag = 0;

struct FunctionVar {
private:
    std::string name;
    uint32_t index;
    uint64_t* funcptr;
    uint64_t faddr;
    uint32_t fsize;
    Symbol* symbol;
    uint64_t tag;
    uint64_t version;

    llvm::Function* function;
    float qos;
    float app_ipc;
    uint32_t searchIndex;

public:
    FunctionVar(Symbol* sym, uint32_t idx){
        symbol = sym;
        name.append(symbol->name.substr(strlen(PROTEAN_MAGIC_PREF), std::string::npos));
        index = idx;
        funcptr = (uint64_t*)symbol->getValue();
        faddr = getTarget();
        fsize = 0;
        tag = 0;

        qos = -1.0;
        app_ipc = -1.0;
        function = NULL;
        searchIndex = 0;
    }

    uint64_t getVersion(){
        return version;
    }

    uint32_t getSearchIndex(){
        return searchIndex;
    }

    void setLLVMFunction(llvm::Function* f){
        assert(NULL == function);
        assert(NULL != f);
        function = f;
    }

    llvm::Function* getLLVMFunction(){
        return function;
    }

    FunctionVar(Symbol* sym, uint32_t idx, uint64_t vr, llvm::Function* f){
        symbol = sym;
        name.append(symbol->name.substr(strlen(PROTEAN_MAGIC_PREF), std::string::npos));
        index = idx;
        funcptr = (uint64_t*)symbol->getValue();
        faddr = getTarget();
        fsize = 0;
        version = vr;

        assert(f != NULL);
        function = f;

        assignTag();
    }

    ~FunctionVar() {}

    void assignTag(){
        unq_tag++;
        version = unq_tag;
    }

    uint32_t getTag(){
        return version;
    }

    Symbol* getSymbol(){
        return symbol;
    }

    uint64_t getOrigAddress(){
        return faddr;
    }

    uint32_t getOrigSize(){
        return fsize;
    }

    bool inOrigRange(uint64_t addr){
        return (addr >= faddr && addr < (faddr + fsize));
    }

    void setOrigSize(uint32_t sz){
        fsize = sz;
    }

    uint64_t getLocation(){
        return (uint64_t)funcptr;
    }

    uint64_t getTarget(){
        return (uint64_t)(*funcptr);
    }

    std::string& getName(){
        return name;
    }

    void setTarget(uint64_t tgt){
#ifdef KEEP_ORIGINAL_FUNCTIONS
        PROTEAN_RT_COUT << "Compiled with -DKEEP_ORIGINAL_FUNCTIONS. skipping redirection step!" << std::endl;
#else
        *(funcptr) = tgt; 
#endif
    }

    void print(){
        PROTEAN_RT_COUT << "[" << std::dec << index << "]\t"
                << name << "V" << std::dec << version << " @ "
                << std::hex << "0x" << getLocation() << "\t"
                << "0x" << getTarget() << "\t"
                << "[" << getOrigAddress() << "," << getOrigAddress() + getOrigSize() << "]" << std::endl;
    }
};

// Very simple memory manager that neither tracks nor reclaims allocated memory.
// However, it allocates all memory at constructor-time and that memory is anonymously
// mmapped so that fork'ed children will see it also.
class SimpleJITMemoryManager : public llvm::JITMemoryManager {
private:
#define DefineAllocator(__mem)                                          \
    MappedMemBlock* Mem ## __mem;                                       \
    uint8_t* AllocateFrom ## __mem(uint32_t size, uint32_t align){      \
        assert(Mem ## __mem != NULL && "MappedMemBlock should be initialized"); \
        DEBUG(PROTEAN_RT_COUT << "SimpleJITMemoryManager allocating memory for " # __mem << "\tsize=" << std::dec << size << "\talign=" << align << std::endl); \
        return AllocateFrom(Mem ## __mem, size, align);                 \
    }

    DefineAllocator(GOT);
    DefineAllocator(Code);
    DefineAllocator(Data);
    DefineAllocator(Stub);
    
    bool BuildingFunction;

    static uint8_t* AllocateFrom(MappedMemBlock* mem, uint32_t size, uint32_t align){
        assert(mem != NULL);
        mem->alignCurrent(align);
        return mem->take(size);
    }

#define MinCodeBlockSize (4096)
    static const uint32_t DefaultAlign = 16;
    static const uint32_t SizeGOT = (64 * __KB);
    static const uint32_t SizeCode = (32 * __MB);
    static const uint32_t SizeData = (8 * __MB);
    static const uint32_t SizeStub = (1 * __MB);

public:
    static SimpleJITMemoryManager* CreateDefaultMemManager() { return new SimpleJITMemoryManager(); }

    SimpleJITMemoryManager() :
        JITMemoryManager(),
        MemGOT(NULL), MemCode(NULL), MemData(NULL), MemStub(NULL),
        BuildingFunction(false)
    {
        DEBUG(PROTEAN_RT_COUT << "creating SimpleJITMemoryManager with region sizes " << std::dec
                  << "\tGOT=" << SizeGOT
                  << "\tCode=" << SizeCode
                  << "\tData=" << SizeData
                  << "\tStub=" << SizeStub
                  << std::endl);
        MemGOT = new MappedMemBlock(SizeGOT);
        MemCode = new MappedMemBlock(SizeCode);
        MemData = new MappedMemBlock(SizeData);
        MemStub = new MappedMemBlock(SizeStub);

        HasGOT = false;
    }
    virtual ~SimpleJITMemoryManager(){
        if (MemGOT)  delete MemGOT;
        if (MemCode) delete MemCode;
        if (MemData) delete MemData;
        if (MemStub) delete MemStub;
    }
    
    void setMemoryWritable() { return; }
    void setMemoryExecutable() { return; }

    void AllocateGOT(){
        assert(false == HasGOT && "Cannot allocate GOT more than once");
        HasGOT = true;
        DEBUG(PROTEAN_RT_COUT << "SimpleJITMemoryManager taking control of GOT" << std::endl);
    }
    uint8_t* getGOTBase() const {
        if (NULL == MemGOT) return NULL;
        return MemGOT->stream();
    }

    uint8_t* startFunctionBody(const llvm::Function* F, uintptr_t& ActualSize){
        assert(false == BuildingFunction && "must call endFunctionBody before starting another Function");
        DEBUG(PROTEAN_RT_COUT << "startFunctionBody " << F->getName().data() << std::endl);
        uint32_t size = std::max<uint32_t>(MinCodeBlockSize, ActualSize);
        uint8_t* loc = AllocateFromCode(size, DefaultAlign);
        assert(loc && "Problem 'allocating' memory");
        ActualSize = size;
        BuildingFunction = true;
        return loc;
    }
    uint8_t* allocateStub(const llvm::GlobalValue* F, unsigned StubSize, unsigned Alignment){
        uint8_t* loc = AllocateFromStub(StubSize, Alignment);
        assert(loc && "Problem 'allocating' memory");
        return loc;
    }
    void endFunctionBody(const llvm::Function* F, uint8_t* FunctionStart, uint8_t* FunctionEnd){
        assert(true == BuildingFunction && "Cannot call this method without first calling startFunctionBody");
        DEBUG(PROTEAN_RT_COUT << "endFunctionBody " << F->getName().data() << std::endl);
        BuildingFunction = false;
    }
    uint8_t* allocateSpace(intptr_t Size, unsigned Alignment){
        assert(false == BuildingFunction && "Cannot call this method between startFunctionBody and endFunctionBody");
        uint8_t* loc = AllocateFromCode(Size, Alignment);
        assert(loc && "Problem 'allocating' memory");
        return loc;
    }
    uint8_t* allocateGlobal(uintptr_t Size, unsigned Alignment){
        uint8_t* loc = AllocateFromData(Size, Alignment);
        DEBUG(PROTEAN_RT_COUT << "allocateGlobal" << std::endl);
        assert(loc && "Problem 'allocating' memory");
        return loc;
    }
    void deallocateFunctionBody(void* Body){ return; } // does nothing (for now)
    uint8_t* allocateCodeSection(uintptr_t Size, unsigned Alignment, unsigned SectionID){
        uint8_t* loc = AllocateFromCode(Size, Alignment);
        assert(loc && "Problem 'allocating' memory");
        return loc;
    }
    uint8_t* allocateDataSection(uintptr_t Size, unsigned Alignment, unsigned SectionID, bool IsReadOnly){
        uint8_t* loc = AllocateFromData(Size, Alignment);
        DEBUG(PROTEAN_RT_COUT << "allocateDataSection" << std::endl);
        assert(loc && "Problem 'allocating' memory");
        return loc;
    }
    void* getPointerToNamedFunction(const std::string& Name, bool AbortOnFailure = true){
        DEBUG(PROTEAN_RT_COUT << "Searching for function in SimpleJITMemoryManager: " << Name << std::endl);

        // this code is copied directly from llvm::DefaultJITMemoryHandler (anonymous)
        // it is not clear to me why the memory manager handles these...
        /*
        if (Name == "exit") return (void*)(intptr_t)&jit_exit;
        if (Name == "atexit") return (void*)(intptr_t)&jit_atexit;
        if (Name == "__main") return (void*)(intptr_t)&jit_noop;
        */

        const char *NameStr = Name.c_str();
        if (NameStr[0] == 1) ++NameStr;

        void *Ptr = llvm::sys::DynamicLibrary::SearchForAddressOfSymbol(NameStr);
        if (Ptr) return Ptr;

        if (NameStr[0] == '_') {
            Ptr = llvm::sys::DynamicLibrary::SearchForAddressOfSymbol(NameStr+1);
            if (Ptr) return Ptr;
        }
        if (AbortOnFailure){
            assert(false && "Cannot find a result for getPointerToNamedFunction");
        }
        return 0;
    }
    bool applyPermissions(std::string* ErrMsg = 0){
        return false;
    }
    uint8_t* startExceptionTable(const llvm::Function* F, uintptr_t& ActualSize){
        return startFunctionBody(F, ActualSize);
    }
    void endExceptionTable(const llvm::Function* F, uint8_t* TableStart, uint8_t* TableEnd, uint8_t* FrameRegister){
        endFunctionBody(F, TableStart, TableEnd);
    }
    void deallocateExceptionTable(void* ET){
        deallocateFunctionBody(ET);
    }

    // these seem to be debug functions so they are stubbed
    void setPoisonMemory(bool poison) { return; }
    bool CheckInvariants(std::string& ErrorStr) { return true; }
    size_t GetDefaultCodeSlabSize() { return 0; }
    size_t GetDefaultDataSlabSize() { return 0; }
    size_t GetDefaultStubSlabSize() { return 0; }
    unsigned GetNumCodeSlabs() { return 1; }
    unsigned GetNumDataSlabs() { return 1; }
    unsigned GetNumStubSlabs() { return 1; }
};

struct OptimizationManager {
private:

    std::vector<FunctionVar*> funcs;
    std::map<uint64_t, FunctionVar*> fmap;
    llvm::Module* module;
    llvm::ExecutionEngine* execengine;
    llvm::LLVMContext* context;
    SimpleJITMemoryManager* jmm;
    SelfElf* selfelf;
    void* dlhandle;
    uint32_t uniqueFunctions;

public:
    Optimizer* optimizer;

    uint32_t countUniqueFunctions(){
        return uniqueFunctions;
    }

    void shared_memory_init(){
        jmm = SimpleJITMemoryManager::CreateDefaultMemManager();
    }

    void JIT_init(){
        llvm::TimePassesIsEnabled = true; // inert?
        llvm::llvm_start_multithreaded();
        llvm::InitializeNativeTarget();
        llvm::InitializeNativeTargetAsmPrinter();
        llvm::InitializeNativeTargetAsmParser();

        context = new llvm::LLVMContext();
        PROTEAN_RT_COUT << "JIT_init: Initialized LLVM objects" << std::endl;

        FILE* tmpf = fopen(PROTEAN_IR_BACKING_FILE, "w");
        assert(tmpf && "Cannot open backing file");
        fwrite(selfelf->IRBytes, sizeof(uint8_t), selfelf->IRSize, tmpf);
        fclose(tmpf);
        PROTEAN_RT_COUT << "JIT_init: Wrote IR backing file" << std::endl;

        if (true == selfelf->GzippedIR){
            PROTEAN_RT_COUT << "Uncompressing IR found in executable" << std::endl;
            int ret = 0;
            char* cmd = new char[__KB];

            sprintf(cmd, "mv %s %s.gz", PROTEAN_IR_BACKING_FILE, PROTEAN_IR_BACKING_FILE);
            ret = system(cmd);
            assert(ret == 0 && "Problem moving gzipped IR file");

            sprintf(cmd, "gunzip %s.gz", PROTEAN_IR_BACKING_FILE);
            ret = system(cmd);
            assert(ret == 0 && "Problem running gunzip on IR file");

            delete[] cmd;
        }
        PROTEAN_RT_COUT << "JIT_init: Parsing IR" << std::endl;

        llvm::SMDiagnostic Err;
        module = llvm::ParseIRFile(PROTEAN_IR_BACKING_FILE, Err, *context);
        assert(module);
        unlink(PROTEAN_IR_BACKING_FILE);
        PROTEAN_RT_COUT << "JIT_init: Parsed IR backing file" << std::endl;

        optimizer = new InertOptimizer(*module, 0);

        std::string error;
        llvm::EngineBuilder eb = llvm::EngineBuilder(module);

        // possible arguments are llvm::CodeGenOpt::None, llvm::CodeGenOpt::Less, llvm::CodeGenOpt::Default, llvm::CodeGenOpt::Aggressive
        eb.setOptLevel(llvm::CodeGenOpt::Default); // default optimization level for code gen
        eb.setUseMCJIT(false); // using MCJIT causes crashes

        // `llvm-as < /dev/null | opt -O2 -std-compile-opts -disable-output -debug-pass=Arguments' to get flags used for -O2
        // `llvm-as < /dev/null | llc -mcpu=help' to get a list of valid CPUs
        //eb.setMCPU("nehalem"); // "nehalem" turns off AVX (for sphinx3)
        //llvm::TargetMachine* tm = eb.selectTarget();
        //PROTEAN_RT_COUT << "Generating code for " << tm->getTargetTriple().data() << std::endl;
        // code gen options
        llvm::TargetOptions* tgtopt = new llvm::TargetOptions();
        //tgtopt->UseSoftFloat = 1; // can use this for avoiding FPU/VPU? read docs, maybe not
        //tgtopt->PrintMachineCode = 1; // this seems to print all functions... is the JIT really compiling everything?
        //tgtopt->EnableFastISel = 0;
        eb.setTargetOptions(*tgtopt);

        assert(NULL != jmm && "JITMemoryManager should be initialized");
        eb.setJITMemoryManager((llvm::JITMemoryManager*)jmm);

        execengine = eb.setErrorStr(&error).create();
        if(!execengine){
            PROTEAN_RT_COUT << "No engine created: " << error << std::endl;
        }
        assert(execengine);

        // this may have something to do with instruction scheduling? don't think so... it seems to be for pass scheduling
        // also see this: http://lists.cs.uiuc.edu/pipermail/llvmdev/2013-September/065632.html
        //llvm::MachineSchedRegistry::ScheduleDAGCtor sdctor = llvm::MachineSchedRegistry::getDefault();

        // equip the engine to call back into the native function code by telling it about protean code's magic symbols
        for (uint32_t i = 0; i < funcs.size(); i++){
            std::string s(PROTEAN_MAGIC_PREF);
            s.append(funcs[i]->getName());
            llvm::GlobalValue* gv = module->getGlobalVariable(s);
            if (NULL == gv){
                // FIXME: can assert false here?
                PROTEAN_RT_COUT << "warning: cannot find protean global variable in module: " << s << std::endl;
                gv->dump();
                continue;
            }
            assert(gv);

            execengine->addGlobalMapping(gv, (void*)funcs[i]->getLocation());

            llvm::Function* f = execengine->FindFunctionNamed(funcs[i]->getName().c_str());
            funcs[i]->setLLVMFunction(f);
        }


        optimizer->runOnce(execengine);

        uniqueFunctions = funcs.size();

        PROTEAN_RT_COUT << "JIT_init: finished" << std::endl;
    }

    OptimizationManager(){
        selfelf = new SelfElf();
        dlhandle = dlopen(NULL, RTLD_LAZY);

        std::vector<Symbol*> symlist;
        selfelf->getMagicSymbols(symlist);

        PROTEAN_RT_COUT << "Found " << std::dec << symlist.size() << " magic function symbols in symbol tables" << std::endl;
        for (std::vector<Symbol*>::const_iterator it = symlist.begin(); it != symlist.end(); it++){
            Symbol* sym = *it;
            FunctionVar* fv = new FunctionVar(sym, funcs.size());
            fmap[fv->getOrigAddress()] = fv;
            funcs.push_back(fv);
            fv->print();
        }

        // here we simply divide the "known" address space into functions by looking at funciton start addresses.
        // this can clearly be better but it might be sufficient for now.
        // e.g., could do a complex search with dladdr to get knowledge of all dynsyms.
        FunctionVar* prev = NULL;
        FunctionVar* fv = NULL;
        DEBUG(PROTEAN_RT_COUT << "FUNCTION MAP" << std::endl);
        for (std::map<uint64_t, FunctionVar*>::const_iterator it = fmap.begin(); it != fmap.end(); it++){
            uint64_t faddr = it->first;
            fv = it->second;
            if (prev != NULL){
                prev->setOrigSize(fv->getOrigAddress() - prev->getOrigAddress());
                DEBUG(prev->print());
            }
            prev = fv;
        }
        fv->setOrigSize(0x2000); // hideous hack
        DEBUG(fv->print());
    }

    ~OptimizationManager(){
        for (std::vector<FunctionVar*>::const_iterator it = funcs.begin(); it != funcs.end(); it++){
            FunctionVar* fv = (*it);
            delete fv;
        }
        if (selfelf) delete selfelf;
    }

    FunctionVar* pcLookup(uint64_t pc){
        std::map<uint64_t, FunctionVar*>::const_iterator it = fmap.upper_bound(pc);
        if (it == fmap.begin()){
            return NULL;
        }
        it--;
        FunctionVar* fv = it->second;
        if (fv->inOrigRange(pc)){
            return fv;
        }
        return NULL;
    }

    void hijackAllOriginal(std::vector<std::string>& hotFunctionList){
        for (uint32_t i = 0; i < hotFunctionList.size(); i++){
            optman->hijack(hotFunctionList[i], 0);
        }
    }

    void hijackAllLast(){
        __SHOULD_NOT_ARRIVE;
    }


    FunctionVar* hijack(std::string name, uint64_t version){
        llvm::Function* origfunc = execengine->FindFunctionNamed(name.c_str());
        PROTEAN_RT_COUT << "Preparing to JIT function " << name << " with version=" << version << std::endl;

        // version should contain information about what the optimizer does to function.
        llvm::Function* func = optimizer->run(origfunc, version);

        // here we examine all operands in the function we are about to compile
        // then compare that to a list of symbols/addresses that were found in the executable. 
        // Matches are passed to the JIT engine
        // to ensure that the code we generate touches the same data structures as the original program.
        // we should expect this scheme to be somewhat brittle and it needs to be improved.
        std::unordered_map<llvm::Value*, uint32_t> touched;
        for (llvm::Function::iterator fit = func->begin(); fit != func->end(); fit++){
            llvm::BasicBlock* bb = fit;
            for (llvm::BasicBlock::iterator bit = bb->begin(); bit != bb->end(); bit++){
                llvm::Instruction* insn = bit;
                //insn->dump();
                std::stack<llvm::Value*> ops;
                for (uint32_t i = 0; i < insn->getNumOperands(); i++){
                    llvm::Value* operand = insn->getOperand(i);
                    ops.push(operand);
                }
                while (!ops.empty()){
                    llvm::Value* operand = ops.top(); ops.pop();
                    if (touched.count(operand) > 0){
                        continue;
                    }
                    touched[operand] = 1;
                    std::string vname(operand->getName().data());
                    //PROTEAN_RT_COUT << "searching for " << vname << " with addr " << std::hex  << (uint64_t)operand << std::endl;
                    //PROTEAN_RT_COUT << "size of stack is " << std::dec << ops.size() << std::endl;

                    llvm::User* u = llvm::dyn_cast<llvm::User>(operand);
                    // FIXME: this seems to touch way too much stuff (e.g., bbs and loops). maybe because of control instructions?
                    if (u){
                        for (uint32_t i = 0; i < u->getNumOperands(); i++){
                            ops.push(u->getOperand(i));
                        }
                    }

                    Symbol* sym = selfelf->lookupSymbol(vname);
                    assert(sym == NULL || vname.compare(sym->name) == 0);
                    if (NULL == sym || 0 == sym->getValue()){
                        continue;
                    }

                    llvm::GlobalValue* gv = llvm::dyn_cast<llvm::GlobalValue>(operand);
                    if (gv){
                        DEBUG(PROTEAN_RT_COUT << "Alerting JIT about a required variable: " << vname << " at " << std::hex << sym->getValue() << std::endl);
                        execengine->updateGlobalMapping(gv, (void*)sym->getValue());
                    } else {
                        DEBUG(PROTEAN_RT_COUT << "warning: bad type for " << vname << std::endl);
                    }
                }
            }
        }
        assert(func);
    
        llvm::FunctionPassManager *p = new llvm::FunctionPassManager(module);
        //p->add(llvm::createLoopUnrollPass(2000, 16, 0));
        optimizer->registerFunctionPasses(p);

        p->doInitialization();
        p->run(*func);
        p->doFinalization();

        llvm::MachineCodeInfo mci;
        execengine->runJITOnFunction(func, &mci);
        PROTEAN_RT_COUT << "Redirecting execution to JITted function " << name <<  "@[" << std::hex << (uint64_t)mci.address() << "," << (uint64_t)((uint64_t)mci.address()+mci.size()) << ")" << std::endl;

        FunctionVar* fv = NULL;
        uint32_t idx = 0;
        for (int i = funcs.size()-1; i >= 0; i--){
            fv = funcs[i];
            if (name.compare(fv->getName()) != 0){
                fv = NULL;
            } else {
                idx = i;
                break;
            }
        }
        if (fv == NULL){
            PROTEAN_RT_COUT << "Cannot find " << name << "V" << std::dec << version << std::endl;
            __SHOULD_NOT_ARRIVE;
        }

        void* newfnptr = execengine->getPointerToFunction(func);
        setFuncPointer(idx, (uint64_t)newfnptr);

        FunctionVar* newfv = new FunctionVar(fv->getSymbol(), funcs.size(), version, func);
        newfv->setOrigSize(mci.size());
        newfv->print();
        fmap[newfv->getOrigAddress()] = newfv; // TODO: use actual address, not current?
        funcs.push_back(newfv);

        PROTEAN_RT_COUT << "Finished with " << fv->getName() << std::endl;
        return newfv;
    }

    void reset(){
        for (int i = funcs.size()-1; i >= 0; i--){
            FunctionVar* fv = funcs[i];
            if (fv->getVersion() > 0){
                funcs.erase(funcs.begin() + i);
                delete fv;
            }
            // TODO: delete from fmap?
        }

    }

    uint64_t minAddress(){
        uint64_t min = 0xdeadbeef;
        for (std::vector<FunctionVar*>::const_iterator it = funcs.begin(); it != funcs.end(); it++){
            FunctionVar* fv = *it;
            if (fv->getLocation() < min){
                min = fv->getLocation();
            }
        }
        assert(min != 0xdeadbeef && "Did not find a min address");
        return min;
    }

    uint64_t maxAddress(){
        uint64_t max = 0;
        for (std::vector<FunctionVar*>::const_iterator it = funcs.begin(); it != funcs.end(); it++){
            FunctionVar* fv = *it;
            if (fv->getLocation() > max){
                max = fv->getLocation();
            }
        }
        assert(max != 0 && "Did not find a max address");
        return max;
    }

    bool setFuncPointer(uint32_t idx, uint64_t fptr){
        funcs[idx]->setTarget(fptr);
        return true;
    }

    FunctionVar* get(uint32_t idx){
        return funcs[idx];
    }

    void print(){
        PROTEAN_RT_COUT << "OptimizationManager contents" << std::endl;
        for (std::vector<FunctionVar*>::const_iterator it = funcs.begin(); it != funcs.end(); it++){
            FunctionVar* fv = (*it);
            fv->print();
        }
    }
};

#define PTRACE_AND_CHECK(__opt, __pid, __addr, __data)                  \
    res = ptrace(__opt, __pid,__addr,__data);                           \
    if (-1 == res){                                                     \
        perror("ptrace failed");                                        \
        PROTEAN_RT_COUT << "ptrace " << #__opt << " failed with " << std::dec << errno << std::endl; \
        exit(1);                                                        \
    }

uint64_t probe_app_pc(pid_t tracee){
    struct user_regs_struct regs;
    int status, res;
    regs.rip = 0;

    assert(-1 != kill(parent_tid, SIGSTOP));
    waitpid(parent_tid, &status, WSTOPPED);
    PTRACE_AND_CHECK(PTRACE_GETREGS, tracee, NULL, &regs);
    PTRACE_AND_CHECK(PTRACE_CONT, tracee, 0, NULL);

    return (uint64_t)regs.rip;
}

int RT_loop(){
    while (1){
        PROTEAN_RT_COUT << "This runtime is not doing anything!" << std::endl;
        sleep(1);
    }
    __SHOULD_NOT_ARRIVE;
    return 0;
}

int RT_init(void* args){
    PROTEAN_RT_COUT << "Beginning protean runtime!" << std::endl;
 
   // here are the beginnings of online hot code detection
    struct user_regs_struct regs;
    int res, status;
    pid_t tracee = getppid();

    // attach to the parent
    PTRACE_AND_CHECK(PTRACE_ATTACH, tracee, NULL, NULL);
    assert(tracee == waitpid(tracee, &status, 0));

    // for some reason I can't get this working without the PTRACE_GETREGS call here
    PTRACE_AND_CHECK(PTRACE_GETREGS, tracee, NULL, &regs);
    PTRACE_AND_CHECK(PTRACE_CONT, tracee, 0, NULL);

    RT_loop();
    return 0;
}

void RT_fini(){
    PROTEAN_RT_COUT << "Cleaning up protean runtime!" << std::endl;
    std::cout.flush();
    if (optman){
        delete optman;
    }
}

extern "C" {

    void init_protean_rt(){
        child_tid = 0;
        tbegin = timer();
        PROTEAN_RT_COUT << "protean runtime starting" << std::endl;

        pgsz = getpagesize();
        assert(pgsz > 0 && "Why is page size not positive?");

        parent_tid = syscall(SYS_gettid);
        PROTEAN_RT_COUT << "Collected parent threadid for ptrace" << std::endl;

        optman = new OptimizationManager();
        PROTEAN_RT_COUT << "Created OptimizationManager object" << std::endl;

        DEBUG(optman->print());

        optman->shared_memory_init();
        mmap_anon_current_memory(align_prev_page(optman->minAddress()), align_next_page(optman->maxAddress() + sizeof(uint64_t)));
        PROTEAN_RT_COUT << "MMapped everything needed for app/LAPT_RT sharing" << std::endl;

        optman->JIT_init(); // need to move as much of this as possible to after fork()
        PROTEAN_RT_COUT << "Initialized JIT" << std::endl;

        pid_t pid = fork();
        if (0 == pid){

            // let the app get to business!
            //sched_yield();


            child_tid = getpid();

            RT_init(NULL);
            __SHOULD_NOT_ARRIVE;
        }
        usleep(1000000);

        child_tid = pid;

        assert(-1 != pid && "fork() failed");
        PROTEAN_RT_COUT << "Returning control to application" << std::endl;
    }

    void print_prof()
    {
        std::map<std::string, std::vector<int>>::iterator it;
        for(it = prof_map.begin(); it != prof_map.end(); it++)\
        {
            std::string func_name = it->first;
            std::vector<int> &vect_alias = it->second;
            ofs  << "Function Name is: " << func_name << std::endl;
            for(int i = 0; i < vect_alias.size(); ++i)
            {
                ofs << "BasicBlock Number: "  << i << " executes " << vect_alias[i] << " times\n";
            }
        }
    }

    void fini_protean_rt(){
        int status, ret;
        PROTEAN_RT_COUT << "Killing off runtime" << std::endl;
        PROTEAN_RT_COUT << "TESTING IF THIS WORKS" << std::endl;
        // kill off the cloned child
        kill(child_tid, SIGKILL); // different signal, sig handler should call RT_fini()
        ret = wait(&status);

        print_prof();

        RT_fini();
    }

    void protean_prof(/*std::vector<int> stack_vars*/ int x, int bb, char *str){
        //PROTEAN_RT_COUT << "PROTEAN PROFILING FUNCTION" << std::endl;
        //PROTEAN_RT_COUT << "Received Integer: " << x << std::endl;
        // // std::string testing(str);
        // // PROTEAN_RT_COUT << testing << std::endl;
        // PROTEAN_RT_COUT  << "Function Name is: " << str << std::endl;
        // PROTEAN_RT_COUT << "BasicBlock Number is: " << bb << std::endl;

        // ofs << "PROTEAN PROFILING FUNCTION" << std::endl;
        // ofs << "Received Integer: " << x << std::endl;
        std::string func_name(str);
        // // PROTEAN_RT_COUT << testing << std::endl;
        // ofs  << "Function Name is: " << str << std::endl;
        // ofs << "BasicBlock Number is: " << bb << std::endl;

        if(prof_map.find(func_name) == prof_map.end())
        {
            prof_map[func_name].push_back(x);
        }
        else
        {
            std::vector<int> &vect_alias = prof_map[func_name];
            if(vect_alias.size() <= bb)
            {
                vect_alias.resize(bb + 1, 0);
                vect_alias[bb] = x;
            }
            else
            {
                vect_alias[bb] += x;
            }
        }

        //PROTEAN_RT_COUT << "Vector Contains: " << std::endl;
        //for (int i = 0; i < stack_vars.size(); i++){
        //    PROTEAN_RT_COUT << "\t" << stack_vars[i] << std::endl;
        //}
    }

};

static llvm::RegisterPass<PrefetcherPass> ___PrefetcherPass("prefetcher", "inserts non-temporal prefetches at each load");