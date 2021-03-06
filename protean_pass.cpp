/*
 * @file       protean_pass.cpp
 * @authors    Michael Laurenzano <mlaurenz@umich.edu>
 *
 * an LLVM pass to virtualize call edges in a module
 * built on top of LLVM3.3
 *
 */

#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Support/CallSite.h>
#include <llvm/Support/CommandLine.h>

#include "../common/protean_common.hpp"

#define PROTEAN_PASS_ERROR(...) std::cerr << "error: " << __VA_ARGS__ << std::endl; __SHOULD_NOT_ARRIVE;

extern bool ProfilingFlag;
using namespace llvm;

namespace {

    struct FunctionData {
    public:
        const llvm::ArrayRef<llvm::Value*>* args;
        llvm::GlobalVariable* gvar;
            
        FunctionData(llvm::ArrayRef<llvm::Value*>* a, llvm::GlobalVariable* g):args(a), gvar(g) {}
        ~FunctionData() {} // FIXME: this leaks
    };

    class ProteanPass : public llvm::ModulePass {
    private:
        std::map<std::string, FunctionData*> allfunc;
        std::map<std::string, uint32_t> filter;

        void initializeFilter(){
            const char* filtfile = getenv("PROTEAN_FUNCTION_FILTER");
            if (NULL == filtfile){
                PROTEAN_PASS_COUT << PROTEAN_FUNC_FILTER_ENV " not defined; virtualizing all functions" << std::endl;
                return;
            }
            PROTEAN_PASS_COUT << " function filter passed via " PROTEAN_FUNC_FILTER_ENV << std::endl;

            std::ifstream ff(filtfile);
            std::string line;
            assert(ff.is_open());
            while (getline(ff, line, '\n')){
                filter[line] = 1;
            }
        }

        bool passesFilter(const std::string& fname){
            if (0 == filter.size()){
                return true;
            }
            if (filter.count(fname) > 0){
                return true;
            }
            return false;
        }
        
    public: 
        static char ID;
        ProteanPass() : llvm::ModulePass(ID) {
            initializeFilter();
        }
        ~ProteanPass(){
            for (std::map<std::string, FunctionData*>::const_iterator it = allfunc.begin(); it != allfunc.end(); it++){
                FunctionData* fd = it->second;
                delete fd;
            }
        }

        void printGlobals(llvm::Module& M){
            for (llvm::Module::const_global_iterator it = M.global_begin(); it != M.global_end(); it++){
                const llvm::GlobalVariable* g = &(*it);
                llvm::StringRef s = g->getName();
                PROTEAN_PASS_COUT << "Global var " << s.data() << std::endl;
            }
        }

        bool runtimeInstrument(llvm::Module& M){
            llvm::Function* mainfn = M.getFunction("main");
            llvm::FunctionType* vtype = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), false);
            
            if (mainfn != NULL){
                llvm::Function* startfn = llvm::Function::Create(vtype, llvm::GlobalValue::ExternalLinkage, "init_protean_rt", &M);
                llvm::Instruction* firstins = mainfn->getEntryBlock().getFirstNonPHI();
                llvm::CallInst::Create(startfn, "", firstins);

                llvm::Function* endfn = llvm::Function::Create(vtype, llvm::GlobalValue::ExternalLinkage, "fini_protean_rt", &M);
                
                for(llvm::Function::iterator I = mainfn->begin(), E = mainfn->end(); I != E; ++I){
                    if (llvm::isa<llvm::ReturnInst>(I->getTerminator())){
                        llvm::BasicBlock* lastbb = I;
                        llvm::CallInst::Create(endfn, "", lastbb->getTerminator());
                        //llvm::CallInst::Create(proffn, Vec, "", lastbb->getTerminator());
                    }
                }

                return true;
            }

            return false;
        }

        void directToIndirect(llvm::Module& M){
            // for each Function
            for (llvm::Module::iterator it = M.getFunctionList().begin(); it !=  M.getFunctionList().end(); it++){
                llvm::Function* f = it;
                
                if (f != NULL){
                    DEBUG(PROTEAN_PASS_COUT << "iterating over code in function: " << f->getName().data() << std::endl);
                    
                    // for each BasicBlock
                    for (llvm::Function::iterator fit = f->getBasicBlockList().begin(); fit != f->getBasicBlockList().end(); fit++){ 
                        llvm::BasicBlock* bbl = fit;
                        
                        // for each Instruction
                        for (llvm::BasicBlock::iterator bit = bbl->begin(); bit != bbl->end(); bit++){
                            llvm::Instruction* insn = bit;
                            llvm::CallInst* callinsn = llvm::dyn_cast<llvm::CallInst>(insn);

                            // if this instruction is a function call
                            if (callinsn != NULL){ 
                                llvm::Function* callee = callinsn->getCalledFunction(); 

                                if (callee != NULL){

                                    const std::string& calleeName(callee->getName().data());

                                    // skip LLVM intrinsics
                                    if (0 == calleeName.compare(0, 4, "llvm")){
                                        DEBUG(PROTEAN_PASS_COUT << "skipping call to intrinsic function: " << calleeName << std::endl);
                                        continue;
                                    }

                                    // skip calls to things outside this module (things calling into PLT entries contain no basic blocks)
                                    /*
                                    if (callee->getLinkage() == llvm::GlobalValue::ExternalLinkage){
                                        DEBUG(PROTEAN_PASS_COUT << "skipping call to function outside Module: " << calleeName << " with visibility " << callee->getVisibility() << std::endl);
                                        continue;
                                    }
                                    */
                                    if (0 == callee->getBasicBlockList().size()){
                                        DEBUG(PROTEAN_PASS_COUT << "skipping call to function outside Module: " << calleeName << std::endl);
                                        continue;
                                    }

                                    if (!passesFilter(calleeName)){
                                        DEBUG(PROTEAN_PASS_COUT << "skipping call to function that doesn't pass filter: " << calleeName << std::endl);
                                        continue;
                                    }

                                    FunctionData* fd = allfunc[calleeName];

                                    // first time we've seen this callee
                                    if (NULL == fd){
                                        DEBUG(PROTEAN_PASS_COUT << "found virtualizable function call to: " << calleeName << " with " << std::dec << callee->getBasicBlockList().size() << " BasicBlocks" << std::endl);

                                        // set up variables needed to support an indirect call to callee
                                        llvm::FunctionType* FuncTy_3 = callee->getFunctionType();
                                        llvm::PointerType* PointerTy_2 = llvm::PointerType::get(FuncTy_3, 0);
                                        
                                        std::string magicName(PROTEAN_MAGIC_PREF);
                                        magicName.append(calleeName);
                                        assert(NULL == M.getNamedGlobal(magicName) && "protean magic variable already exists in binary - something is wrong and we are bailing");
                                        assert(NULL == M.getGlobalVariable(magicName, true) && "protean magic variable already exists in binary - something is wrong and we are bailing");
                                        llvm::GlobalVariable* gvar_mycall = new llvm::GlobalVariable(M, PointerTy_2, false, llvm::GlobalValue::ExternalLinkage, 0, magicName);
                                        gvar_mycall->setAlignment(8);
                                        llvm::Constant* fconst = llvm::ConstantExpr::getCast(llvm::Instruction::BitCast, callee, PointerTy_2);
                                        gvar_mycall->setInitializer(fconst);

                                        uint32_t aidx = 0;
                                        llvm::CallSite CS(callinsn);
                                        llvm::Value** af = new llvm::Value*[CS.arg_size()];
                                        for (llvm::CallSite::arg_iterator ait = CS.arg_begin(); ait != CS.arg_end(); ait++){
                                            af[aidx] = ait->get();
                                            aidx++;
                                        }
                                        assert(CS.arg_size() == aidx);
                                        llvm::ArrayRef<llvm::Value*>* cargs = new llvm::ArrayRef<llvm::Value*>(af, aidx);

                                        fd = new FunctionData(cargs, gvar_mycall);
                                        allfunc[calleeName] = fd;
                                    }

                                    DEBUG(bbl->dump());

                                    // load the address of the function pointer into a reg
                                    llvm::LoadInst* load_fptr = new llvm::LoadInst(fd->gvar, "", false, insn);

                                    DEBUG(bbl->dump());
                                    load_fptr->setAlignment(sizeof(uint64_t));

                                    // now change the call to use the function pointer
                                    callinsn->setCalledFunction(load_fptr);

                                    DEBUG(bbl->dump());
                                }
                            }
                        }
                    } 
                }
            }

            if (0 == allfunc.size()){
                PROTEAN_PASS_ERROR("No virtualization points found");
            }
        }

        void insertProfiling(llvm::Module& M){
            //Declare protean_prof function
            std::vector<Type*> profargs;//, Type::getInt32Ty(M.getContext())); 

            PointerType *point_type = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
            profargs.push_back(Type::getInt32Ty(M.getContext()));
            profargs.push_back(Type::getInt32Ty(M.getContext()));
            profargs.push_back(point_type);
            // profargs.push_back(array_type);
            // profargs.push_back(Type::getInt8PtrTy(M.getContext()));
            FunctionType *proftype = FunctionType::get(Type::getVoidTy(M.getContext()), profargs, false);
            Function* proffn = Function::Create(proftype, llvm::GlobalValue::ExternalLinkage, "protean_prof", &M);
            
            //For each function in the Module
            for (llvm::Module::iterator it = M.getFunctionList().begin(); it !=  M.getFunctionList().end(); it++){
                llvm::Function* f = it;
                if (f != NULL){
                    DEBUG(PROTEAN_PASS_COUT << "profiler iterating over code in function: " << f->getName().data() << std::endl);
                    
                    //Get BasicBlock pointer to entry and exit block
                    Function::iterator beg = f->getBasicBlockList().begin();
                    BasicBlock* entry = beg;
                    BasicBlock* endblock;
                    for (Function::iterator itf = f->begin(), ite = f->end(); itf != ite; ++itf){
                        if (isa<ReturnInst>(itf->getTerminator())){
                            endblock = itf;
                        }
                    }
                    
                    StringRef func_name = f->getName();

                    ArrayType *array_type = ArrayType::get(Type::getInt8Ty(M.getContext()), func_name.size());

                    Constant* test_str = llvm::ConstantDataArray::getString(M.getContext(), func_name, false);

                    AllocaInst *string_var = new AllocaInst(array_type, "TESTING", endblock->getTerminator());

                    StoreInst *str_str = new StoreInst(test_str, string_var, endblock->getTerminator());

                    LoadInst *ld_str = new LoadInst(string_var, "test_load", endblock->getTerminator());

                    //For each Basic Block
                    int bb_num = 0;
                    for (llvm::Function::iterator fit = f->getBasicBlockList().begin(); fit != f->getBasicBlockList().end(); fit++){
                        llvm::BasicBlock* bbl = fit;
                        
                        //Get instructions to help in insertion of profiling code
                        Instruction* insert_exe = entry->begin();
                        Instruction* insert_incr = bbl->getTerminator();
                    
                        //Create stack variable for basic block profiling in entry block
                        AllocaInst* execount = new AllocaInst(Type::getInt32Ty(bbl->getContext()), "STACKSHEEP", insert_exe);

                        AllocaInst * bb_var = new AllocaInst(Type::getInt32Ty(bbl->getContext()), "bb_var", insert_exe);

                    
                        //Store value 0 to flag after allocating
                        StoreInst *st0 = new StoreInst(ConstantInt::get(Type::getInt32Ty(M.getContext()), 0), execount);
                        st0->insertAfter(execount);

                        StoreInst *st_bb = new StoreInst(ConstantInt::get(Type::getInt32Ty(M.getContext()), bb_num), bb_var);
                        st_bb->insertAfter(bb_var);

                    
                        //Load value at end of current basic block
                        LoadInst *loadexe = new LoadInst(execount, "loadexe", insert_incr);


                    
                        //Increment value
                        BinaryOperator *incr = BinaryOperator::Create(Instruction::Add, ConstantInt::get(Type::getInt32Ty(M.getContext()), 1), loadexe, "incr");
                        incr->insertAfter(loadexe);
                    
                        //Store incremented value back to stack variable
                        StoreInst *stincr = new StoreInst(incr, execount);
                        stincr->insertAfter(incr);
                    
                        //Load value into end basic block
                        LoadInst *loadfinal = new LoadInst(execount, "loadfinal", endblock->getTerminator());
                        LoadInst *load_bb = new LoadInst(bb_var, "load_bb", endblock->getTerminator());


                        //String value
                        // Value* v = llvm::ConstantArray::get(array_type, StringRef("test"));

                        
                       

                        std::vector<llvm::Value*> vect_1;
                        vect_1.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), 0));
                        vect_1.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), 0));

                        GetElementPtrInst *ptr = GetElementPtrInst::Create(string_var, ArrayRef<Value*>(vect_1), "");

                        ptr->insertBefore(endblock->getTerminator());
                        // Value *v = StringRef("test");

                        std::vector<Value *> func_args;
                        func_args.push_back(loadfinal);
                        func_args.push_back(load_bb);
                        func_args.push_back(ptr);
                        //Insert profiling call for block
                        llvm::CallInst::Create(proffn, ArrayRef<Value*>(func_args),  "", endblock->getTerminator());
                        // llvm::CallInst::Create(proffn, loadfinal,  "", endblock->getTerminator());
                        ++bb_num;
                    }
                }
            }
        }

        bool runOnModule(llvm::Module& M){
            DEBUG(printGlobals(M));

            directToIndirect(M);
            
            if (ProfilingFlag){
                PROTEAN_PASS_COUT << "Inserting profiling code\n";
                insertProfiling(M);
            }
            
            bool hasmain = runtimeInstrument(M);
            if (!hasmain){
                PROTEAN_PASS_ERROR("main() not found");
            }

            DEBUG(printGlobals(M));
            return true;
        }

    };
}

char ProteanPass::ID = 0;
static llvm::RegisterPass<ProteanPass> ___ProteanPass("protean", "edge virtualization pass");

static void registerMyPass(const llvm::PassManagerBuilder &, llvm::PassManagerBase &PM) {
    PM.add(new ProteanPass());
}
static llvm::PassManagerBuilder::ExtensionPointTy pt = llvm::PassManagerBuilder::EP_ModuleOptimizerEarly;
static llvm::RegisterStandardPasses RegisterMyPass(pt, registerMyPass);