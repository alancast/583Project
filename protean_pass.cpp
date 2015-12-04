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

#include "../common/protean_common.hpp"

#define PROTEAN_PASS_ERROR(...) std::cerr << "error: " << __VA_ARGS__ << std::endl; __SHOULD_NOT_ARRIVE;

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

        bool runOnModule(llvm::Module& M){
            DEBUG(printGlobals(M));

            directToIndirect(M);

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
