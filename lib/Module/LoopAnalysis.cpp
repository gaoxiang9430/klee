#include "Passes.h"

#include "klee/Config/Version.h"

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MD5.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"


#include <cassert>
#include <cstdio>
#include <cstring>

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include <cxxabi.h>

using namespace llvm;
using namespace std;

static DISubprogram* getSubprogramScope(MDNode* Scope){

    if(!Scope)
        return nullptr;

    if(DILexicalBlock* LB = dyn_cast<DILexicalBlock>(Scope)){
        return getSubprogramScope(LB->getScope());
    }

    if(DISubprogram* SP = dyn_cast<DISubprogram>(Scope)){
        return SP;
    }
    return nullptr;
}

static StringRef getFileLastName(StringRef FileName){
    size_t idx = FileName.find_last_of("/");
    if(idx != std::string::npos)
        FileName = FileName.substr(idx + 1);
    return FileName;
}

static Function* inSameFunc(Module &M, string FixLine, vector<Instruction*>& FixLineInsts,
                            string CrashLine, vector<Instruction*>& CrashLineInsts){

    Function *FixFunc = nullptr;
    Function *CrashFunc = nullptr;

    for (auto &F: M) {
        if(F.isDeclaration())
            continue;

        for (auto &BB: F){
            for (auto &I : BB) {
                if(!I.getDebugLoc())
                    continue;

                auto Loc = I.getDebugLoc();
                if(!Loc.getScope())
                    continue;

                MDNode* Scope = Loc.getScope();

                DISubprogram* DIS = getSubprogramScope(Scope);
                if(!DIS)
                    continue;

                StringRef FileName = DIS->getFilename();
                if(FileName == "")
                    continue;
                FileName = getFileLastName(FileName);

                unsigned int Line = Loc.getLine();

                string CurrLoc = FileName.str() + ":" + std::to_string(Line);

                if(CurrLoc == FixLine) {
                    FixLineInsts.push_back(&I);

                    if(!FixFunc)
                        FixFunc = &F;
                }

                if(CurrLoc == CrashLine) {
                    CrashLineInsts.push_back(&I);

                    if(!CrashFunc)
                        CrashFunc = &F;
                }

            } // for I
        }// for BB
    } // for F

    if(FixFunc == CrashFunc && FixFunc != nullptr && CrashFunc != nullptr)
        return FixFunc;
    else
        return nullptr;
}

static void processSucc(BasicBlock* BB, DominatorTree &DT, Loop* CrashLoop,
        Instruction *Fix, Instruction *Crash, set<Instruction *> *TermInsts){

    for (auto* SBB: successors(BB)){
        if(CrashLoop->contains(SBB))
            continue;

        if (!DT.dominates(Fix, SBB))
            continue;

        if (DT.dominates(&(SBB->front()), Crash)) {

            processSucc(SBB, DT, CrashLoop, Fix, Crash, TermInsts);

        } else {
            TermInsts->insert(&(SBB->front()));
        }

    }
}

static void processLoop(Function &F, DominatorTree &DT, LoopInfo &LI, Instruction *Fix, Instruction *Crash,
                        set<Instruction *> *TermInsts) {

    // if in the same level loop
    Loop* CrashLoop = LI.getLoopFor(Crash->getParent());
    Loop* FixLoop = LI.getLoopFor(Crash->getParent());

    if (CrashLoop && CrashLoop == FixLoop) {
        BasicBlock* BB = Crash->getParent();
        TerminatorInst* T = BB->getTerminator();
        TermInsts->insert(T);
    }

    while(CrashLoop) {

        //errs() << "==========================================\n";
        //CrashLoop->dump();

        SmallVector<BasicBlock *, 4> ExitBlocks;
        CrashLoop->getExitBlocks(ExitBlocks);

        bool DomAll = true;
        for(auto* EB: ExitBlocks) {

            for (auto* SEB: successors(EB)) {
                if(CrashLoop->contains(SEB))
                    continue;

                //errs()<<">>>>  "<<SEB->front().getDebugLoc().getLine()<<"\n";
                //SEB->dump();

                if(!DT.dominates(Fix, SEB)) {
                    DomAll = false;
                    break;
                }
            }

        }

        if (DomAll)
            break;
        else
            CrashLoop = CrashLoop->getParentLoop();

    } // end while(CrashLoop)

    if (!CrashLoop)
        return;

    SmallVector<BasicBlock *, 4> ExitBlocks;
    CrashLoop->getExitBlocks(ExitBlocks);

    for(auto* EB: ExitBlocks) {
        processSucc(EB, DT, CrashLoop, Fix, Crash, TermInsts);
    }
}

static void processNonLoop(Function &F, DominatorTree &DT, LoopInfo &LI, Instruction *Fix, Instruction *Crash, set<Instruction *> *TermInsts, string CrashLine) {

    if(!DT.dominates(Fix, Crash)) {
        return;
    }

    int RetNum = 0;
    Instruction* LastRet = nullptr;
    for (auto & BB : F) {
        for (auto &I : BB) {
            if (I.getOpcode() == Instruction::Ret) {
                RetNum++;
                LastRet = &I;
            }
        }
    }
    if (RetNum == 1) {
        TermInsts->insert(LastRet);
    }

    Loop* CrashLoop = LI.getLoopFor(Crash->getParent());
    Loop* FixLoop = LI.getLoopFor(Fix->getParent());

    if (!CrashLoop && !FixLoop) {
        for (auto &I : *(Crash->getParent())) {

            if(!I.getDebugLoc())
                continue;

            auto Loc = I.getDebugLoc();
            if(!Loc.getScope())
                continue;

            MDNode* Scope = Loc.getScope();

            DISubprogram* DIS = getSubprogramScope(Scope);
            if(!DIS)
                continue;

            StringRef FileName = DIS->getFilename();
            if(FileName == "")
                continue;
            FileName = getFileLastName(FileName);

            unsigned int Line = Loc.getLine();

            string CurrLoc = FileName.str() + ":" + std::to_string(Line);
            if(CurrLoc == CrashLine) {
                TermInsts->insert(I.getNextNode());
                break;
            }
        }

        TerminatorInst* BBTerm = Crash->getParent()->getTerminator();

        if(DT.dominates(Fix, BBTerm)) { // TODO, redundant check?
            TermInsts->insert(BBTerm);
        }
    }

}


namespace klee {

char LoopPrimary::ID = 0;

bool LoopPrimary::runOnModule (Module &M) {

    FixLine = getFileLastName(FixLine);
    CrashLine = getFileLastName(CrashLine);

    errs()<<">>>>>>>>> LoopPrimary: FixLine: "<<FixLine<<"  CrashLine: "<<CrashLine<<"\n";

    vector<Instruction*> FixLineInsts;
    vector<Instruction*> CrashLineInsts;

    Function* TargetFunc = inSameFunc(M, FixLine, FixLineInsts, CrashLine, CrashLineInsts);
    if(!TargetFunc) {
        errs()<<">>>> DIFFERENT FUNCTION, SKIP\n";
        return false;
    }

    Instruction* CrashLast = CrashLineInsts.back();
    Instruction* FixFront = FixLineInsts.front();

    for (auto &F: M)
    {
        if(F.isDeclaration())
            continue;

        if(&F != TargetFunc) {
            continue;
        }

        DominatorTree DT(F);
        LoopInfo & LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();

#if 0
        errs()<<">>>>>>>> LOOP BEG\n";
        for(auto& Loop: LI){
            errs()<<"LINE: "<<Loop->getHeader()->front().getDebugLoc().getLine()<<"\n";
            Loop->dump();
            errs()<<"\n";
        }
        errs()<<">>>>>>>> LOOP END\n";
#endif

        if(!isPotentiallyReachable(FixFront, CrashLast, &DT, &LI)) {
            return false;
        }

        processLoop(F, DT, LI, FixFront, CrashLast, TermInsts);

        processNonLoop(F, DT, LI, FixFront, CrashLast, TermInsts, CrashLine);
    }

    errs()<<"\nIterate TermInsts Beg >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";
    for(auto *I : *TermInsts) {
        if(I->getDebugLoc()){
            errs()<<I->getDebugLoc().getLine()<<": \n";
        }
        I->print(errs());
        errs()<<"\n";
    }
    errs()<<"Iterate TermInsts End >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";

    return true;
}


void LoopPrimary::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
}

ModulePass *createLoopPrimary(std::string _FL, std::string _CL, std::set<llvm::Instruction*> *_TermInsts) {
    return new LoopPrimary(_FL, _CL, _TermInsts);
}

} // namespace klee
