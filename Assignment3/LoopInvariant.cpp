//=============================================================================
// FILE:
//    TestPass.cpp
//
// DESCRIPTION:
//    Visits all functions in a module and prints their names. Strictly speaking, 
//    this is an analysis pass (i.e. //    the functions are not modified). However, 
//    in order to keep things simple there's no 'print' method here (every analysis 
//    pass should implement it).
//
// USAGE:
//    New PM
//      opt -load-pass-plugin=<path-to>libTestPass.so -passes="test-pass" `\`
//        -disable-output <input-llvm-file>
//
//
// License: MIT
//=============================================================================
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;

//-----------------------------------------------------------------------------
// TestPass implementation
//-----------------------------------------------------------------------------
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.

namespace {
// funzione atta a controllare se un valore è spostabile nel preheader
bool isMovable(Value *I) {
  if (isa<BinaryOperator>(I) || isa<CastInst>(I) || isa<SelectInst>(I) || isa<GetElementPtrInst>(I)) {
    return true;
  }
  return false;
}
// data un'istruzione, il dominator tree e il loop, controlla se l'istruzione
// domina tutti i suoi usi
bool dominatesAllUses(Instruction *I, DominatorTree &DT, Loop *L) {
  // per ogni uso dell'istruzione
  for (User *U : I->users()) {
    // se l'uso è un'istruzione
    if (Instruction *UserInst = dyn_cast<Instruction>(U)) {
      BasicBlock *UserBB = UserInst->getParent();
      // se l'uso è in un blocco che non è nel loop il controllo è superfluo
      if (!L->contains(UserBB))
        continue;
      // se invece è interno e il blocco non è dominato dall'istruzione
      // allora l'istruzione non è spostabile
      if (!DT.dominates(I->getParent(), UserBB)) {
        return false;
      }
    }
  }
  return true;
}
// funzione che controlla se l'istruzione è dead al di fuori del loop
bool isDeadAfterLoop(Instruction *I, Loop *L) {
  for (User *U : I->users()) {
    if (Instruction *UserInst = dyn_cast<Instruction>(U)) {
      BasicBlock *UserBB = UserInst->getParent();
      if (!L->contains(UserBB)) {
        return false;
      }
    }
  }
  return true;
}

// New PM implementation
struct TestPass: PassInfoMixin<TestPass> {
  // Main entry point, takes IR unit to run the pass on (&F) and the
  // corresponding pass manager (to be queried if need be)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
    DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);

    // esce immediatamente se non ci sono loop
    if(LI.empty()) {
      errs() << "No loops in function: " << F.getName() << "\n";
      return PreservedAnalyses::all();
    }
    // per ogni loop della funzione
    for(auto &L : LI) {
      std::vector<Instruction*> LoopInvariantInst;
      // qui vengono raccolte le istruzioni che sono loop invariant
      for(auto &BB : L->blocks()) {
        for(auto &I : *BB) {
          // se l'istruzione è spostabile e non è un'istruzione di terminazione
          if (isMovable(&I)) {
            unsigned int isLoopInvariant = 0; // entrambi i contatori se alla fine del ciclo non sono uguali allora non tutti gli operandi 
            unsigned int i = 0;               // sono loop invariant, e di conseguenza l'istruzione non è loop invariant
            for (auto Iter = I.op_begin(); Iter != I.op_end(); ++Iter){
              Value *Operand = *Iter;
              if (isa<Instruction>(Operand)) {
                Instruction *OpInst = cast<Instruction>(Operand);
                if ((OpInst->getParent() && !L->contains(OpInst->getParent())) || is_contained(LoopInvariantInst,OpInst)) {
                  isLoopInvariant++;
                }
              } else if (isa<Constant>(Operand)) {
                isLoopInvariant++;
              }
              i++;
            }
            if (isLoopInvariant == i) {
              if(!is_contained(LoopInvariantInst, &I)) 
                LoopInvariantInst.push_back(&I);
            }
          }
        }
      }
      // calcolo di tutti i blocchi di uscita del loop
      std::vector<BasicBlock*> ExitBlocks = {};
      for(auto &BB : L->blocks()) {
        for (auto *Succ : successors(BB)) {
          if (!L->contains(Succ)) {
              if (!is_contained(ExitBlocks, Succ)) {
                ExitBlocks.push_back(Succ);
              }
            break;
          }
        }        
      }
      // per ogni istruzione loop invariant controlla se domina tutti i blocchi di uscita
      // e se domina tutti i suoi usi
      for(auto *I : LoopInvariantInst){
        bool dominatesAllExits = true;
        for (auto *ExitBB : ExitBlocks) {
          if (!DT.dominates(I, ExitBB)) {
            dominatesAllExits = false;
            break;
          }
        }
        // se l'istruzione domina tutti i blocchi di uscita e tutti i suoi usi oppure è morta dopo il loop
        // allora l'istruzione può essere spostata nel preheader del loop
        if ((dominatesAllExits || isDeadAfterLoop(I, L)) && dominatesAllUses(I, DT, L)) {
          BasicBlock *Preheader = L->getLoopPreheader();
          if (Preheader) {
            I->moveBefore(Preheader->getTerminator());
          }
        }
      }
    }
  	return PreservedAnalyses::all();
}


  // Without isRequired returning true, this pass will be skipped for functions
  // decorated with the optnone LLVM attribute. Note that clang -O0 decorates
  // all functions with optnone.
  static bool isRequired() { return true; }
};
} // namespace

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getTestPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "LoopInv", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "loop-inv") {
                    FPM.addPass(TestPass());
                    return true;
                  }
                  return false;
                });
          }};
}

// This is the core interface for pass plugins. It guarantees that 'opt' will
// be able to recognize TestPass when added to the pass pipeline on the
// command line, i.e. via '-passes=test-pass'
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getTestPassPluginInfo();
}
