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
bool isASafeInstruction(Value *I);
bool dominatesAllUses(Instruction *I, DominatorTree &DT, Loop *L);
bool isDeadAfterLoop(Instruction *I, Loop *L);
bool isOperLoopInvariant(Instruction &I, Loop *L, DominatorTree &DT, 
  std::set<Instruction*> &LoopInvariantInst, 
  std::set<Instruction*> &isChecked);
bool IsLoopInvariant(Instruction &I, Loop *L, DominatorTree &DT,
  std::set<Instruction*> &LoopInvariantInst, 
  std::set<Instruction*> &isChecked);

// funzione atta a controllare se un valore è considerabile loop invariant
bool isASafeInstruction(Value *I) {
  if (isa<BinaryOperator>(I)    || 
      isa<CastInst>(I)          || 
      isa<SelectInst>(I)        || 
      isa<GetElementPtrInst>(I) ||
      isa<CmpInst>(I)){
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
      // se l'uso è in un blocco che non è nel loop il controllo è superfluo
      if (!L->contains(UserInst->getParent())) {
        continue;
      }
        // se invece è interno e l'istruzione loop invariant non è dominata dall'istruzione
        // allora l'istruzione loop invariant non è spostabile
      if (!DT.dominates(I, UserInst)) {
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
// controlla un operando dell'istruzione e dice se è loop invariant o no
bool isOperLoopInvariant(Value &V, Loop *L, DominatorTree &DT,
  std::set<Instruction*> &LoopInvariantInst,
  std::set<Instruction*> &isChecked) {
  // Se è una costante o un argomento, è loop invariant
  if (isa<Constant>(&V) || isa<Argument>(&V)) {
    return true;
  }  
  // se non è un istruzione allora non è loop invariant
  if (Instruction *Inst = dyn_cast<Instruction>(&V)) {
  // Se già marcata come invariant, ritorna true
    if (LoopInvariantInst.count(Inst)) {
      return true;
    }
    // Se già controllata ma non invariant, evitiamo ricorsioni infinite
    if (isChecked.count(Inst)) {
      return false;
    }
    isChecked.insert(Inst);
    // Se non è dentro il loop, è considerata loop invariant
    if (!L->contains(Inst)) {
      return true;
    }

    // Chiedi se questa istruzione è loop invariant ricorsivamente ai suoi operandi
    if (IsLoopInvariant(*Inst, L, DT, LoopInvariantInst, isChecked)) {
      LoopInvariantInst.insert(Inst);
      return true;
    }
  }
  return false;
}
// controlla se un'istruzione è loop invariant
bool IsLoopInvariant(Instruction &I, Loop *L, DominatorTree &DT,
  std::set<Instruction*> &LoopInvariantInst,
  std::set<Instruction*> &isChecked) {
  // Se non è sicura, non può essere loop invariant
  if (!isASafeInstruction(&I)) {
    return false;
  }
  // Tutti gli operandi devono essere loop invariant
  for (unsigned i = 0; i < I.getNumOperands(); ++i) {
    if (!isOperLoopInvariant(*I.getOperand(i), L, DT, LoopInvariantInst, isChecked)) {
      return false;
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
      std::set<Instruction*> LoopInvariantInst;
      std::set<Instruction*> isChecked;
      // aggiungo ad una lista tutte le istruzioni loop invariant
      for(auto &BB : L->blocks()) {
        for(auto &I : *BB) {
          if(IsLoopInvariant(I, L, DT, LoopInvariantInst, isChecked) && dominatesAllUses(&I, DT, L)) {
            LoopInvariantInst.insert(&I);            
          }
        }
      }
      // calcolo di tutti i blocchi di uscita del loop
      std::set<BasicBlock*> ExitBlocks = {};
      for(auto &BB : L->blocks()) {
        for (auto *Succ : successors(BB)) {
          if (!L->contains(Succ)) {
            ExitBlocks.insert(Succ);
            break;
          }
        }        
      }
      // per ogni istruzione loop invariant controlla se domina tutti i blocchi di uscita
      // e se domina tutti i suoi usi
      for(auto *I : LoopInvariantInst) {
        bool dominatesAllExits = true;
        for (auto *ExitBB : ExitBlocks) {
          if (!DT.dominates(I, ExitBB)) {
            dominatesAllExits = false;
            break;
          }
        }
        // se l'istruzione domina tutti i blocchi di uscita e tutti i suoi usi oppure è morta dopo il loop
        // allora l'istruzione può essere spostata nel preheader del loop
        if ((dominatesAllExits || isDeadAfterLoop(I, L))) {
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
