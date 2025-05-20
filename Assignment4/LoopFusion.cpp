#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"

using namespace llvm;
namespace {

bool isLoopAdjacent(std::pair<Loop*, Loop*> LPair, Function &F, FunctionAnalysisManager &AM) {
  Loop *L1 = LPair.first;
  Loop *L2 = LPair.second;

  BasicBlock *L1Exit = nullptr;
  BasicBlock *L2Header = L2->getHeader();

  // Determina l'uscita del primo loop
  SmallVector<BasicBlock *, 4> L1ExitBlocks;
  L1->getExitBlocks(L1ExitBlocks);

  // Caso 1: entrambi sono guarded
  if (L1->isGuarded() && L2->isGuarded()) {
    BasicBlock *L1Guard = L1->getLoopGuardBranch()->getParent();
    BasicBlock *L2Guard = L2->getLoopGuardBranch()->getParent();
    for (auto *Succ : successors(L1Guard)) {
      if (Succ == L2Guard)
        return true;
    }
  }
  // Caso 2: nessuno dei due è guarded
  else if (!L1->isGuarded() && !L2->isGuarded() && L1->isLoopSimplifyForm() && L2->isLoopSimplifyForm()) { 
    for (BasicBlock *Exit : L1ExitBlocks) {
      if (Exit == L2->getLoopPreheader())
        return true;
    }
  }

  return false;
}

bool isDomPostDom(std::pair<Loop*, Loop*> LPair, Function &F, FunctionAnalysisManager &AM) {
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);

  // Determina l'entry del secondo loop
  BasicBlock *SecondEntry = LPair.second->isGuarded()
      ? LPair.second->getLoopGuardBranch()->getParent()
      : LPair.second->getLoopPreheader();

  if (!SecondEntry)
    return false; // non possiamo analizzare senza entry

  // Prova prima con un’unica exit
  if (BasicBlock *FirstExit = LPair.first->getExitBlock()) {
    return DT.dominates(FirstExit, SecondEntry) &&
           PDT.dominates(SecondEntry, FirstExit);
  }

  // Più exit: controlla se almeno una soddisfa la condizione
  SmallVector<BasicBlock *, 4> ExitBlocks;
  LPair.first->getExitBlocks(ExitBlocks);
  for (BasicBlock *Exit : ExitBlocks) {
    if (DT.dominates(Exit, SecondEntry) &&
        PDT.dominates(SecondEntry, Exit)) {
      return true;
    }
  }

  return false;
}

std::set<std::pair<Loop*, Loop*>> getLoopCandidates(Function &F, FunctionAnalysisManager &AM) {
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  std::set<std::pair<Loop*, Loop*>> LoopCandidates;
  Loop *LastGood = nullptr;

  for (Loop *L : LI.getLoopsInPreorder()) {
    if (!L->isInnermost())
      continue;

    if (LastGood) {

      if (!isLoopAdjacent({LastGood, L}, F, AM)) {
        continue;
      }

      if (isDomPostDom({LastGood, L}, F, AM)) {
        LoopCandidates.insert(std::make_pair(LastGood, L));
        LastGood = nullptr;
        continue;
      }
    }
    LastGood = L;
  }
  return LoopCandidates;
}


struct TestPass: PassInfoMixin<TestPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    std::set<std::pair<Loop*,Loop*>> LI = getLoopCandidates(F,AM);
    
    
  	return PreservedAnalyses::all();
}
  static bool isRequired() { return true; }
};
}

llvm::PassPluginLibraryInfo getTestPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "LoFu", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "lofu") {
                    FPM.addPass(TestPass());
                    return true;
                  }
                  return false;
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getTestPassPluginInfo();
}
