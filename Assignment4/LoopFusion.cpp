#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"

using namespace llvm;
namespace {
//TODO: da aggiungere
std::set<std::pair<Loop*, Loop*>> getLoopCandidates(Function &F, FunctionAnalysisManager &AM) {
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  std::set<std::pair<Loop*, Loop*>> LoopCandidates;
  std::vector<Loop*> Loops(LI.begin(), LI.end());
  //TODO: da aggiungere
  LoopCandidates.insert(std::make_pair(Loops[1], Loops[0]));

  return LoopCandidates;
}
BasicBlock* getEntryPoint(Loop* L){
  if(L->getLoopPreheader() == nullptr){
    return L->getHeader();
  } else {
    return L->getLoopPreheader();
  }
}
bool isLoopAdjacent(std::pair<Loop*, Loop*> LPair, Function &F, FunctionAnalysisManager &AM){
  SmallVector<BasicBlock *, 4> EB;
  bool isLoopAdj = false;
  LPair.first->getExitBlocks(EB);
  if (LPair.first->isGuarded()) {
    errs() << "guard";
    BasicBlock* Guard = LPair.first->getLoopGuardBranch()->getParent();
    for (auto *Succ : successors(Guard)) {
      for (auto *ExitBlock : EB) {
        if (Succ == ExitBlock && Succ == getEntryPoint(LPair.second)) {
          return true;
        }
      }
    }
  } else {
    for(auto &E: EB){
      if(E == getEntryPoint(LPair.second)){
        return true;
      }
    }
  }
  return false;
}
bool isDomPostDom(std::pair<Loop*, Loop*> LPair, Function &F, FunctionAnalysisManager &AM) {
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
  BasicBlock *FirstExit = LPair.first->getExitBlock();
  BasicBlock *SecondEntry = getEntryPoint(LPair.second);

  if (FirstExit && SecondEntry) {
    return DT.dominates(FirstExit, SecondEntry) && PDT.dominates(SecondEntry, FirstExit);
  }
  return false;
}
struct TestPass: PassInfoMixin<TestPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    std::set<std::pair<Loop*,Loop*>> LI = getLoopCandidates(F,AM);
    
    for (auto &LPair : LI) {
      if(isLoopAdjacent(LPair,F,AM) && isDomPostDom(LPair,F,AM)){
        //TODO: fusione
      }
    }
    
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
