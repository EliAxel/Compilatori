#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IRBuilder.h"


using namespace llvm;
namespace {

//Controlla se le condizioni delle guardie sono identiche
bool areEquivalentConds(Value *V1, Value *V2) {
  auto *IC1 = dyn_cast<ICmpInst>(V1);
  auto *IC2 = dyn_cast<ICmpInst>(V2);
  if (!IC1 || !IC2)
    return false;

  if (IC1->getPredicate() != IC2->getPredicate())
    return false;

  // Controllo se gli operandi sono uguali anche nel caso fossero commutativi (A == B e B == A)
  return (IC1->getOperand(0) == IC2->getOperand(0) &&
          IC1->getOperand(1) == IC2->getOperand(1)) ||
         (IC1->isCommutative() &&
          IC1->getOperand(0) == IC2->getOperand(1) &&
          IC1->getOperand(1) == IC2->getOperand(0));
}
//Controlla se i due loop sono adiacenti
bool isLoopAdjacent(std::pair<Loop*, Loop*> LPair) {
  Loop *L1 = LPair.first;
  Loop *L2 = LPair.second;

  BasicBlock *L1Exit = nullptr;
  BasicBlock *L2Header = L2->getHeader();

  // Determina l'uscita del primo loop
  SmallVector<BasicBlock *, 4> L1ExitBlocks;
  L1->getExitBlocks(L1ExitBlocks);

  // Caso 1: entrambi sono guarded
  if (L1->isGuarded() && L2->isGuarded()) {
    BranchInst* L1Grd = L1->getLoopGuardBranch();
    BranchInst* L2Grd = L2->getLoopGuardBranch();

    BasicBlock *L1Guard = L1Grd->getParent();
    BasicBlock *L2Guard = L2Grd->getParent();
    
    if (!L1Grd->isConditional() || !L2Grd->isConditional())
      return false;

    Value* cond1 = L1Grd->getCondition();
    Value* cond2 = L2Grd->getCondition();
    
    if (areEquivalentConds(cond1,cond2)){
      for (auto *Succ : successors(L1Guard)) {
        if (Succ == L2Guard){
          return true;
        }
      }
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

      if (!isLoopAdjacent({LastGood, L})) {
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

bool haveSameTripCount(Loop *L1, Loop *L2, Function &F, FunctionAnalysisManager &AM) {
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  const SCEV *C1 = SE.getBackedgeTakenCount(L1);
  const SCEV *C2 = SE.getBackedgeTakenCount(L2);
  
  if (isa<SCEVCouldNotCompute>(C1) || isa<SCEVCouldNotCompute>(C2))
    return false;
  
  if(L1->getCanonicalInductionVariable() && L2->getCanonicalInductionVariable())
    return C1 == C2;
  
  return false;
}

const SCEVConstant* getConstantStart(const SCEV *S) {
    if (auto *Const = dyn_cast<SCEVConstant>(S)) {
        return Const;
    } else if (auto *AddRec = dyn_cast<SCEVAddRecExpr>(S)) {
        return getConstantStart(AddRec->getStart());
    }
    return nullptr; // non è costante né addrec
}

bool isThereNegativeDistance(Instruction &I1, Instruction &I2, ScalarEvolution &SE){
  Value *PtrSt;
  Value *PtrLd;
  if (isa<StoreInst>(I1)){
    auto *Store = cast<StoreInst>(&I1);
    PtrSt = Store->getPointerOperand();
  }
  if (isa<LoadInst>(I2)){
    auto *Load = cast<LoadInst>(&I2);
    PtrLd = Load->getPointerOperand();
  }
  auto *GEPst = dyn_cast<GetElementPtrInst>(PtrSt);
  Value *IndexSt = GEPst->getOperand(GEPst->getNumOperands() - 1); 

  auto *GEPld = dyn_cast<GetElementPtrInst>(PtrLd);
  Value *IndexLd = GEPld->getOperand(GEPld->getNumOperands() - 1);

  const SCEV *S1 = SE.getSCEV(IndexSt);
  const SCEV *S2 = SE.getSCEV(IndexLd);

  // Se è una costante negativa → distanza negativa
  const SCEV *distance = SE.getMinusSCEV(S1, S2);
  // Caso 2: differenza con AddRecExpr
  if (auto *AddRec = dyn_cast<SCEVAddRecExpr>(distance)) {
    const SCEVConstant *ConstStart = getConstantStart(AddRec->getStart());
    if (ConstStart) {
      int64_t startVal = ConstStart->getValue()->getSExtValue();
      return startVal < 0;
    }
  }
  return true;
}

bool hasNegativeDistance(Loop *L1, Loop *L2, Function &F, FunctionAnalysisManager &AM) {
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  DependenceInfo &DI = AM.getResult<DependenceAnalysis>(F);
  for(auto &BB1 : L1->getBlocks()){ 
    if(BB1 == L1->getHeader() || BB1 == L1->getLoopPreheader())
      continue;

    for(auto &I1:*BB1){
      if(isa<StoreInst>(I1)){
        for(auto &BB2 : L2->getBlocks()){
          if(BB2 == L2->getHeader() || BB2 == L2->getLoopPreheader())
            continue;
          
          for(auto &I2:*BB2){
            if(isa<LoadInst>(I2)){
              auto D = DI.depends(&I1,&I2,true);
              if(D){
                return isThereNegativeDistance(I1,I2,SE);
              }
            }
          }          
        }
      }
    }
  }
  return false;
}

void fuseLoops(std::pair<Loop*, Loop*> LPair, Function &F) {
  IRBuilder<> Builder(F.getContext());
  Loop *L1 = LPair.first;
  Loop *L2 = LPair.second;

  BasicBlock *L2Preheader = L2->getLoopPreheader();
  BasicBlock *L1Header = L1->getHeader();
  BasicBlock *L2Header = L2->getHeader();
  BasicBlock *L1Latch = L1->getLoopLatch();
  BasicBlock *L2Latch = L2->getLoopLatch();
  BasicBlock *L2Exit = L2->getExitBlock();
  if(!L2Exit)
    return;

  BasicBlock *L1BodyStart = nullptr;
  for (auto *Succ : successors(L1Header)) {
    if (L1->contains(Succ)) {
      L1BodyStart = Succ;
      break;
    }
  }
  BasicBlock *L1BodyEnd = L1Latch->getSinglePredecessor();

  BasicBlock *L2BodyStart = nullptr;
  for (auto *Succ : successors(L2Header)) {
    if (L2->contains(Succ)) {
      L2BodyStart = Succ;
      break;
    }
  }
  BasicBlock *L2BodyEnd = L2Latch->getSinglePredecessor();

  if(!L1BodyStart || !L1BodyEnd || !L2BodyStart || !L2BodyEnd)
    return;
  
  Instruction *L1BrBodyExit = L1BodyEnd->getTerminator();
  Instruction *L1BrHeader = L1Header->getTerminator();
  Instruction *L2BrBodyExit = L2BodyEnd->getTerminator();
  Instruction *L2BrHeader = L2Header->getTerminator();
  
  L2->getCanonicalInductionVariable()->replaceAllUsesWith(L1->getCanonicalInductionVariable());
  //
  // FUSIONE L1 BODY CON L2 BODY
  //
  Builder.SetInsertPoint(L1BodyEnd);
  if (auto *Br = dyn_cast<BranchInst>(L1BrBodyExit)) {
    if (Br->isConditional()) {
      Builder.CreateCondBr(Br->getCondition(), L2BodyStart, Br->getSuccessor(1));
    } else {
      Builder.CreateBr(L2BodyStart);
    }
  }
  L1BrBodyExit->eraseFromParent();
  //
  // FUSIONE L2 BODY CON L1 LATCH
  //
  Builder.SetInsertPoint(L2BodyEnd);
  if (auto *Br = dyn_cast<BranchInst>(L2BrBodyExit)) {
    if (Br->isConditional()) {
      Builder.CreateCondBr(Br->getCondition(), L1Latch, Br->getSuccessor(1));
    } else {
      Builder.CreateBr(L1Latch);
    }
  }
  L2BrBodyExit->eraseFromParent();
  //
  // FUSIONE L1 HEADER CON L2 EXIT
  //
  Builder.SetInsertPoint(L1BrHeader);
  auto *Br = dyn_cast<BranchInst>(L1BrHeader);
  if (Br->isConditional()) {
    Builder.CreateCondBr(Br->getCondition(), Br->getSuccessor(0), L2Exit);
  }
  L1BrHeader->eraseFromParent();
  //
  // FUSIONE L2 HEADER CON L2 LATCH
  //
  Builder.SetInsertPoint(L2BrHeader);
  Builder.CreateBr(L2Latch);
  L2BrHeader->eraseFromParent();
  //
  // RIMOZIONE PRE-HEADER, HEADER E LATCH DI L2
  //
  L2Preheader->removeFromParent();
  L2Header->removeFromParent();
  L2Latch->removeFromParent();
}
void exits(Function &F) {
  // Inserisce un metadata di tipo 'llvm.function.flags' come commento custom
  const std::string &Comment = "Nothing_changed";
  LLVMContext &Ctx = F.getContext();
  Metadata *Vals[] = {
      MDString::get(Ctx, Comment),
      MDString::get(Ctx, Comment)
  };
  MDNode *Node = MDNode::get(Ctx, Vals);
  F.setMetadata(Comment, Node);
}

struct TestPass: PassInfoMixin<TestPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    std::set<std::pair<Loop*,Loop*>> LI = getLoopCandidates(F,AM);

    for(auto &L : LI){
      if(haveSameTripCount(L.first,L.second,F,AM) && !hasNegativeDistance(L.first,L.second,F,AM)){
        fuseLoops(L,F);
      } else exits(F);
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
