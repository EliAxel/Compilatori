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
         (IC1->isCommutative() && IC2->isCommutative() &&
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

  // Caso 1: entrambi i loop sono guarded
  if (L1->isGuarded() && L2->isGuarded()) {
    BranchInst* L1Grd = L1->getLoopGuardBranch();
    BranchInst* L2Grd = L2->getLoopGuardBranch();

    BasicBlock *L1Guard = L1Grd->getParent();
    BasicBlock *L2Guard = L2Grd->getParent();
    
    if (!L1Grd->isConditional() || !L2Grd->isConditional())
      return false;

    Value* cond1 = L1Grd->getCondition();
    Value* cond2 = L2Grd->getCondition();
    
    // Vero se le condizioni di entrambe le guardie sono uguali e se 
    // un successore della guardia è l'altra guardia
    if (areEquivalentConds(cond1,cond2)){
      for (auto *Succ : successors(L1Guard)) {
        if (Succ == L2Guard){
          return true;
        }
      }
    }
  }
  // Caso 2: nessuno dei due è guarded (i loop devono essere in formato Simplified)
  // Inoltre l'exitblock del primo deve essere il preheader del secondo
  else if (!L1->isGuarded() && !L2->isGuarded() && L1->isLoopSimplifyForm() && L2->isLoopSimplifyForm()) { 
    for (BasicBlock *Exit : L1ExitBlocks) {
      if (Exit == L2->getLoopPreheader())
        return true;
    }
  }

  return false;
}
// Controlla se fra i due loop cè dominanza e postdominanza
bool isDomPostDom(std::pair<Loop*, Loop*> LPair, Function &F, FunctionAnalysisManager &AM) {
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);

  // Determina l'entry del primo loop
  BasicBlock *FirstEntry = LPair.first->isGuarded()
      ? LPair.first->getLoopGuardBranch()->getParent()
      : LPair.first->getLoopPreheader();
  
  if (!FirstEntry)
    return false;

  // Determina l'entry del secondo loop
  BasicBlock *SecondEntry = LPair.second->isGuarded()
      ? LPair.second->getLoopGuardBranch()->getParent()
      : LPair.second->getLoopPreheader();

  if (!SecondEntry)
    return false;

  return DT.dominates(FirstEntry, SecondEntry) && PDT.dominates(SecondEntry, FirstEntry);
}
// Restituisce un insieme di paia di loops, il primo è il loop "sopra", il secondo il loop "sotto".
// I loop candidati sono quei loop che insieme soddisfano l'adiacenza e la dominanza e post dominanza.
// Il risultato finale è un insieme di coppie di loop pronti per i controlli successivi
std::set<std::pair<Loop*, Loop*>> getLoopCandidates(Function &F, FunctionAnalysisManager &AM) {
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  std::set<std::pair<Loop*, Loop*>> LoopCandidates;
  Loop *LastGood = nullptr;

  // Guardando i loop in depth first...
  for (Loop *L : LI.getLoopsInPreorder()) {
    // ...se il loop non è una foglia continua la discesa
    if (!L->isInnermost()){
      LastGood = nullptr;
      continue;
    }

    if (LastGood) { // LastGood è la foglia sibling al loop corrente
      if (!isLoopAdjacent({LastGood, L})) { // Se il loop corrente non è adiacente con quello precedente
        LastGood = L;                       // allora il loop precedente è scartato
        continue;
      }

      if (isDomPostDom({LastGood, L}, F, AM)) {             // Se il loop corrente soddisfa entrambe le condizioni
        LoopCandidates.insert(std::make_pair(LastGood, L)); // allora il paio è creato e LastGood è consumato
        LastGood = nullptr;
        continue;
      }
    }
    LastGood = L;
  }
  return LoopCandidates;
}
// Controlla che i due loops abbiano lo stesso trip count (per semplicità si controllano solo i loop canonici, ovvero
// non si controllano i casi tipo int i = 0; i < 10 con j = 4; j < 14
bool haveSameTripCount(Loop *L1, Loop *L2, Function &F, FunctionAnalysisManager &AM) {
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  const SCEV *C1 = SE.getBackedgeTakenCount(L1);
  const SCEV *C2 = SE.getBackedgeTakenCount(L2);
  
  if (isa<SCEVCouldNotCompute>(C1) || isa<SCEVCouldNotCompute>(C2))
    return false;
  
  if(L1->getCanonicalInductionVariable() && L2->getCanonicalInductionVariable())
    return C1 == C2;
  
  return false; // Se almeno uno dei due loop non è canonico, si assume in modo conservativo che non siano compatibili
}
// Cerca ricorsivamente di trovare la distanza fra due induzioni (il calcolo fra le distanze di due SCEV fra loop diversi
// necessita di una visita ricorsiva)
const SCEVConstant* getConstantStart(const SCEV *S) {
    if (auto *Const = dyn_cast<SCEVConstant>(S)) { // Caso base: è una costante e l'induzione è stata trovata
        return Const;
    } else if (auto *AddRec = dyn_cast<SCEVAddRecExpr>(S)) { // Caso ricorsivo
        return getConstantStart(AddRec->getStart());
    }
    return nullptr; // non è costante né AddRecExpr
}
// Continuo della funzione "hasNegativeDistance": Date due istruzioni, ne calcola la distanza partendo
// dalle store e load.
bool isThereNegativeDistance(StoreInst *I1, LoadInst *I2, ScalarEvolution &SE){
  Value *PtrSt;
  Value *PtrLd;

  // Ottengo i puntatori delle rispettive store e load
  auto *Store = I1;
  PtrSt = Store->getPointerOperand();
  auto *Load = I2;
  PtrLd = Load->getPointerOperand();

  // Dai loro puntatori, ne traggo il loro n-esimo operando, ovvero l'offset di salto
  auto *GEPst = dyn_cast<GetElementPtrInst>(PtrSt);
  Value *IndexSt = GEPst->getOperand(GEPst->getNumOperands() - 1); 
  auto *GEPld = dyn_cast<GetElementPtrInst>(PtrLd);
  Value *IndexLd = GEPld->getOperand(GEPld->getNumOperands() - 1);

  const SCEV *S1 = SE.getSCEV(IndexSt);
  const SCEV *S2 = SE.getSCEV(IndexLd);

  // Se è una costante negativa allora la distanza è negativa
  const SCEV *distance = SE.getMinusSCEV(S1, S2);
  // Bisogna ricercare ricorsivamente il valore costante della distanza
  if (auto *AddRec = dyn_cast<SCEVAddRecExpr>(distance)) {
    const SCEVConstant *ConstStart = getConstantStart(AddRec->getStart());
    if (ConstStart) {
      int64_t startVal = ConstStart->getValue()->getSExtValue();
      return startVal < 0;
    }
  }
  return true; // Conservativamente dice che la distanza è negativa
}
// Controlla se la distanza di tutte le istruzioni dei due loop è negativa e se in caso contrario
// ritorna true. Questa funzione deve essere usata solo se "hasSameTripCount" ha avuto esito positivo.
bool hasNegativeDistance(Loop *L1, Loop *L2, Function &F, FunctionAnalysisManager &AM) {
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  DependenceInfo &DI = AM.getResult<DependenceAnalysis>(F);

  for(auto &BB1 : L1->getBlocks()){ 
    if(BB1 == L1->getHeader() || BB1 == L1->getLoopPreheader() || BB1 == L1->getLoopLatch()) // Solo i blocchi del body
      continue;

    for(auto &I1:*BB1){
      if(isa<StoreInst>(I1)){
        for(auto &BB2 : L2->getBlocks()){
          if(BB2 == L2->getHeader() || BB2 == L2->getLoopPreheader() || BB2 == L1->getLoopLatch()) // Solo i blocchi del body
            continue;
          
          for(auto &I2:*BB2){
            if(isa<LoadInst>(I2)){
              auto *Store = cast<StoreInst>(&I1);
              auto *Load = cast<LoadInst>(&I2);
              auto D = DI.depends(&I1,&I2,true);              // Se le due store e load dipendono tra di loro (ovvero accedono alla stessa memoria)
              if(D && isThereNegativeDistance(Store,Load,SE)) // allora si può controllare se la loro distanza è negativa, in caso positivo la
                return true;                                  // Loop Fusion non si può fare.
            }
          }          
        }
      }
    }
  }
  return false;
}
// Fusione dei due loop: Questa funzione si occupa solamente di fusioni fra due cicli for non guarded
// con definizioni di variabili dead after loop.
void fuseLoops(std::pair<Loop*, Loop*> LPair, Function &F) {
  Loop *L1 = LPair.first;
  Loop *L2 = LPair.second;

  // Ottengo preventivamente tutti i blocchi utili
  BasicBlock *L2Preheader = L2->getLoopPreheader();
  BasicBlock *L1Header = L1->getHeader();
  BasicBlock *L2Header = L2->getHeader();
  BasicBlock *L1Latch = L1->getLoopLatch();
  BasicBlock *L2Latch = L2->getLoopLatch();
  BasicBlock *L2Exit = L2->getExitBlock();
  if (!L2Exit)
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

  // Ottengo tutte le entrate e uscite dal body
  if (!L1BodyStart || !L1BodyEnd || !L2BodyStart || !L2BodyEnd)
    return;

  // Ottengo i terminatori utili
  Instruction *L1BrBodyExit = L1BodyEnd->getTerminator();
  Instruction *L1BrHeader = L1Header->getTerminator();
  Instruction *L2BrBodyExit = L2BodyEnd->getTerminator();
  Instruction *L2BrHeader = L2Header->getTerminator();

  // Sostituzione variabile d’induzione
  L2->getCanonicalInductionVariable()->replaceAllUsesWith(L1->getCanonicalInductionVariable());

  // Fusione L1 body con L2 body
  if (auto *Br = dyn_cast<BranchInst>(L1BrBodyExit)) {
    L1BrBodyExit->setSuccessor(0, L2BodyStart);
  } else return;

  // Fusione L2 body con L1 latch
  if (auto *Br = dyn_cast<BranchInst>(L2BrBodyExit)) {
    L2BrBodyExit->setSuccessor(0, L1Latch);
  } else return;

  // Fusione L1 header con L2 exit
  if (auto *Br = dyn_cast<BranchInst>(L1BrHeader)) {
    Br->setSuccessor(1, L2Exit);
  } else return;

  // Fusione L2 header con L2 latch
  if (auto *Br = dyn_cast<BranchInst>(L2BrHeader)) {
    Br->setSuccessor(0, L2Latch);
  } else return;

  // Pulizia codice
  L2Preheader->eraseFromParent();
  L2Header->eraseFromParent();
  L2Latch->eraseFromParent();
}
// Generico passo di Loop Fusion NON iterativo (itera solamente una volta)
struct TestPass: PassInfoMixin<TestPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    std::set<std::pair<Loop*,Loop*>> LI = getLoopCandidates(F,AM);
    bool anyChanges = false;

    for(auto &L : LI){
      if(haveSameTripCount(L.first,L.second,F,AM) && !hasNegativeDistance(L.first,L.second,F,AM)){
        fuseLoops(L,F);
        anyChanges = true;
      } 
    }
  	if(anyChanges) return PreservedAnalyses::none();
    else return PreservedAnalyses::all();
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