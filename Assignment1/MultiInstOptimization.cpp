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
#include "llvm/IR/Dominators.h"

using namespace llvm;

//-----------------------------------------------------------------------------
// TestPass implementation
//-----------------------------------------------------------------------------
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.
namespace {


// New PM implementation
struct MultiInstOptimization: PassInfoMixin<MultiInstOptimization> {
  // Main entry point, takes IR unit to run the pass on (&F) and the
  // corresponding pass manager (to be queried if need be)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    // il booleano changes serve per capire se ci sono stati cambiamenti e in caso positivo abilita nuovamente il while
    // per controllare se ci sono altre ottimizzazioni da fare
    bool changes = false;
    // mentre anyChanges tiene conto di ogni modifica
    bool anyChanges = false;
    //ci spostiamo all'interno di ogni blocco base della funzione
    for(auto B = F.begin(), BE = F.end(); B != BE; ++B) {
      BasicBlock &BB = *B;
      do{
        changes = false;
        //scorriamo tutte le istruzioni del blocco base
        for (auto I = BB.begin(), IE = --BB.end(); I != IE; ++I) {
          Instruction &Instr = *I;
          auto Next = std::next(I);
          // scorriamo tutte le istruzioni successive per cercare le ottimizzazioni
          while (Next != BB.end()) {
            Instruction &InstrNext = *Next;
            //se troviamo due istruzioni di somma e sottrazione o viceversa con gli stessi operandi
            //possiamo sostituire la seconda istruzione con la prima
            if (auto *BinOp1 = dyn_cast<BinaryOperator>(&Instr)) {
              if (auto *BinOp2 = dyn_cast<BinaryOperator>(&InstrNext)) {
                if ((BinOp1->getOpcode() == Instruction::Add && BinOp2->getOpcode() == Instruction::Sub) ||
                    (BinOp1->getOpcode() == Instruction::Sub && BinOp2->getOpcode() == Instruction::Add)) {
                    if (BinOp1 == BinOp2->getOperand(0) && BinOp1->getOperand(1) == BinOp2->getOperand(1)) {
                        InstrNext.replaceAllUsesWith(BinOp1->getOperand(0));
                        InstrNext.eraseFromParent();
                        changes = true;
                        anyChanges = true;
                        break;
                    }
                }
              }
            }
            ++Next;
          }
        }
      }while(changes);
    }
    if(anyChanges){
      PreservedAnalyses PA;
      PA.preserve<DominatorTreeAnalysis>();  // CFG non modificato
      PA.preserve<LoopAnalysis>();           // Loops non toccati
      return PA;
    } else return PreservedAnalyses::all();
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
  return {LLVM_PLUGIN_API_VERSION, "MultiInstOptimization", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "mio-pass") {
                    FPM.addPass(MultiInstOptimization());
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