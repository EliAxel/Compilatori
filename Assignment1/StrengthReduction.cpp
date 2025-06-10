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
struct StrenghtReduction: PassInfoMixin<StrenghtReduction> {
  // Main entry point, takes IR unit to run the pass on (&F) and the
  // corresponding pass manager (to be queried if need be)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    // il booleano changes serve per capire se ci sono stati cambiamenti e in caso positivo abilita nuovamente il while
    // per controllare se ci sono altre ottimizzazioni da fare
    bool changes = false;
    // mentre anyChanges tiene conto di ogni modifica
    bool anyChanges = false;
    // scorro tutti i blocchi base della funzione
    for(auto B = F.begin(), BE = F.end(); B != BE; ++B) {
      BasicBlock &BB = *B;
      do{
        changes = false;
        //scorro tutte le istruzioni del blocco base
        for(auto I = BB.begin(), IE = BB.end(); I != IE; ++I) {
          Instruction &Instr = *I;
          // se l'istruzione è una moltiplicazione controllo se il secondo operando è una costante e se è una potenza di 2
          // se è vero allora sostituisco la moltiplicazione con uno shift a sinistra
          if(Instr.getOpcode() == Instruction::Mul) {
            auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1));
            if (Op1 && Op1->getValue().isPowerOf2()) {
              Instr.replaceAllUsesWith(BinaryOperator::Create(Instruction::Shl, Instr.getOperand(0), ConstantInt::get(Instr.getType(), Op1->getValue().logBase2()), "", &Instr));
              Instr.eraseFromParent();
              changes = true;
              anyChanges = true;
              break;
              // se non è una diretta potenza di 2 controllo se il secondo operando è una costante e
              // se è un numero che si può scrivere come somma di potenze di 2,
              // se è vero allora sostituisco la moltiplicazione con uno shift a sinistra e una somma
            } else if (auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if (Op1) {
                // utilizzo di valori in 32 bit secondo la scelta di utilizzo nel primo semestre di Compilatori
                uint32_t Val = Op1->getValue().getZExtValue();
                // funzione che calcola il logaritmo in base 2 di un numero più piccolo o uguale al numero passato come parametro
                uint32_t ClosestPowerOf2 = 1UL << Log2_32(Val);
                // funzione che calcola il logaritmo in base 2 di un numero meno grande o uguale al numero passato come parametro
                uint32_t ClosestPowerOf2s = 1UL << (Log2_32(Val)+1UL);
                uint32_t Difference = Val - ClosestPowerOf2;
                uint32_t Difference2 = Val - ClosestPowerOf2s;
                //se la differenza è di uno allora posso scrivere il numero come somma di potenze di 2
                if (Difference - 1 == 0) {
                  auto *ShiftInstr = BinaryOperator::Create(
                      Instruction::Shl, Instr.getOperand(0),
                      ConstantInt::get(Instr.getType(), Log2_32(ClosestPowerOf2)), "", &Instr);
          
                  auto *AddInstr = BinaryOperator::Create(
                      Instruction::Add, ShiftInstr,
                      Instr.getOperand(0), "", &Instr);
          
                  Instr.replaceAllUsesWith(AddInstr);
                  Instr.eraseFromParent();
                  changes = true;
                  anyChanges = true;
                  break;
                  // se la differenza non è di uno controllo se è un numero che si può scrivere come differenza di potenze di 2,
                  // se è vero allora sostituisco la moltiplicazione con uno shift a sinistra e una sottrazione
                } else if (Difference2 + 1 == 0){
                  auto *ShiftInstr = BinaryOperator::Create(
                      Instruction::Shl, Instr.getOperand(0),
                      ConstantInt::get(Instr.getType(), Log2_32(ClosestPowerOf2s)), "", &Instr);
          
                  auto *SubInstr = BinaryOperator::Create(
                      Instruction::Sub,ShiftInstr ,Instr.getOperand(0) , "", &Instr);
          
                  Instr.replaceAllUsesWith(SubInstr);
                  Instr.eraseFromParent();
                  changes = true;
                  anyChanges = true;
                  break;
                }
              }
            }
            // se non è una moltiplicazione controllo se l'istruzione è una divisione e
            // se il secondo operando è una costante e se è una potenza di 2,
            // se è vero allora sostituisco la divisione con uno shift aritmetico a destra
          } else if (Instr.getOpcode() == Instruction::SDiv){
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1 && Op1->getValue().isPowerOf2()) {
                Instr.replaceAllUsesWith(BinaryOperator::Create(Instruction::AShr, Instr.getOperand(0), ConstantInt::get(Instr.getType(), Op1->getValue().logBase2()), "", &Instr));
                Instr.eraseFromParent();
                changes = true;
                anyChanges = true;
                break;
              }
            }
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
  return {LLVM_PLUGIN_API_VERSION, "StrengthReduction", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "strength-reduction") {
                    FPM.addPass(StrenghtReduction());
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
