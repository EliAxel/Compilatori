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
    bool changes = true;
    for(auto B = F.begin(), BE = F.end(); B != BE; ++B) {
      BasicBlock &BB = *B;
      while(changes){
        changes = false;
        for(auto I = BB.begin(), IE = BB.end(); I != IE; ++I) {
          Instruction &Instr = *I;
          if(Instr.getOpcode() == Instruction::Mul) {
            auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1));
            if (Op1 && Op1->getValue().isPowerOf2()) {
              Instr.replaceAllUsesWith(BinaryOperator::Create(Instruction::Shl, Instr.getOperand(0), ConstantInt::get(Instr.getType(), Op1->getValue().logBase2()), "", &Instr));
              Instr.eraseFromParent();
              changes = true;
              break;
            } else if (auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if (Op1) {
                uint32_t Val = Op1->getValue().getZExtValue();
                uint32_t ClosestPowerOf2 = 1UL << Log2_32(Val);
                uint32_t ClosestPowerOf2s = 1UL << (Log2_32(Val)+1UL);
                uint32_t Difference = Val - ClosestPowerOf2;
                uint32_t Difference2 = Val - ClosestPowerOf2s;
          
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
                  break;
                } else if (Difference2 + 1 == 0){
                  auto *ShiftInstr = BinaryOperator::Create(
                      Instruction::Shl, Instr.getOperand(0),
                      ConstantInt::get(Instr.getType(), Log2_32(ClosestPowerOf2s)), "", &Instr);
          
                  auto *SubInstr = BinaryOperator::Create(
                      Instruction::Sub,ShiftInstr ,Instr.getOperand(0) , "", &Instr);
          
                  Instr.replaceAllUsesWith(SubInstr);
                  Instr.eraseFromParent();
                  changes = true;
                  break;
                }
              }
            }
          } else if (Instr.getOpcode() == Instruction::SDiv){
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1 && Op1->getValue().isPowerOf2()) {
                Instr.replaceAllUsesWith(BinaryOperator::Create(Instruction::AShr, Instr.getOperand(0), ConstantInt::get(Instr.getType(), Op1->getValue().logBase2()), "", &Instr));
                Instr.eraseFromParent();
                changes = true;
                break;
              }
            }
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
  return {LLVM_PLUGIN_API_VERSION, "StrenghtReduction", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "strenght-reduction") {
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
