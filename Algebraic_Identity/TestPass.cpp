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
struct TestPass: PassInfoMixin<TestPass> {
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
          if(Instr.getOpcode() == Instruction::Add) {
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1->isZero()) {
                Instr.replaceAllUsesWith(Instr.getOperand(0));
                Instr.eraseFromParent();
                changes = true;
                break;
              }
            }
          } else if (Instr.getOpcode() == Instruction::Mul){
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1->isOne()) {
                Instr.replaceAllUsesWith(Instr.getOperand(0));
                Instr.eraseFromParent();
                changes = true;
                break;
              }
            }
          } else if (Instr.getOpcode() == Instruction::Sub){
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1->isZero()) {
                Instr.replaceAllUsesWith(Instr.getOperand(0));
                Instr.eraseFromParent();
                changes = true;
                break;
              }
            }
          } else if (Instr.getOpcode() == Instruction::SDiv){
            if(auto *Op1 = dyn_cast<ConstantInt>(Instr.getOperand(1))) {
              if(Op1->isOne()) {
                Instr.replaceAllUsesWith(Instr.getOperand(0));
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
  return {LLVM_PLUGIN_API_VERSION, "TestPass", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "algebraic-identity") {
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
