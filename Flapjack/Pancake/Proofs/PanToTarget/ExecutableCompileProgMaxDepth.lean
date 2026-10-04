import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import Flapjack.Compiler.Backend.WordDepth.AnalysisInput

/-! Callable whole compiler with the kernel-equivalent fused stack-depth
computation. The full bytes/bitmaps/configuration/stack-bound tuple is unchanged.
This executable realization is Flapjack infrastructure, not a new HOL port. -/
namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang

def compileProgMaxAsmDepthExecutable {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) × Backend.Config) × Option Nat :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.Executable.fullCallGraphDepthExecutable wordConfig.stackFrameSize
    BvlToBvi.initGlobalsLocation (sptFromAList wordProgram)
  (Backend.fromStack asmConf config .ln stackProgram bitmaps, maximum)

/-- Unconditional full result equality with the checked fast whole compiler. -/
theorem compileProgMaxAsmDepthExecutable_eq {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    compileProgMaxAsmDepthExecutable config asmConf program =
      compileProgMaxAsmFast config asmConf program := by
  unfold compileProgMaxAsmDepthExecutable compileProgMaxAsmFast compileProgMaxAsmWith
  simp only [WordDepth.Executable.fullCallGraphDepthExecutable_eq]

end Flapjack.Pancake.Proofs.PanToTarget
