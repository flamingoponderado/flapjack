import Flapjack.Pancake.PanToWord
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordDepth
import Flapjack.Compiler.Backend.Backend

/-! Callable compiler definitions without the end-to-end correctness imports.
The ordinary artifact API deliberately performs no stack-depth analysis. Its relation
to the full logical compiler is proved in `ExecutableCompileProgMaxAsmWith`.
These are Flapjack interfaces, with no independently named HOL originals. -/
namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang
set_option autoImplicit false

def compileProgMaxAsmExecutable {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileExecutable config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.maxDepth wordConfig.stackFrameSize
    (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wordProgram))
  (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps,
    maximum)

def compileProgMaxAsmWith (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.maxDepth wordConfig.stackFrameSize
    (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wordProgram))
  (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps,
    maximum)

def compileProgMaxAsmFast {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  compileProgMaxAsmWith Flapjack.RegAlloc.regAllocExecutable config asmConf program

def compileProgAsmWith (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  let (bitmaps, _wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps

/-- Ordinary compilation: bytes, bitmaps and final configuration, without computing
an unused stack bound. Failure is preserved. -/
def compileProgAsmFast {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  compileProgAsmWith Flapjack.RegAlloc.regAllocExecutable config asmConf program

end Flapjack.Pancake.Proofs.PanToTarget
