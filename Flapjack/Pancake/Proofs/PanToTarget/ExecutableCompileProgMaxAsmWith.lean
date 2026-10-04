import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsm
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.RegAlloc.Executable

/-! Allocator-parametric assembler-only callable compiler.

`compileProgMaxAsmExecutable` with its word-to-word stage replaced by the
allocator-parametric `WordToWord.compileWith ra`. When `ra = RegAlloc.regAlloc` it is
`compileProgMaxAsmExecutable`, so every theorem stated for that function (in particular
`panToTargetCompileSemanticsRiscVAsmExecutable` and the source-level
`panToTargetCompileSemanticsRiscVSource`) applies after rewriting with
`compileProgMaxAsmWith_eq`. A driver may thus run an executable allocator proved equal to
`regAlloc`. Flapjack computation infrastructure; no HOL declaration. -/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang
set_option autoImplicit false

/-- `compileProgMaxAsmExecutable` with the graph-colouring allocator supplied as `ra`. -/
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

/-- With `ra = regAlloc` the allocator-parametric callable compiler is
`compileProgMaxAsmExecutable` (whole-function kernel equality; Flapjack infrastructure). -/
theorem compileProgMaxAsmWith_eq (ra : WordToWord.RegAllocFn)
    (same : ra = Flapjack.RegAlloc.regAlloc) {width : Nat} [NeZero width] :
    compileProgMaxAsmWith ra (width := width) = compileProgMaxAsmExecutable := by
  subst same
  rfl

/-- With `ra = regAlloc` the allocator-parametric callable compiler is `compile_prog_max` at
every machine configuration with that assembler configuration (Flapjack infrastructure). -/
theorem compileProgMaxAsmWith_eq_compileProgMax (ra : WordToWord.RegAllocFn)
    (same : ra = Flapjack.RegAlloc.regAlloc) {width : Nat} [NeZero width]
    {State Projection : Type} (config : Backend.Config)
    (machine : MachineConfig width State Projection) (program : List (DeclHOL width)) :
    compileProgMaxAsmWith ra config machine.target.config program =
      compileProgMax config machine program := by
  rw [compileProgMaxAsmWith_eq ra same, compileProgMaxAsmExecutable_eq]

/-- The executable allocator `regAllocExecutable` is `reg_alloc` as a function (from its
unconditional pointwise kernel equality; Flapjack infrastructure). -/
theorem regAllocExecutable_fun_eq :
    (Flapjack.RegAlloc.regAllocExecutable : WordToWord.RegAllocFn) = Flapjack.RegAlloc.regAlloc := by
  funext algorithm costs limit moves tree forced stackOnly
  exact Flapjack.RegAlloc.regAllocExecutable_eq algorithm costs limit moves tree forced stackOnly

/-- The callable compiler running the executable allocator in its word-to-word stage
(Flapjack computation infrastructure). -/
def compileProgMaxAsmFast {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  compileProgMaxAsmWith Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- The fast callable compiler is `compileProgMaxAsmExecutable`: the whole result, including
bytes, bitmaps, updated configuration and stack bound, with no premise (Flapjack
infrastructure). -/
theorem compileProgMaxAsmFast_eq {width : Nat} [NeZero width] :
    compileProgMaxAsmFast (width := width) = compileProgMaxAsmExecutable := by
  funext config asmConf program
  exact congrFun (congrFun (congrFun
    (compileProgMaxAsmWith_eq _ regAllocExecutable_fun_eq (width := width)) config) asmConf)
    program

/-- The fast callable compiler is `compile_prog_max` at every machine configuration with
that assembler configuration (Flapjack infrastructure). -/
theorem compileProgMaxAsmFast_eq_compileProgMax {width : Nat} [NeZero width]
    {State Projection : Type} (config : Backend.Config)
    (machine : MachineConfig width State Projection) (program : List (DeclHOL width)) :
    compileProgMaxAsmFast config machine.target.config program =
      compileProgMax config machine program := by
  rw [compileProgMaxAsmFast_eq, compileProgMaxAsmExecutable_eq]

end Flapjack.Pancake.Proofs.PanToTarget
