import Flapjack.Pancake.PanToWord
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToStack.Guard
import Flapjack.Compiler.Backend.LabToTarget.RegisterGuard
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

/-- Full compiler and logical maximum-stack bound using only the assembler configuration.
The bound is computed from the lowered Word program and returned frame sizes. -/
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

/-- Full compiler and logical bound with an explicitly supplied allocator. -/
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

/-- Bound-computing API with the proved executable allocator. Ordinary drivers use
`compileProgAsmFast` instead; the artifact projection agrees unconditionally. -/
def compileProgMaxAsmFast {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  compileProgMaxAsmWith Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- Allocator-parametric artifact-only compilation. The Word-to-Stack outputs feed
`fromStack` directly, without constructing a call graph or computing depth. -/
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

/-- Located sibling of `compileProgAsmWith`: the reviewed result on success, a
structured lab-to-target failure otherwise. -/
def compileProgAsmWithReason (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except Flapjack.Compiler.Backend.LabToTarget.LabLoweringFailure
      (List (BitVec 8) × List (BitVec width) ×
        Flapjack.Compiler.Backend.Backend.Config) :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  let (bitmaps, _wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  Flapjack.Compiler.Backend.Backend.fromStackWithReason asmConf config .ln stackProgram bitmaps

/-- The located sibling succeeds exactly when `compileProgAsmWith` succeeds,
with the same tuple; proved from the definition. -/
theorem compileProgAsmWithReason_toOption (ra : WordToWord.RegAllocFn)
    {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    (compileProgAsmWithReason ra config asmConf program).toOption
      = compileProgAsmWith ra config asmConf program := by
  simp only [compileProgAsmWithReason, compileProgAsmWith]
  exact Flapjack.Compiler.Backend.Backend.fromStackWithReason_toOption
    asmConf config .ln _ _

/-- Ordinary compilation with a located failure, using the proved executable
allocator. -/
def compileProgAsmFastWithReason {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except Flapjack.Compiler.Backend.LabToTarget.LabLoweringFailure
      (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  compileProgAsmWithReason Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- The located sibling agrees with `compileProgAsmFast` on success and failure. -/
theorem compileProgAsmFastWithReason_toOption {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    (compileProgAsmFastWithReason config asmConf program).toOption
      = compileProgAsmFast config asmConf program :=
  compileProgAsmWithReason_toOption Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- A driver-side failure of the checked native backend route.  The two guards
are Flapjack-only; `labToTarget` carries the reviewed-stage failure unchanged. -/
inductive NativeBackendFailure where
  | wordToStack (failure : WordToStack.WordStackGuardFailure)
  | labRegister (failure : LabToTarget.RegisterGuardFailure)
  | labToTarget (failure : LabToTarget.LabLoweringFailure)
  deriving DecidableEq, Repr

/-- Human-readable description of a checked native backend failure. -/
def nativeBackendFailureDescription : NativeBackendFailure → String
  | .wordToStack failure => WordToStack.wordStackGuardFailureDescription failure
  | .labRegister failure => LabToTarget.registerGuardFailureDescription failure
  | .labToTarget failure => LabToTarget.labLoweringFailureDescription failure

/-- Located sibling of `from_stack_def` that also checks the `stack_to_lab`
output for registers the target cannot encode, before `lab_to_target` runs.
The guard is a no-op on every accepted program; on success this agrees with
`fromStack`. -/
def fromStackChecked {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) :
    Except NativeBackendFailure
      (List (BitVec 8) × Bitmaps × Flapjack.Compiler.Backend.Backend.Config) :=
  let program := StackToLab.compile config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
    (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset program
  match LabToTarget.firstBadRegister asmConf program with
  | some failure => .error (.labRegister failure)
  | none =>
      match Flapjack.Compiler.Backend.Backend.fromLabWithReason asmConf config names program
        bitmaps with
      | .error failure => .error (.labToTarget failure)
      | .ok result => .ok result

/-- The checked native backend pipeline: the reviewed Word-to-Word and
Word-to-Stack passes, the word-to-stack guard before `compileNative`, the
`stack_to_lab` register guard before encoding, and the located lab-to-target
sibling. -/
def compileProgAsmWithChecked (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except NativeBackendFailure
      (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  match WordToStack.firstUncompilable wordProgram with
  | some failure => .error (.wordToStack failure)
  | none =>
      let (bitmaps, _wordConfig, _frames, stackProgram) :=
        WordToStack.Native.compileNative asmConf false wordProgram
      fromStackChecked asmConf config .ln stackProgram bitmaps

/-- Ordinary checked compilation, using the proved executable allocator. -/
def compileProgAsmFastChecked {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except NativeBackendFailure
      (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  compileProgAsmWithChecked Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- The checked `from_stack` sibling returns exactly the reviewed tuple on
success; proved from the definitions, so the register guard never changes the
bytes of a program it accepts. -/
theorem fromStackChecked_ok_agrees {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) {r}
    (h : fromStackChecked asmConf config names program bitmaps = .ok r) :
    Flapjack.Compiler.Backend.Backend.fromStack asmConf config names program bitmaps = some r := by
  unfold Flapjack.Compiler.Backend.Backend.fromStack
  unfold fromStackChecked at h
  dsimp only at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i result hok
      injection h with hr
      subst hr
      rw [← Flapjack.Compiler.Backend.Backend.fromLabWithReason_toOption]
      rw [hok]
      rfl

/-- The checked pipeline returns exactly the reviewed `compileProgAsmWith`
tuple on success; the two guards are no-ops on every program they accept. -/
theorem compileProgAsmWithChecked_ok_agrees (ra : WordToWord.RegAllocFn) {width : Nat}
    [NeZero width] (config : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) (program : List (DeclHOL width)) {r}
    (h : compileProgAsmWithChecked ra config asmConf program = .ok r) :
    compileProgAsmWith ra config asmConf program = some r := by
  unfold compileProgAsmWith
  unfold compileProgAsmWithChecked at h
  dsimp only at h ⊢
  split at h
  · simp at h
  · exact fromStackChecked_ok_agrees asmConf config .ln _ _ h

/-- The ordinary checked pipeline agrees with `compileProgAsmFast` on success. -/
theorem compileProgAsmFastChecked_ok_agrees {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) {r}
    (h : compileProgAsmFastChecked config asmConf program = .ok r) :
    compileProgAsmFast config asmConf program = some r :=
  compileProgAsmWithChecked_ok_agrees Flapjack.RegAlloc.regAllocExecutable config asmConf
    program h

end Flapjack.Pancake.Proofs.PanToTarget
