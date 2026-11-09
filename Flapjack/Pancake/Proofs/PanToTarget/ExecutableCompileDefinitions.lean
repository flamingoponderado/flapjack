module

public import Flapjack.Pancake.PanToWord
public import Flapjack.Compiler.Backend.WordToWord.FastCompile
public import Flapjack.Compiler.Backend.RegAlloc.Executable
public import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
public import Flapjack.Compiler.Backend.WordToStack.Guard
public import Flapjack.Compiler.Backend.WordToStack.StubNames
public import Flapjack.Compiler.Backend.StackAlloc.StubNames
public import Flapjack.Compiler.Backend.StackRemove.StubNames
public import Flapjack.Compiler.Backend.LabToTarget.EncodingGuard
public import Flapjack.Compiler.Backend.WordDepth
public import Flapjack.Compiler.Backend.Backend

@[expose] public section

/-! Callable compiler definitions without the end-to-end correctness imports.
The ordinary artifact API deliberately performs no stack-depth analysis. Its relation
to the full logical compiler is proved in `ExecutableCompileProgMaxAsmWith`.
These are Flapjack interfaces, with no independently named HOL originals. -/
namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Encoders.RiscV
set_option autoImplicit false

/-- `compile_prog`'s function-name table (`pan_to_targetScript.sml:41-47`) for the
main-first declarations: sorted pan-to-word function numbers paired with
`generated_main` and the declared function names, extended by the backend stub
names.  `functionNumbers` is the pan-to-word output's function-number list, so
the pipeline does not recompute `pan_to_word` to build the table. -/
def compileProgNames {width : Nat} [NeZero width] (prog1 : List (DeclHOL width))
    (functionNumbers : List Nat) : Spt Flapjack.Basis.Pure.MlString.MlString :=
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) functionNumbers).zip
    (Flapjack.Basis.Pure.MlString.ofString "generated_main" ::
      (functionsHOL prog1).map Prod.fst))
  sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

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
`fromStack` directly, without constructing a call graph or computing depth.  The
configuration carries the real symbol table, so the CLI does not recompute it. -/
def compileProgAsmWith (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) :=
  let prog1 := program
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  let (bitmaps, _wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  Flapjack.Compiler.Backend.Backend.fromStack asmConf config
    (compileProgNames prog1 (program.map Prod.fst)) stackProgram bitmaps

/-- Ordinary compilation: bytes, bitmaps and final configuration, without computing
an unused stack bound. Failure is preserved. -/
def compileProgAsmFast {width : Nat} [NeZero width]
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  compileProgAsmWith Flapjack.RegAlloc.regAllocExecutable config asmConf program

/-- The symbol table `attach_bitmaps` records for a names table: each computed
section name looked up in the table, defaulting to `NOTFOUND`. -/
def artifactSymbols (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (config : Flapjack.Compiler.Backend.Backend.Config) :
    List (Flapjack.Basis.Pure.MlString.MlString × Nat × Nat) :=
  config.labConf.secPosLen.map fun (name, position, length) =>
    (lookupAny name names (Flapjack.Basis.Pure.MlString.ofString "NOTFOUND"), position, length)

/-- The symbol table recorded with the empty names table: every section name is
`NOTFOUND`, exactly as `compile_prog_max`'s `from_stack ... LN` records it. -/
def notFoundSymbols (config : Flapjack.Compiler.Backend.Backend.Config) :
    List (Flapjack.Basis.Pure.MlString.MlString × Nat × Nat) :=
  config.labConf.secPosLen.map fun (_, position, length) =>
    (Flapjack.Basis.Pure.MlString.ofString "NOTFOUND", position, length)

/-- `from_stack` with a names table differs from the empty table only in the
recorded symbol table; bytes, bitmaps and every other configuration field agree. -/
theorem fromStack_names_eq {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) :
    Flapjack.Compiler.Backend.Backend.fromStack asmConf config names program bitmaps =
      (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln program bitmaps).map
        fun (bytes, bms, c) => (bytes, bms, { c with symbols := artifactSymbols names c }) := by
  unfold Flapjack.Compiler.Backend.Backend.fromStack
    Flapjack.Compiler.Backend.Backend.fromLab
    Flapjack.Compiler.Backend.Backend.attachBitmaps
  dsimp only
  cases h : LabToTarget.compile asmConf config.labConf
      (StackToLab.compile config.stackConf config.dataConf
        (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
        (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset program) with
  | none => rfl
  | some result =>
      cases result with
      | mk bytes updatedLab => rfl

/-- `from_stack` with the empty names table is the named result with the symbol
table reset to `NOTFOUND`; bytes, bitmaps and every other configuration field agree. -/
theorem fromStack_ln_eq_names {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) :
    Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln program bitmaps =
      (Flapjack.Compiler.Backend.Backend.fromStack asmConf config names program bitmaps).map
        fun (bytes, bms, c) => (bytes, bms, { c with symbols := notFoundSymbols c }) := by
  unfold Flapjack.Compiler.Backend.Backend.fromStack
    Flapjack.Compiler.Backend.Backend.fromLab
    Flapjack.Compiler.Backend.Backend.attachBitmaps
  dsimp only
  cases h : LabToTarget.compile asmConf config.labConf
      (StackToLab.compile config.stackConf config.dataConf
        (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
        (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset program) with
  | none => rfl
  | some result =>
      cases result with
      | mk bytes updatedLab => rfl

/-- The symbol table the driver records: the real name table applied to the
configuration's section positions. -/
def compileProgSymbols {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) (config : Flapjack.Compiler.Backend.Backend.Config) :
    List (Flapjack.Basis.Pure.MlString.MlString × Nat × Nat) :=
  artifactSymbols
    (compileProgNames program ((panToWordCompileProgHOL asmConf.isa program).map Prod.fst))
    config

/-- The `compile_prog_max` mirror differs from the named artifact pipeline only
in the recorded symbol table. -/
theorem compileProgAsmWith_fst_names_eq (ra : WordToWord.RegAllocFn) {width : Nat}
    [NeZero width] (config : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) (program : List (DeclHOL width)) :
    (compileProgMaxAsmWith ra config asmConf program).1 =
      (compileProgAsmWith ra config asmConf program).map fun (bytes, bms, c) =>
        (bytes, bms, { c with symbols := notFoundSymbols c }) := by
  unfold compileProgAsmWith compileProgMaxAsmWith
  dsimp only
  exact fromStack_ln_eq_names asmConf config _ _ _

/-- The named artifact pipeline differs from the `compile_prog_max` mirror only
in the recorded symbol table. -/
theorem compileProgAsmWith_names_eq_fst (ra : WordToWord.RegAllocFn) {width : Nat}
    [NeZero width] (config : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) (program : List (DeclHOL width)) :
    compileProgAsmWith ra config asmConf program =
      (compileProgMaxAsmWith ra config asmConf program).1.map fun (bytes, bms, c) =>
        (bytes, bms, { c with symbols := compileProgSymbols asmConf program c }) := by
  unfold compileProgAsmWith compileProgMaxAsmWith
  dsimp only
  exact fromStack_names_eq asmConf config _ _ _

/-- Located sibling of `compileProgAsmWith`: the reviewed result on success, a
structured lab-to-target failure otherwise. -/
def compileProgAsmWithReason (ra : WordToWord.RegAllocFn) {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except Flapjack.Compiler.Backend.LabToTarget.LabLoweringFailure
      (List (BitVec 8) × List (BitVec width) ×
        Flapjack.Compiler.Backend.Backend.Config) :=
  let prog1 := program
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  let (bitmaps, _wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  Flapjack.Compiler.Backend.Backend.fromStackWithReason asmConf config
    (compileProgNames prog1 (program.map Prod.fst)) stackProgram bitmaps

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
    asmConf config _ _ _

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
  | labEncoding (failure : LabToTarget.EncodingGuardFailure)
  | labToTarget (failure : LabToTarget.LabLoweringFailure)
  deriving DecidableEq, Repr

/-- Human-readable description of a checked native backend failure. -/
def nativeBackendFailureDescription : NativeBackendFailure → String
  | .wordToStack failure => WordToStack.wordStackGuardFailureDescription failure
  | .labEncoding failure => LabToTarget.encodingGuardFailureDescription failure
  | .labToTarget failure => LabToTarget.labLoweringFailureDescription failure

/-- Located sibling of `from_stack_def` that also checks the `stack_to_lab`
output before `lab_to_target` runs: every `Asm` register must be encodable and
no `Asm` instruction may be an unsupported shape.  The guards are no-ops on
every accepted program; on success this agrees with `fromStack`. -/
def fromStackChecked {width : Nat} [NeZero width] {Bitmaps : Type}
    (unsupported : HolAsm width → Option UnsupportedReason)
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) :
    Except NativeBackendFailure
      (List (BitVec 8) × Bitmaps × Flapjack.Compiler.Backend.Backend.Config) :=
  let program := StackToLab.compile config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
    (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset program
  match LabToTarget.firstUnencodable asmConf unsupported program with
  | some failure => .error (.labEncoding failure)
  | none =>
      match Flapjack.Compiler.Backend.Backend.fromLabWithReason asmConf config names program
        bitmaps with
      | .error failure => .error (.labToTarget failure)
      | .ok result => .ok result

/-- The checked native backend pipeline: the reviewed Word-to-Word and
Word-to-Stack passes, the word-to-stack guard before `compileNative`, the
encoding guard before `lab_to_target`, and the located lab-to-target sibling.
The artifact configuration carries the real symbol table. -/
def compileProgAsmWithChecked {width : Nat} [NeZero width]
    (unsupported : HolAsm width → Option UnsupportedReason)
    (ra : WordToWord.RegAllocFn)
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except NativeBackendFailure
      (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let prog1 := program
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileWith ra config.wordToWordConf asmConf program
  match WordToStack.firstUncompilable wordProgram with
  | some failure => .error (.wordToStack failure)
  | none =>
      let (bitmaps, _wordConfig, _frames, stackProgram) :=
        WordToStack.Native.compileNative asmConf false wordProgram
      fromStackChecked unsupported asmConf config
        (compileProgNames prog1 (program.map Prod.fst)) stackProgram bitmaps

/-- Ordinary checked compilation, using the proved executable allocator. -/
def compileProgAsmFastChecked {width : Nat} [NeZero width]
    (unsupported : HolAsm width → Option UnsupportedReason)
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Except NativeBackendFailure
      (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  compileProgAsmWithChecked unsupported Flapjack.RegAlloc.regAllocExecutable config asmConf
    program

/-- The checked `from_stack` sibling returns exactly the reviewed tuple on
success; proved from the definitions, so the guards never change the bytes of a
program they accept. -/
theorem fromStackChecked_ok_agrees {width : Nat} [NeZero width] {Bitmaps : Type}
    (unsupported : HolAsm width → Option UnsupportedReason)
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) {r}
    (h : fromStackChecked unsupported asmConf config names program bitmaps = .ok r) :
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
theorem compileProgAsmWithChecked_ok_agrees {width : Nat} [NeZero width]
    (unsupported : HolAsm width → Option UnsupportedReason)
    (ra : WordToWord.RegAllocFn)
    (config : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) (program : List (DeclHOL width)) {r}
    (h : compileProgAsmWithChecked unsupported ra config asmConf program = .ok r) :
    compileProgAsmWith ra config asmConf program = some r := by
  unfold compileProgAsmWith
  unfold compileProgAsmWithChecked at h
  dsimp only at h ⊢
  split at h
  · simp at h
  · exact fromStackChecked_ok_agrees unsupported asmConf config _ _ _ h

/-- The ordinary checked pipeline agrees with `compileProgAsmFast` on success. -/
theorem compileProgAsmFastChecked_ok_agrees {width : Nat} [NeZero width]
    (unsupported : HolAsm width → Option UnsupportedReason)
    (config : Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) {r}
    (h : compileProgAsmFastChecked unsupported config asmConf program = .ok r) :
    compileProgAsmFast config asmConf program = some r :=
  compileProgAsmWithChecked_ok_agrees unsupported Flapjack.RegAlloc.regAllocExecutable config
    asmConf program h

end Flapjack.Pancake.Proofs.PanToTarget
