import Flapjack.Compiler.Backend.LabToTarget.Compile

/-!
# Located `lab_to_target` failure diagnostics

The reviewed `lab_to_target$compile_lab`/`compile_def` ports (`compileLab`,
`compile` in `Compile.lean`) return `Option`, so a rejected program loses the
reason and the position where the pass gave up.  This module adds a
Flapjack-only sibling: it calls the reviewed `compile` first, so the bytes path
is unchanged by construction, and only when that returns `none` it re-runs the
same deterministic stages with the same clock — `filter_skip`, the FFI-subset
check, `remove_labels` (`removeLabelsLoop`) and `prog_to_bytes` — to report the
first failing stage together with the zero-based section and line index (or the
missing zero-offset label).

`compileWithReason_toOption` and `compileLabWithReason_toOption` below are
proved by `cases` on the reviewed definition, so the sibling succeeds exactly
when it succeeds, with exactly the same tuple.

Nothing here carries an `@[hol]` tag: the HOL-shaped `compile_lab_def`,
`remove_labels_def`, `remove_labels_loop_def` and `compile_def` stay in their
counterpart modules untouched, and this module only adds driver-side
diagnostic infrastructure.  The section/line indices are pipeline-local
positions in the lab program, not stable source locations; the CLI marks them
as such.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Misc
open Flapjack

/-- The stage of `lab_to_target` that rejected a program. -/
inductive LabLoweringStage where
  | ffiSubset
  | encodingOk
  | missingZeroLabel
  | clockExhausted
  deriving DecidableEq, Repr

/-- A located `lab_to_target` failure.  `sectionIndex` and `lineIndex` are
zero-based positions in the lab program; `label` is the missing zero-offset
label.  The counts in `ffiSubset` are the program's FFI entries and the
configured `ffi_names` list length. -/
inductive LabLoweringFailure where
  | ffiSubset (currentCount requestedCount : Nat)
  | encodingOk (sectionIndex lineIndex : Nat)
  | missingZeroLabel (label : Nat)
  | clockExhausted
  deriving DecidableEq, Repr

/-- Human-readable description of a located lab-to-target failure. -/
def labLoweringFailureDescription : LabLoweringFailure → String
  | .ffiSubset current requested =>
      "lab-to-target: the program uses " ++ toString current ++
        " FFI entries but the configured ffi_names list has " ++ toString requested
  | .encodingOk sectionIndex lineIndex =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " cannot be encoded for this target"
  | .missingZeroLabel label =>
      "lab-to-target: label " ++ toString label ++
        " has no zero-offset entry in the computed label map"
  | .clockExhausted =>
      "lab-to-target: label layout did not converge within the configured initial clock"

/-- Index of the first line rejected by `line_ok_light` in the given lines. -/
private def firstBadLineIndexAux {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (index : Nat) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Option Nat
  | [] => none
  | line :: rest =>
      if lineOkLight config line then firstBadLineIndexAux config (index + 1) rest
      else some index

/-- Position of the first section/line pair rejected by `line_ok_light`. -/
private def firstBadSectionIndexAux {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (index : Nat) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Option (Nat × Nat)
  | [] => none
  | ⟨_, lines⟩ :: rest =>
      match firstBadLineIndexAux config 0 lines with
      | some lineIndex => some (index, lineIndex)
      | none => firstBadSectionIndexAux config (index + 1) rest

/-- The first section and line that `sec_ok_light` rejects, if any. -/
def firstEncodingFailure {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Option (Nat × Nat) :=
  firstBadSectionIndexAux config 0 secList

/-- The first zero-offset label that `zero_labs_acc_exist` rejects, if any. -/
def firstMissingZeroLabel {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Option Nat :=
  (sptToAList (getZeroLabsAcc code)).findSome? fun p =>
    match sptLookup p.1 labs with
    | none => some p.1
    | some inner => if (sptLookup 0 inner).isSome then none else some p.1

/-- Classify a converged `remove_labels_loop` state whose final guard failed:
`sec_ok_light` first, then `zero_labs_acc_exist`.  The final `clockExhausted`
is a defensive fallback for a state that cannot fail the guard. -/
def classifyFailure {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (labs : Spt (Spt Nat))
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : LabLoweringFailure :=
  match firstEncodingFailure config secList with
  | some (sectionIndex, lineIndex) => .encodingOk sectionIndex lineIndex
  | none =>
      match firstMissingZeroLabel labs secList with
      | some label => .missingZeroLabel label
      | none => .clockExhausted

/-- Re-run the deterministic `remove_labels_loop` stages with the same clock to
report why it returned `none`.  Called only when the reviewed loop failed, so
the success branch of the final guard is unreachable. -/
def diagnoseRemoveLabels {width : Nat} [NeZero width] (clock : Nat)
    (config : AsmConfigExact width) (pos : Nat) (initLabs : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : LabLoweringFailure :=
  let labs := computeLabelsAlt pos secList initLabs
  let (secList, done) := encSecsAgain pos labs ffis config.encode secList
  if done then
    let secList := updLabLen pos secList
    let labs := computeLabelsAlt pos secList initLabs
    let (secList, done) := encSecsAgain pos labs ffis config.encode secList
    let secList := padCode (config.encode (.inst .skip)) secList
    if done && allEncOkLight config secList && zeroLabsAccExist labs secList then
      .clockExhausted
    else classifyFailure config labs secList
  else
    if clock = 0 then .clockExhausted
    else diagnoseRemoveLabels (clock - 1) config pos initLabs ffis secList
termination_by clock

/-- Locate the first failing `compile_lab_def` stage.  Runs only after the
reviewed definition returned `none`. -/
def diagnoseCompileLab {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : LabLoweringFailure :=
  let currentFfis := findFfiNames secList
  let (ffis, ffisOk) :=
    match c.ffiNames with
    | some ffis => (ffis, listSubset currentFfis ffis)
    | none => (currentFfis, true)
  if ffisOk then
    diagnoseRemoveLabels c.initClock asmConf c.pos c.labels ffis secList
  else .ffiSubset currentFfis.length ffis.length

/-- Located sibling of `compile_lab_def`: the reviewed result on success, a
located failure otherwise. -/
def compileLabWithReason {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Except LabLoweringFailure (List (BitVec 8) × Config) :=
  match compileLab asmConf c secList with
  | some result => .ok result
  | none => .error (diagnoseCompileLab asmConf c secList)

/-- Located sibling of `compile_def`: the reviewed result on success, a located
failure otherwise. -/
def compileWithReason {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Except LabLoweringFailure (List (BitVec 8) × Config) :=
  match compile asmConf c secList with
  | some result => .ok result
  | none => .error (diagnoseCompileLab asmConf c (filterSkip secList))

/-- The located sibling succeeds exactly when `compile_lab_def` succeeds, with
the same tuple; proved from the definition. -/
theorem compileLabWithReason_toOption {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (compileLabWithReason asmConf c secList).toOption = compileLab asmConf c secList := by
  unfold compileLabWithReason
  cases compileLab asmConf c secList <;> rfl

/-- The located sibling succeeds exactly when `compile_def` succeeds, with the
same tuple; proved from the definition. -/
theorem compileWithReason_toOption {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (compileWithReason asmConf c secList).toOption = compile asmConf c secList := by
  unfold compileWithReason
  cases compile asmConf c secList <;> rfl

end Flapjack.Compiler.Backend.LabToTarget
