import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.LabSem.Classifier

/-! Native source navigation. PC counts non-label instructions rather than encoded
lengths. A section entry (label id zero) resolves even for an empty section;
positive label matching uses the label payload independently of the section
header. Return labels are searched strictly after the current instruction.
The structural measure only proves termination and does not bound execution. -/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Structural recursion measure; labels count here even though they consume
no executable instruction position. No separate HOL declaration. -/
private def navigationSize {width : Nat} [NeZero width] (code : LabProgHOL width) : Nat :=
  (code.map (fun sec => sec.lines.length + 1)).sum

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def asmFetchAux {width : Nat} [NeZero width] (position : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (LabLineHOL width) :=
  match code with
  | [] => none
  | ⟨_, []⟩ :: rest => asmFetchAux position rest
  | ⟨sectionId, line :: lines⟩ :: rest =>
      if isLabelHOL line then asmFetchAux position (⟨sectionId, lines⟩ :: rest)
      else if position = 0 then some line
      else asmFetchAux (position - 1) (⟨sectionId, lines⟩ :: rest)
termination_by navigationSize code
decreasing_by all_goals simp_wf; simp_all [navigationSize] <;> omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def asmFetch {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : Option (LabLineHOL width) :=
  asmFetchAux state.pc state.code

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def asmCodeLength {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Nat :=
  match code with
  | [] => 0
  | ⟨_, []⟩ :: rest => asmCodeLength rest
  | ⟨sectionId, line :: lines⟩ :: rest =>
      asmCodeLength (⟨sectionId, lines⟩ :: rest) + if isLabelHOL line then 0 else 1
termination_by navigationSize code
decreasing_by all_goals simp_wf; simp_all [navigationSize] <;> omega

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "lab_to_loc_def"
  (words_as_type_indexed_bitvec)]
def labToLoc {width : Nat} [NeZero width] (label : Lab) : WordLocW width :=
  match label with
  | .lab sectionId labelId => .loc sectionId labelId

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def locToPc {width : Nat} [NeZero width] (sectionId labelId : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Option Nat :=
  match code with
  | [] => none
  | ⟨currentSection, lines⟩ :: rest =>
      if currentSection = sectionId ∧ labelId = 0 then some 0
      else match lines with
        | [] => locToPc sectionId labelId rest
        | line :: lines =>
            let isMatchingLabel := match line with
              | .label ownSection ownLabel _ => ownSection == sectionId && ownLabel == labelId
              | _ => false
            if isMatchingLabel && labelId != 0 then some 0
            else if isLabelHOL line then locToPc sectionId labelId (⟨currentSection, lines⟩ :: rest)
            else (locToPc sectionId labelId (⟨currentSection, lines⟩ :: rest)).map (· + 1)
termination_by navigationSize code
decreasing_by all_goals simp_wf; simp_all [navigationSize] <;> omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getPcValue {width : Nat} [NeZero width] {C F : Type}
    (label : Lab) (state : Flapjack.Compiler.Backend.LabSem.State width C F) : Option Nat :=
  match label with
  | .lab sectionId labelId => locToPc sectionId labelId state.code

/-- The original result word dimension is independent of the code/state dimension.
Native evaluator calls select their state dimension through the expected result type. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def nextLabel {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (WordLocW resultWidth) :=
  match code with
  | [] => none
  | ⟨_, []⟩ :: rest => nextLabel (resultWidth := resultWidth) rest
  | ⟨sectionId, line :: lines⟩ :: rest =>
      match line with
      | .label ownSection ownLabel _ => some (.loc ownSection ownLabel)
      | _ => nextLabel (resultWidth := resultWidth) (⟨sectionId, lines⟩ :: rest)
termination_by navigationSize code
decreasing_by all_goals simp_wf; simp_all [navigationSize] <;> omega

/-- The original result word dimension is independent of the code/state dimension.
Native evaluator calls select their state dimension through the expected result type. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getLabAfter {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth] (position : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (WordLocW resultWidth) :=
  match code with
  | [] => none
  | ⟨_, []⟩ :: rest => getLabAfter (resultWidth := resultWidth) position rest
  | ⟨sectionId, line :: lines⟩ :: rest =>
      if isLabelHOL line then getLabAfter (resultWidth := resultWidth) position (⟨sectionId, lines⟩ :: rest)
      else if position = 0 then nextLabel (resultWidth := resultWidth) (⟨sectionId, lines⟩ :: rest)
      else getLabAfter (resultWidth := resultWidth) (position - 1) (⟨sectionId, lines⟩ :: rest)
termination_by navigationSize code
decreasing_by all_goals simp_wf; simp_all [navigationSize] <;> omega

/-- The original result word dimension is independent of the code/state dimension.
Native evaluator calls select their state dimension through the expected result type. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getRetLoc {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : Option (WordLocW resultWidth) :=
  getLabAfter (resultWidth := resultWidth) state.pc state.code

/-- Internal induction form of the source fetch-position bound. -/
private theorem asmFetchAuxBound {width : Nat} [NeZero width]
    (position : Nat) (code : LabProgHOL width) (line : LabLineHOL width)
    (h : asmFetchAux position code = some line) : position < asmCodeLength code := by
  fun_induction asmFetchAux position code generalizing line <;>
    simp_all [asmCodeLength] <;> omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchImp {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) (line : LabLineHOL width) :
    asmFetch state = some line → state.pc < asmCodeLength state.code :=
  asmFetchAuxBound state.pc state.code line

end Flapjack.Compiler.Backend.LabSem
