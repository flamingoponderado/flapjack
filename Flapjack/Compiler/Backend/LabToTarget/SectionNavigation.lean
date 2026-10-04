import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabSem.Navigation

/-! Original section-local lookup and decomposition of native label navigation.
Section label validity supplies exactly the ownership and nonzero-label facts
needed to ignore sections with a different header.

Original inferred types are `num -> α line list -> num option` and
`num -> num -> α sec list -> num option`. Here `α` is the HOL word-index
parameter of labLang's datatype, not independent instruction/name carriers:
Asm embeds `α asm_or_cbw`; LabAsm embeds `α asm_with_lab`, `α word`, and
fixed word8 bytes. ShareMem fixes memop, JumpCmp fixes cmp/reg_imm, and
CallFFI fixes mlstring. The native Lean instantiation below preserves those
carriers with one positive word width. The complete reproducible original
type transcript is scripts/hol-probes/lab_to_target_navigation_types.txt. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- Constructive decision procedure for a label constructor test; local Lean
infrastructure, not an independent HOL declaration. -/
private instance labelTestDecidable {width : Nat} [NeZero width]
    (line : LabLineHOL width) (labelId : Nat) :
    Decidable (∃ sid position, line = .label sid labelId position) := by
  cases line with
  | label sid label position =>
    exact decidable_of_iff (label = labelId) (by simp)
  | asm _ _ _ => exact isFalse (by simp)
  | labAsm _ _ _ _ => exact isFalse (by simp)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLocToPc {width : Nat} [NeZero width] (labelId : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Option Nat :=
  if labelId = 0 then some 0
  else match lines with
  | [] => none
  | line :: rest =>
    if (∃ sid position, line = .label sid labelId position) then some 0
    else if isLabelHOL line then secLocToPc labelId rest
    else (secLocToPc labelId rest).map Nat.succ

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secLocToPc_cons {width : Nat} [NeZero width] (labelId : Nat)
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (lines : List (LabLineHOL width)) :
    secLocToPc labelId (line :: lines) =
      if labelId = 0 ∨ (∃ sid position, line = .label sid labelId position)
      then some 0 else (secLocToPc labelId lines).map
        (if isLabelHOL line then id else Nat.succ) := by
  by_cases h : labelId = 0
  · simp [secLocToPc, h]
  · cases line <;> simp [secLocToPc, h, isLabelHOL]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem locToPc_sections {width : Nat} [NeZero width] (sectionId labelId : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
    locToPc sectionId labelId code =
      match code with
      | [] => none
      | ⟨sid, lines⟩ :: rest =>
        if sectionId = sid then
          match secLocToPc labelId lines with
          | none => (locToPc sectionId labelId rest).map (lenNoLab lines + ·)
          | result => result
        else (locToPc sectionId labelId rest).map (lenNoLab lines + ·) := by
  cases code with
  | nil => simp [locToPc]
  | cons sec rest =>
    rcases sec with ⟨sid, lines⟩
    intro hok
    have hlines : ∀ line ∈ lines, secLabelOk sid line := by
      simpa [secLabelsOk] using hok ⟨sid, lines⟩ (by simp)
    clear hok
    induction lines with
    | nil => by_cases hs : sectionId = sid <;> have hsrev : (sid = sectionId) ↔ (sectionId = sid) := eq_comm <;> by_cases hl : labelId = 0 <;> simp_all [locToPc, secLocToPc, lenNoLab]
    | cons line lines ih =>
      have hhead := hlines line (by simp)
      have htail : ∀ l ∈ lines, secLabelOk sid l := fun l hl => hlines l (by simp [hl])
      have ih := ih htail
      cases line with
      | label own label position =>
        simp only [secLabelOk] at hhead
        have hnonzero := hhead.2
        have howner := hhead.1
        subst own
        by_cases hs : sectionId = sid <;> have hsrev : (sid = sectionId) ↔ (sectionId = sid) := eq_comm <;> by_cases hl : labelId = 0 <;>
          simp_all [locToPc, secLocToPc, lenNoLab, isLabelHOL]
        all_goals split <;> rfl
      | asm instruction bytes length =>
        simp only [locToPc, isLabelHOL, Bool.false_eq_true, ↓reduceIte]
        by_cases hs : sectionId = sid <;> have hsrev : (sid = sectionId) ↔ (sectionId = sid) := eq_comm <;> by_cases hl : labelId = 0 <;>
          simp_all [secLocToPc, lenNoLab, isLabelHOL, Function.comp_def, Option.map_map, Nat.add_comm, Nat.add_left_comm]
        all_goals cases hr : secLocToPc labelId lines <;>
          simp [Option.map_map, Function.comp_def, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
      | labAsm instruction position bytes length =>
        simp only [locToPc, isLabelHOL, Bool.false_eq_true, ↓reduceIte]
        by_cases hs : sectionId = sid <;> have hsrev : (sid = sectionId) ↔ (sectionId = sid) := eq_comm <;> by_cases hl : labelId = 0 <;>
          simp_all [secLocToPc, lenNoLab, isLabelHOL, Function.comp_def, Option.map_map, Nat.add_comm, Nat.add_left_comm]
        all_goals cases hr : secLocToPc labelId lines <;>
          simp [Option.map_map, Function.comp_def, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

end Flapjack.Compiler.Backend.LabToTarget
