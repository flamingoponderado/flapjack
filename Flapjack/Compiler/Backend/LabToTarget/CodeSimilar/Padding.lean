import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.Padding

/-! Original padding similarity chain, preserving arbitrary source accumulators. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private theorem normal_addNop {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines : List (NativeLine width)) :
    (addNop nop lines).map normalLine = lines.map normalLine := by
  induction lines with
  | nil => rfl
  | cons line lines ih =>
    cases line <;> simp [addNop, normalLine, ih]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_similar_add_nop" (words_as_type_indexed_bitvec)]
theorem lineSimilar_addNop {width : Nat} [NeZero width]
    (ls ls' : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (h : List (BitVec 8)) :
    LinesRel lineSimilar ls ls' → LinesRel lineSimilar ls (addNop h ls') := by
  intro rel
  apply (linesRel_normal_iff _ _).mpr
  rw [normal_addNop]
  exact (linesRel_normal_iff _ _).mp rel

private theorem normal_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines aux : List (NativeLine width)) :
    (padSection nop lines aux).map normalLine =
      (aux.reverse ++ lines).map normalLine := by
  induction lines generalizing aux with
  | nil => simp [padSection]
  | cons line lines ih =>
    cases line <;>
      simp [padSection, ih, List.map_append, List.map_reverse,
        normalLine, List.append_assoc]
    split <;> simp only [normal_addNop]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_similar_pad_section" (words_as_type_indexed_bitvec)]
theorem lineSimilar_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (l2 aux l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar l1 (aux.reverse ++ l2) →
      LinesRel lineSimilar l1 (padSection nop l2 aux) := by
  intro rel
  apply (linesRel_normal_iff _ _).mpr
  rw [normal_padSection]
  exact (linesRel_normal_iff _ _).mp rel

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "code_similar_pad_code" (words_as_type_indexed_bitvec)]
theorem codeSimilar_padCode {width : Nat} [NeZero width]
    (code1 code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (nop : List (BitVec 8)) :
    codeSimilar code1 code2 → codeSimilar code1 (padCode nop code2) := by
  induction code1 generalizing code2 with
  | nil =>
    cases code2 <;> simp [codeSimilar, padCode]
  | cons s rest ih =>
    cases code2 with
    | nil => simp [codeSimilar]
    | cons t tail =>
      cases s with
      | mk n ls =>
        cases t with
        | mk m rs =>
          intro rel
          exact ⟨ih tail rel.1, lineSimilar_padSection nop rs [] ls rel.2.1, rel.2.2⟩

end Flapjack.Compiler.Backend.LabToTarget
