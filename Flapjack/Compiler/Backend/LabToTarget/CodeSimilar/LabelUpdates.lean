import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.SecondPass

/-! Full original accumulator equality and label-update similarity laws.
Only label annotations change; arbitrary input positions, cached bytes,
annotations, section identifiers and accumulators are retained. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_AUX"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_aux {width : Nat} [NeZero width]
    (l aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    (linesUpdLabLen pos l aux).1 = aux.reverse ++ (linesUpdLabLen pos l []).1 := by
  induction l generalizing pos aux with
  | nil => simp [linesUpdLabLen]
  | cons line tail ih =>
    cases line with
    | label sec label len =>
      simp only [linesUpdLabLen]
      rw [ih (.label sec label (if pos % 2 = 0 then 0 else 1) :: aux) _,
        ih [.label sec label (if pos % 2 = 0 then 0 else 1)] _]
      simp [List.reverse_cons,List.append_assoc]
    | asm a bytes len =>
      simp only [linesUpdLabLen]
      rw [ih (.asm a bytes len :: aux) _,ih [.asm a bytes len] _]
      simp [List.reverse_cons,List.append_assoc]
    | labAsm a w bytes len =>
      simp only [linesUpdLabLen]
      rw [ih (.labAsm a w bytes len :: aux) _,ih [.labAsm a w bytes len] _]
      simp [List.reverse_cons,List.append_assoc]

/-- Local proof factoring of exactly the fields ignored by line_similar;
there is no separate HOL declaration for this normal-form operation. -/
private def updateNormal {width : Nat} [NeZero width] : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)
  | .label s l _ => .label s l 0
  | .asm a _ _ => .asm a [] 0
  | .labAsm a _ _ _ => .labAsm a 0 [] 0

private theorem similarNormal {width : Nat} [NeZero width]
    (x y : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : lineSimilar x y ↔ updateNormal x = updateNormal y := by
  cases x <;> cases y <;> simp [lineSimilar,updateNormal]

private theorem listSimilarNormal {width : Nat} [NeZero width]
    (xs ys : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar xs ys ↔ xs.map updateNormal = ys.map updateNormal := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => rfl,fun _ => .nil⟩
    | cons => constructor <;> intro h <;> cases h
  | cons x tail ih =>
    cases ys with
    | nil => constructor <;> intro h <;> cases h
    | cons y rest =>
      constructor
      · intro h
        cases h with
        | cons hxy htail =>
          simp only [List.map_cons,List.cons.injEq]
          exact ⟨(similarNormal x y).mp hxy,(ih rest).mp htail⟩
      · intro h
        simp only [List.map_cons,List.cons.injEq] at h
        exact .cons ((similarNormal x y).mpr h.1) ((ih rest).mpr h.2)

private theorem normalUpdated {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (linesUpdLabLen pos lines acc).1.map updateNormal = (acc.reverse ++ lines).map updateNormal := by
  induction lines generalizing pos acc with
  | nil => simp [linesUpdLabLen]
  | cons line tail ih =>
    cases line <;> simp [linesUpdLabLen,ih,updateNormal,List.map_append,List.map_reverse,List.append_assoc]

/-- Original unused aux:beta binder is vacuous and omitted after fresh full
original type capture. The actual native line-list accumulator in the other
three declarations is retained without restriction. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_lines_upd_lab_len"
  (words_as_type_indexed_bitvec)]
theorem linesRel_linesUpdLabLen {width : Nat} [NeZero width]
    (l : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) (l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar (linesUpdLabLen pos l []).1 l1 ↔ LinesRel lineSimilar l l1 := by
  rw [listSimilarNormal,listSimilarNormal,normalUpdated]
  simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_upd_lab_len"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_updLabLen {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) (code1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar (updLabLen pos code) code1 ↔ codeSimilar code code1 := by
  induction code generalizing pos code1 with
  | nil => simp [updLabLen]
  | cons sec tail ih =>
    rcases sec with ⟨id,lines⟩
    cases code1 with
    | nil => simp [updLabLen,codeSimilar]
    | cons sec1 tail1 =>
      simp only [updLabLen,codeSimilar]
      rw [ih,linesRel_linesUpdLabLen]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_similar"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_similar {width : Nat} [NeZero width]
    (pos : Nat) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar (linesUpdLabLen pos lines aux).1 (aux.reverse ++ lines) := by
  apply (listSimilarNormal _ _).mpr
  exact normalUpdated lines pos aux

end Flapjack.Compiler.Backend.LabToTarget
