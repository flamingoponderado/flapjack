module

public import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public import Flapjack.Compiler.Backend.BvlInline.LetOp
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels

@[expose] public section

/-! Code-label preservation for BVL inlining passes. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlProps

/-- A recognized variable list contains no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "var_list_code_labels_imp"]
theorem varList_codeLabels {α : Type} (n : Nat) (xs : List Bvl.Exp) (ys : List α)
    (valid : varListHOL n xs ys = true) :
    (⋃₀ (getCodeLabels '' {e | e ∈ xs})) = ∅ := by
  rw [← getCodeLabelsList_eq]
  induction xs generalizing n ys with
  | nil => simp [getCodeLabelsList]
  | cons e es ih =>
    cases ys with
    | nil => cases e <;> simp_all [varListHOL]
    | cons y ys =>
      cases e <;> simp_all [varListHOL, getCodeLabelsList, getCodeLabels]
      exact ih (n + 1) ys valid.2

private theorem destOp_labels {α : Type} (body : Bvl.Exp) (args : List α) (op : ClosLang.Op)
    (found : destOp body args = some op) : getCodeLabels body = ClosLang.assignGetCodeLabel op := by
  cases body with
  | op operation variables =>
    simp only [destOp] at found
    split at found
    · rename_i valid
      cases found
      have empty := varList_codeLabels 0 variables args valid
      rw [← getCodeLabelsList_eq] at empty
      simp only [getCodeLabels, empty, Set.union_empty]
    · simp at found
  | _ => simp [destOp] at found

mutual
private theorem letOpOne_labels (e : Bvl.Exp) : getCodeLabels (letOpOne e) = getCodeLabels e := by
  cases e with
  | var n => simp only [letOpOne]
  | force loc n => simp only [letOpOne]
  | ifThenElse x y z =>
    simp only [letOpOne, getCodeLabels, letOpOne_labels x, letOpOne_labels y, letOpOne_labels z]
  | «let» xs body =>
    have bindings := letOpList_labels xs
    have bodyLabels := letOpOne_labels body
    simp only [letOpOne]
    cases found : destOp (letOpOne body) (letOpList xs) with
    | none => simp only [getCodeLabels, bindings, bodyLabels]
    | some op =>
      have operation := destOp_labels (letOpOne body) (letOpList xs) op found
      simp only [getCodeLabels]
      rw [← operation, bindings, bodyLabels]
      exact Set.union_comm _ _
  | raise x => simpa only [letOpOne, getCodeLabels] using letOpOne_labels x
  | tick x => simpa only [letOpOne, getCodeLabels] using letOpOne_labels x
  | handle x y => simp only [letOpOne, getCodeLabels, letOpOne_labels x, letOpOne_labels y]
  | op op xs => simp only [letOpOne, getCodeLabels, letOpList_labels xs]
  | call ticks dest xs => simp only [letOpOne, getCodeLabels, letOpList_labels xs]
termination_by sizeOf e

private theorem letOpList_labels (xs : List Bvl.Exp) :
    getCodeLabelsList (letOpList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => simp only [letOpList]
  | cons x xs => simp only [letOpList, getCodeLabelsList, letOpOne_labels x, letOpList_labels xs]
termination_by sizeOf xs
end

/-- The let-operation pass preserves the complete union of input labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_op_code_labels"]
theorem letOp_codeLabels (xs : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ letOp xs})) =
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact letOpList_labels xs

/-- The singleton let-operation pass preserves code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "let_op_sing_code_labels"]
theorem letOpSing_codeLabels (e : Bvl.Exp) : getCodeLabels (letOpSing e) = getCodeLabels e := by
  simpa [letOpSing, letOp, letOpList] using letOpOne_labels e

mutual
private theorem removeTicksSing_labels (e : Bvl.Exp) :
    getCodeLabels (removeTicksSing e) = getCodeLabels e := by
  cases e with
  | var n => simp only [removeTicksSing]
  | force loc n => simp only [removeTicksSing]
  | ifThenElse x y z =>
    simp only [removeTicksSing, getCodeLabels, removeTicksSing_labels x,
      removeTicksSing_labels y, removeTicksSing_labels z]
  | «let» xs body =>
    simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs, removeTicksSing_labels body]
  | raise x => simpa only [removeTicksSing, getCodeLabels] using removeTicksSing_labels x
  | tick x => simpa only [removeTicksSing, getCodeLabels] using removeTicksSing_labels x
  | handle x y =>
    simp only [removeTicksSing, getCodeLabels, removeTicksSing_labels x, removeTicksSing_labels y]
  | op op xs => simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs]
  | call ticks dest xs => simp only [removeTicksSing, getCodeLabels, removeTicksList_labels xs]
termination_by sizeOf e

private theorem removeTicksList_labels (xs : List Bvl.Exp) :
    getCodeLabelsList (removeTicksList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => simp only [removeTicksList]
  | cons x xs =>
    simp only [removeTicksList, getCodeLabelsList, removeTicksSing_labels x, removeTicksList_labels xs]
termination_by sizeOf xs
end

/-- Removing ticks preserves the complete union of input code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "remove_ticks_code_labels"]
theorem removeTicks_codeLabels (xs : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ removeTicks xs})) =
      (⋃₀ (getCodeLabels '' {e | e ∈ xs})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact removeTicksList_labels xs

/-- Optimizing a program entry introduces no new code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "optimise_get_code_labels"]
theorem optimise_codeLabels {α : Type} (splitSeq : Bool) (limit : Nat)
    (entry : α × Nat × Bvl.Exp) :
    getCodeLabels (optimise splitSeq limit entry).2.2 ⊆ getCodeLabels entry.2.2 := by
  obtain ⟨name, arity, body⟩ := entry
  simp only [optimise, BvlHandle.compileAny]
  split
  · simpa only [Set.union_empty, letOpSing_codeLabels, removeTicksSing_labels] using
      BvlHandle.Proofs.compileSeqs_codeLabels limit (letOpSing (removeTicksSing body)) none
  · simpa only [letOpSing_codeLabels, removeTicksSing_labels] using
      BvlHandle.Proofs.compileExp_codeLabels limit arity (letOpSing (removeTicksSing body))

end Flapjack.Compiler.Backend.BvlInline.Proofs
