module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLet
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels

@[expose] public section

/-! Code-label properties of handler variable adjustment. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlProps

/-- A recognized safe raise has exactly its operand's labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "get_code_labels_dest_handle_Raise"]
theorem destHandleRaise_codeLabels (c x : Bvl.Exp) (found : destHandleRaise c = some x) :
    getCodeLabels c = getCodeLabels x := by
  cases c <;> simp_all [destHandleRaise, getCodeLabels]

private theorem adjustList_labels (d l : Nat) (xs : List Bvl.Exp)
    (each : ∀ x ∈ xs, getCodeLabels (handleAdjVars d l x) = getCodeLabels x) :
    getCodeLabelsList (handleAdjVarsList d l xs) = getCodeLabelsList xs := by
  induction xs with
  | nil => simp [handleAdjVarsList]
  | cons x xs ih =>
    simp only [handleAdjVarsList, getCodeLabelsList]
    rw [each x (by simp), ih (fun y member => each y (by simp [member]))]

private theorem adjust_labels_expr (x : Bvl.Exp) (d l : Nat) :
    getCodeLabels (handleAdjVars d l x) = getCodeLabels x := by
  cases x with
  | var n => simp [handleAdjVars, getCodeLabels]
  | force loc n => simp [handleAdjVars, getCodeLabels]
  | ifThenElse x y z =>
    simp [handleAdjVars, getCodeLabels, adjust_labels_expr x, adjust_labels_expr y, adjust_labels_expr z]
  | «let» xs body =>
    have listEq := adjustList_labels d l xs (fun x member => adjust_labels_expr x d l)
    simp [handleAdjVars, getCodeLabels, listEq, adjust_labels_expr body]
  | handle x y => simp [handleAdjVars, getCodeLabels, adjust_labels_expr x, adjust_labels_expr y]
  | raise x => simp [handleAdjVars, getCodeLabels, adjust_labels_expr x]
  | tick x => simp [handleAdjVars, getCodeLabels, adjust_labels_expr x]
  | op op xs =>
    have listEq := adjustList_labels d l xs (fun x member => adjust_labels_expr x d l)
    simp [handleAdjVars, getCodeLabels, listEq]
  | call ticks dest xs =>
    have listEq := adjustList_labels d l xs (fun x member => adjust_labels_expr x d l)
    simp [handleAdjVars, getCodeLabels, listEq]
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have h := List.sizeOf_lt_of_mem member
  all_goals omega

/-- Handler adjustment preserves expression labels and the ordered list of
label sets for an expression list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "get_code_labels_handle_adj_vars"]
theorem handleAdjVars_codeLabels :
    (∀ (x : Bvl.Exp) (d l : Nat), getCodeLabels (handleAdjVars d l x) = getCodeLabels x) ∧
    (∀ (xs : List Bvl.Exp) (d l : Nat),
      (handleAdjVarsList d l xs).map getCodeLabels = xs.map getCodeLabels) := by
  constructor
  · exact adjust_labels_expr
  · intro xs d l
    rw [handleAdjVarsList_eq_map, List.map_map]
    apply List.map_congr_left
    intro x _
    exact adjust_labels_expr x d l

/-- The environment-packing lets introduce no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "LetLet_code_labels"]
theorem letLet_codeLabels {α : Type} (n : Nat) (live : Spt α) (body : Bvl.Exp) :
    getCodeLabels (letLet n live body) = getCodeLabels body := by
  rw [letLet_source_equation]
  dsimp only
  let xs := List.range n
  let zs := xs.filter fun i => (sptLookup i live).isSome
  let ys := zs.mapIdx fun i x => (x, i)
  let long := xs.map fun i =>
    match ys.lookup i with
    | some k => Bvl.Exp.var k
    | none => .op (.intOp (.const 0)) []
  change getCodeLabels (.let (zs.map .var) (smartLet long body)) = _
  have varLabels : getCodeLabelsList (zs.map Bvl.Exp.var) = ∅ := by
    rw [getCodeLabelsList_eq]
    ext label
    simp [getCodeLabels]
  have longLabels : getCodeLabelsList long = ∅ := by
    rw [getCodeLabelsList_eq]
    ext label
    simp only [Set.mem_sUnion, Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_exists]
    intro labelSet ⟨⟨e, member, eq⟩, labels⟩
    subst labelSet
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    cases h : ys.lookup i <;>
      simp [h, getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel] at labels
  simp only [getCodeLabels, varLabels, Set.empty_union]
  by_cases empty : long.isEmpty
  · simp [smartLet, empty]
  · simp [smartLet, empty, getCodeLabels, longLabels]

end Flapjack.Compiler.Backend.BvlHandle.Proofs
