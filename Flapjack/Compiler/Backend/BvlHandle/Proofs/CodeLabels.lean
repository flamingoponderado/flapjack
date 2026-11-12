module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLet
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
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

private theorem optionalLetLetSing_labels (e : Bvl.Exp) (n : Nat) (live : DbVars.DbVarSet)
    (size limit : Nat) (nr : Bool) :
    getCodeLabels (optionalLetLetSing e n live size limit nr).1 = getCodeLabels e := by
  unfold optionalLetLetSing
  split <;> simp [getCodeLabels, getCodeLabelsList, letLet_codeLabels]

mutual
private theorem compileSing_labels (limit env : Nat) (e : Bvl.Exp) :
    getCodeLabels (compileSing limit env e).1 ⊆ getCodeLabels e := by
  cases e with
  | var n =>
    simp only [compileSing]
    split <;> simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
  | force loc n =>
    simp only [compileSing]
    split <;> simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
  | tick x =>
    cases h : compileSing limit env x with
    | mk y rest =>
      obtain ⟨live, size, nr⟩ := rest
      have ih := compileSing_labels limit env x
      simp only [h] at ih
      simpa [compileSing, h, getCodeLabels] using ih
  | raise x =>
    cases h : compileSing limit env x with
    | mk y rest =>
      obtain ⟨live, size, nr⟩ := rest
      have ih := compileSing_labels limit env x
      simp only [h] at ih
      simpa only [compileSing, h, optionalLetLetSing_labels, getCodeLabels] using ih
  | call ticks dest xs =>
    cases h : compileList limit env xs with
    | mk ys rest =>
      obtain ⟨live, size, nr⟩ := rest
      have ih := compileList_labels limit env xs
      simp only [h] at ih
      simp only [compileSing, h, optionalLetLetSing_labels, getCodeLabels]
      exact Set.union_subset_union (Set.Subset.rfl) ih
  | op op xs =>
    cases h : compileList limit env xs with
    | mk ys rest =>
      obtain ⟨live, size, nr⟩ := rest
      have ih := compileList_labels limit env xs
      simp only [h] at ih
      cases op <;> simp only [compileSing, h, optionalLetLetSing_labels, getCodeLabels] <;>
        try exact Set.union_subset_union (Set.Subset.rfl) ih
      rename_i thunk
      cases thunk <;> simp only [optionalLetLetSing_labels, getCodeLabels] <;>
        exact Set.union_subset_union (Set.Subset.rfl) ih
  | handle x y =>
    cases hx : compileSing limit env x with
    | mk cx rest =>
      obtain ⟨lx, sx, nx⟩ := rest
      have ix := compileSing_labels limit env x
      simp only [hx] at ix
      cases nx with
      | true =>
        simp only [compileSing, hx, getCodeLabels, ↓reduceIte]
        exact Set.Subset.trans ix Set.subset_union_left
      | false =>
        cases hy : compileSing limit (env + 1) y with
        | mk cy rest =>
          obtain ⟨ly, sy, ny⟩ := rest
          have iy := compileSing_labels limit (env + 1) y
          simp only [hy] at iy
          simp only [compileSing, hx, hy, getCodeLabels, Bool.false_eq_true, ↓reduceIte,
            letLet_codeLabels]
          exact Set.union_subset_union ix iy
  | ifThenElse x y z =>
    cases hx : compileSing limit env x with
    | mk cx rest =>
      obtain ⟨lx, sx, nx⟩ := rest
      cases hy : compileSing limit env y with
      | mk cy rest =>
        obtain ⟨ly, sy, ny⟩ := rest
        cases hz : compileSing limit env z with
        | mk cz rest =>
          obtain ⟨lz, sz, nz⟩ := rest
          have ix := compileSing_labels limit env x
          have iy := compileSing_labels limit env y
          have iz := compileSing_labels limit env z
          simp only [hx, hy, hz] at ix iy iz
          simp only [compileSing, hx, hy, hz, optionalLetLetSing_labels, getCodeLabels]
          exact Set.union_subset_union (Set.union_subset_union ix iy) iz
  | «let» xs body =>
    by_cases empty : xs.isEmpty
    · have ih := compileSing_labels limit env body
      have eq : xs = [] := List.isEmpty_iff.mp empty
      subst xs
      simpa [compileSing, getCodeLabels, getCodeLabelsList] using ih
    · cases hx : compileList limit env xs with
      | mk ys rest =>
        obtain ⟨lx, sx, nx⟩ := rest
        cases hy : compileSing limit (env + xs.length) body with
        | mk cy rest =>
          obtain ⟨ly, sy, ny⟩ := rest
          have ix := compileList_labels limit env xs
          have iy := compileSing_labels limit (env + xs.length) body
          simp only [hx, hy] at ix iy
          simp only [compileSing, empty, Bool.false_eq_true, ↓reduceIte, hx, hy, optionalLetLetSing_labels, getCodeLabels]
          exact Set.union_subset_union ix iy
termination_by sizeOf e

private theorem compileList_labels (limit env : Nat) (xs : List Bvl.Exp) :
    getCodeLabelsList (compileList limit env xs).1 ⊆ getCodeLabelsList xs := by
  cases xs with
  | nil => simp [compileList, getCodeLabelsList]
  | cons x xs =>
    cases hx : compileSing limit env x with
    | mk y rest =>
      obtain ⟨live, size, nr⟩ := rest
      cases hs : compileList limit env xs with
      | mk ys rest =>
        obtain ⟨live2, size2, nr2⟩ := rest
        have ix := compileSing_labels limit env x
        have is := compileList_labels limit env xs
        simp only [hx, hs] at ix is
        simp only [compileList, hx, hs, getCodeLabelsList]
        exact Set.union_subset_union ix is
termination_by sizeOf xs
end

/-- Handler compilation introduces no code labels in its output expressions. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_code_labels"]
theorem compile_codeLabels (limit env : Nat) (expressions : List Bvl.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ (compile limit env expressions).1})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ expressions})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact compileList_labels limit env expressions

end Flapjack.Compiler.Backend.BvlHandle.Proofs
