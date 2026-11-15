module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLet
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.Simplify
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels
public import Flapjack.Compiler.Backend.BvlConst.Proofs.CompileLabels

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

mutual
private theorem handleSimp_labels_expr (e : Bvl.Exp) : getCodeLabels (handleSimp e) ⊆ getCodeLabels e := by
  cases e with
  | var n => simp [handleSimp]
  | force l n => simp [handleSimp]
  | raise e => simpa only [handleSimp, getCodeLabels] using handleSimp_labels_expr e
  | tick e => simpa only [handleSimp, getCodeLabels] using handleSimp_labels_expr e
  | call t d xs =>
    simp only [handleSimp, getCodeLabels]
    exact Set.union_subset_union Set.Subset.rfl (handleSimp_labels_list xs)
  | op op xs =>
    simp only [handleSimp, getCodeLabels]
    exact Set.union_subset_union Set.Subset.rfl (handleSimp_labels_list xs)
  | «let» xs e =>
    simp only [handleSimp, getCodeLabels]
    exact Set.union_subset_union (handleSimp_labels_list xs) (handleSimp_labels_expr e)
  | ifThenElse x y z =>
    simp only [handleSimp, getCodeLabels]
    exact Set.union_subset_union (Set.union_subset_union (handleSimp_labels_expr x) (handleSimp_labels_expr y)) (handleSimp_labels_expr z)
  | handle x y =>
    simp only [handleSimp, getCodeLabels]
    exact makeHandle_labels x y 0
termination_by handleSize e
decreasing_by all_goals simp_all [handleSize] <;> omega
private theorem handleSimp_labels_list (xs : List Bvl.Exp) :
    getCodeLabelsList (handleSimpList xs) ⊆ getCodeLabelsList xs := by
  cases xs with
  | nil => simp [handleSimpList, getCodeLabelsList]
  | cons e es =>
    simp only [handleSimpList, getCodeLabelsList]
    exact Set.union_subset_union (handleSimp_labels_expr e) (handleSimp_labels_list es)
termination_by handleSizeList xs
decreasing_by all_goals (simp_all [handleSizeList]; omega)

private theorem makeHandle_labels (e d : Bvl.Exp) (l : Nat) :
    getCodeLabels (makeHandle e d l) ⊆ getCodeLabels e ∪ getCodeLabels d := by
  cases e with
  | raise e =>
    simp only [makeHandle]
    split
    · simp only [getCodeLabels, handleAdjVars_codeLabels.1]
      exact Set.union_subset_union (handleSimp_labels_expr (.raise e)) (handleSimp_labels_expr d)
    · simp only [getCodeLabels, getCodeLabelsList, Set.union_empty, handleAdjVars_codeLabels.1]
      exact Set.union_subset_union Set.Subset.rfl (handleSimp_labels_expr d)
  | «let» xs e =>
    simp only [makeHandle]
    split
    · simp only [getCodeLabels, handleAdjVars_codeLabels.1]
      exact Set.union_subset_union (handleSimp_labels_expr (.let xs e)) (handleSimp_labels_expr d)
    · simp only [getCodeLabels]
      have h := Set.union_subset_union (handleSimp_labels_list xs) (makeHandle_labels e d (l + xs.length))
      simpa only [Set.union_assoc] using h
  | ifThenElse x y z =>
    have ix := handleSimp_labels_expr x
    have iy := handleSimp_labels_expr y
    have iz := handleSimp_labels_expr z
    have id := handleSimp_labels_expr d
    have hy := makeHandle_labels y d l
    have hz := makeHandle_labels z d l
    have whole := handleSimp_labels_expr (.ifThenElse x y z)
    simp only [makeHandle]
    repeat' split
    all_goals simp only [getCodeLabels, handleAdjVars_codeLabels.1] at *
    all_goals simp only [Set.subset_def, Set.mem_union] at *
    all_goals intro k hk
    all_goals specialize ix k
    all_goals specialize iy k
    all_goals specialize iz k
    all_goals specialize id k
    all_goals specialize hy k
    all_goals specialize hz k
    all_goals specialize whole k
    all_goals aesop
  | _ =>
    simp only [makeHandle, getCodeLabels, handleAdjVars_codeLabels.1]
    exact Set.union_subset_union (handleSimp_labels_expr _) (handleSimp_labels_expr d)
termination_by handleSize e + handleSize d
decreasing_by
  all_goals simp_wf
  all_goals try simp only [handleSize]
  all_goals have h := handleSize_nonzero d
  all_goals try omega
end

/-- Handler simplification introduces no code labels in expressions, lists, or handlers. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "get_code_labels_handle_simp"]
theorem handleSimp_codeLabels :
    (∀ c, getCodeLabels (handleSimp c) ⊆ getCodeLabels c) ∧
    (∀ c, (⋃₀ (getCodeLabels '' {e | e ∈ handleSimpList c})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ c}))) ∧
    (∀ c d l, getCodeLabels (makeHandle c d l) ⊆ getCodeLabels c ∪ getCodeLabels d) := by
  refine ⟨handleSimp_labels_expr, ?_, makeHandle_labels⟩
  intro c
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  exact handleSimp_labels_list c

/-- The complete expression pass introduces no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_exp_code_labels"]
theorem compileExp_codeLabels (limit arity : Nat) (e : Bvl.Exp) :
    getCodeLabels (compileExp limit arity e) ⊆ getCodeLabels e := by
  have compiled := compile_codeLabels limit arity [handleSimp (BvlConst.compileExp e)]
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq, compileExp_list_head] at compiled
  simp only [getCodeLabelsList, Set.union_empty] at compiled
  exact compiled.trans ((handleSimp_codeLabels.1 _).trans (BvlConst.Proofs.compileExp_codeLabels e))

/-- Sequence splitting introduces no labels beyond its expression and continuation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_seqs_code_labels"]
theorem compileSeqs_codeLabels (limit : Nat) (e : Bvl.Exp) (acc : Option Bvl.Exp) :
    getCodeLabels (compileSeqs limit e acc) ⊆
      getCodeLabels e ∪ (match acc with | none => ∅ | some rest => getCodeLabels rest) := by
  change getCodeLabels (compileSeqsWith (fun limit e => compileExp limit 0 e) limit e acc) ⊆ _
  by_cases shape : ∃ first second, e = .let [first, second] (.var 1)
  · obtain ⟨first, second, rfl⟩ := shape
    simp only [compileSeqsWith]
    have outer := compileSeqs_codeLabels limit first (some (compileSeqs limit second acc))
    have inner := compileSeqs_codeLabels limit second acc
    simp only [getCodeLabels, getCodeLabelsList, Set.union_empty, Set.subset_def,
      Set.mem_union] at outer inner ⊢
    intro label present
    rcases outer label present with firstLabel | restLabel
    · exact Or.inl (Or.inl firstLabel)
    · rcases inner label restLabel with secondLabel | accLabel
      · exact Or.inl (Or.inr secondLabel)
      · exact Or.inr accLabel
  · have notShape : ∀ first second, e = .let [first, second] (.var 1) → False := by
      intro first second equal
      exact shape ⟨first, second, equal⟩
    cases acc with
    | none =>
      rw [compileSeqsWith.eq_2 _ limit e notShape]
      simpa only [Set.union_empty] using compileExp_codeLabels limit 0 e
    | some rest =>
      rw [compileSeqsWith.eq_3 _ limit e rest notShape]
      simpa only [getCodeLabels, getCodeLabelsList, Set.union_empty, Set.empty_union] using
        Set.union_subset_union (compileExp_codeLabels limit 0 e) (Set.Subset.rfl)
termination_by sizeOf e

end Flapjack.Compiler.Backend.BvlHandle.Proofs
