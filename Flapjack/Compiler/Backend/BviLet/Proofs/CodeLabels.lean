module

public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels
public import Flapjack.Compiler.Backend.BviLet.Helpers
public import Flapjack.Compiler.Backend.BviLet.SourceList

@[expose] public section

/-! Code-label preservation for BVI let propagation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs

/-- Deleting a propagated variable preserves its code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "dest_var_code_labels"]
theorem deleteVar_codeLabels (x : Bvi.Exp) :
    BviProps.getCodeLabels (deleteVar x) = BviProps.getCodeLabels x := by
  cases x <;> simp [deleteVar, BviProps.getCodeLabels, BviProps.getCodeLabelsList,
    ClosLang.assignGetCodeLabel]

open Flapjack.Compiler.Backend.BviProps

private theorem deleteVar_labelsList (xs : List Bvi.Exp) :
    getCodeLabelsList (xs.map deleteVar) = getCodeLabelsList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [getCodeLabelsList, deleteVar_codeLabels, ih]

private theorem labelsList_append (xs ys : List Bvi.Exp) :
    getCodeLabelsList (xs ++ ys) = getCodeLabelsList xs ∪ getCodeLabelsList ys := by
  induction xs with
  | nil => simp [getCodeLabelsList]
  | cons x xs ih => simp [getCodeLabelsList, ih, Set.union_assoc]

private theorem compileList_labels (env : List Nat) (d : Nat) (xs : List Bvi.Exp)
    (each : ∀ e ∈ xs, getCodeLabels (compileSing env d e) = getCodeLabels e) :
    getCodeLabelsList (compileList env d xs) = getCodeLabelsList xs := by
  induction xs with
  | nil => rw [compileList.eq_1]
  | cons e es ih =>
    rw [compileList.eq_2]
    simp only [getCodeLabelsList]
    rw [each e (by simp), ih (by intro e h; exact each e (by simp [h]))]

private theorem compileSing_labels (env : List Nat) (d : Nat) (e : Bvi.Exp) :
    getCodeLabels (compileSing env d e) = getCodeLabels e := by
  cases e with
  | var v => simp only [compileSing.eq_1, getCodeLabels]
  | ifThenElse x y z =>
    simp only [compileSing.eq_2, getCodeLabels, compileSing_labels env d x,
      compileSing_labels env d y, compileSing_labels env d z]
  | «let» xs body =>
    cases xs with
    | nil =>
      simp only [compileSing.eq_3, getCodeLabels, getCodeLabelsList, Set.empty_union]
      exact compileSing_labels env d body
    | cons x xs =>
      have bindings := compileList_labels env d (x :: xs)
        (fun e member => compileSing_labels env d e)
      by_cases hv : ∃ v, body = .var v
      · obtain ⟨v, rfl⟩ := hv
        rw [compileSing.eq_4]
        split
        · have earlier := compileList_labels env d (x :: xs).dropLast
            (fun e member => compileSing_labels env d e)
          have last := compileSing_labels (env.map ((x :: xs).length - 1 + ·))
            (d + ((x :: xs).length - 1)) ((x :: xs).getLast (by simp))
          simp only [getCodeLabels, earlier, last, Set.union_empty]
          have decomp := List.dropLast_concat_getLast (by simp : x :: xs ≠ [])
          calc
            _ = getCodeLabelsList ((x :: xs).dropLast ++ [(x :: xs).getLast (by simp)]) := by
              rw [labelsList_append]
              simp [getCodeLabelsList]
            _ = _ := by rw [decomp]
        · simp only [getCodeLabels, deleteVar_labelsList, bindings, compileSing.eq_1,
            Set.union_empty]
      · have neq : ∀ v, body = .var v → False := by
          intro v eq; exact hv ⟨v, eq⟩
        rw [compileSing.eq_5 env d x xs body neq]
        simp only [getCodeLabels, deleteVar_labelsList, bindings,
          compileSing_labels (extractList (compileList env d (x :: xs)) ++ env) d body]
  | raise x =>
    simp only [compileSing.eq_6, getCodeLabels, compileSing_labels env d x]
  | tick x =>
    simp only [compileSing.eq_7, getCodeLabels, compileSing_labels env d x]
  | force loc v => simp only [compileSing.eq_8, getCodeLabels]
  | op op xs =>
    have h := compileList_labels env d xs (fun e member => compileSing_labels env d e)
    simp only [compileSing.eq_9, getCodeLabels, h]
  | call ticks dest xs handler =>
    have h := compileList_labels env d xs (fun e member => compileSing_labels env d e)
    cases handler with
    | none => simp only [compileSing.eq_10, getCodeLabels, h]
    | some handler =>
      simp only [compileSing.eq_11, getCodeLabels, h, compileSing_labels (0 :: env) d handler]
  | «return» xs =>
    have h := compileList_labels env d xs (fun e member => compileSing_labels env d e)
    simp only [compileSing.eq_12, getCodeLabels, h]
  | letCall rets ticks dest xs body =>
    have h := compileList_labels env d xs (fun e member => compileSing_labels env d e)
    simp only [compileSing.eq_13, getCodeLabels, h,
      compileSing_labels (List.replicate rets 0 ++ env) d body]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals try (have h := List.sizeOf_lt_of_mem member; have bound := BviLet.sizeOf_dropLast_le (x :: xs); simp only [List.cons.sizeOf_spec] at *; omega)
  all_goals try (have h := List.sizeOf_lt_of_mem member; omega)
  all_goals try (have h := BviLet.sizeOf_getLast_le (x :: xs) (by simp); simp only [List.cons.sizeOf_spec] at h; omega)

/-- Let propagation preserves exactly the labels in the expression list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "compile_code_labels"]
theorem compile_codeLabels (env : List Nat) (d : Nat) (xs : List Bvi.Exp) :
    (⋃₀ (getCodeLabels '' {e | e ∈ BviLet.compile env d xs})) =
    (⋃₀ (getCodeLabels '' {e | e ∈ xs})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq, compile_eq_compileList]
  exact compileList_labels env d xs (fun e _ => compileSing_labels env d e)

/-- Compiling one expression preserves exactly its labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "compile_exp_code_labels"]
theorem compileExp_codeLabels (e : Bvi.Exp) : getCodeLabels (BviLet.compileExp e) = getCodeLabels e := by
  rw [compileExp_eq, compileSing_labels]

end Flapjack.Compiler.Backend.BviLet.Proofs
