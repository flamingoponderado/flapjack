module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.SemanticPrimitivesHOL.PatternMatch
public import Flapjack.SemanticPrimitivesHOL.Control
public import Flapjack.EvaluateHOL
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Short independent facts from `evaluatePropsScript.sml`. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.NamespaceHOL Flapjack.AstHOL Flapjack.EvaluateHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "pair_CASE_eq_forall"]
theorem pairCase_eq_forall {α β : Type} (x : α × β) (P : α → β → Prop) :
    (match x with | (a, b) => P a b) ↔ ∀ a b, x = (a, b) → P a b := by
  cases x with
  | mk a b => simp

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "same_type_sym"]
theorem sameType_sym (t1 t2 : Stamp) (h : sameType t1 t2 = true) : sameType t2 t1 = true := by
  cases t1
  all_goals cases t2
  all_goals simp [sameType] at h ⊢
  omega

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "same_type_trans"]
theorem sameType_trans (t1 t2 t3 : Stamp) (h12 : sameType t1 t2 = true)
    (h13 : sameType t1 t3 = true) : sameType t2 t3 = true := by
  cases t1
  all_goals cases t2
  all_goals cases t3
  all_goals simp [sameType] at h12 h13 ⊢
  omega

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "combine_dec_result_eq_Rerr"]
theorem combineDecResult_eq_err {α : Type} (env : SemEnv Value) (r : Result (SemEnv Value) α)
    (e : ErrorResult α) : combineDecResult env r = .err e ↔ r = .err e := by
  cases r
  all_goals simp [combineDecResult]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "result_rel_list_result"]
theorem resultRel_listResult {α β γ δ : Type} (R : α → β → Prop) (Q : γ → δ → Prop)
    (r1 : Result α γ) (r2 : Result β δ) :
    resultRel (List.Forall₂ R) Q (listResult r1) (listResult r2) ↔ resultRel R Q r1 r2 := by
  cases r1
  all_goals cases r2
  all_goals simp [resultRel, listResult]

/-- Flapjack proof infrastructure: the `canPmatchAll` recursion step in the
shape of the HOL equation `can_pmatch_all_def`. -/
private theorem canPmatchAll_cons (envC : Namespace ModN ConN (Nat × Stamp))
    (refs : Store Value) (p : Pat) (ps : List Pat) (v : Value) :
    canPmatchAll envC refs (p :: ps) v = true ↔
      (pmatch envC refs p v [] ≠ .typeError ∧ canPmatchAll envC refs ps v = true) := by
  simp only [canPmatchAll, List.all_cons]
  cases pmatch envC refs p v [] with
  | noMatch => simp
  | typeError => simp
  | «match» bindings => simp

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "can_pmatch_all_EVERY"]
theorem canPmatchAll_EVERY (envC : Namespace ModN ConN (Nat × Stamp)) (refs : Store Value)
    (ps : List Pat) (v : Value) :
    canPmatchAll envC refs ps v = true ↔ ∀ p ∈ ps, pmatch envC refs p v [] ≠ .typeError := by
  induction ps with
  | nil => simp [canPmatchAll]
  | cons p ps ih =>
    rw [canPmatchAll_cons]
    simp [ih, List.mem_cons]

end Flapjack.EvaluateProps
