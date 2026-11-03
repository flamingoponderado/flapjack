import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend

/-! Semantic cases for source direct equality simplification. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace DirectEvaluatePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DirectEvaluatePort

/-- Integer literal evaluation, used to compare the two source operations. -/
private theorem evalInt {C F : Type} (trace : BackendCommon.Tra) (i : Int)
    (env : List Value) (s : State C F) :
    evaluate [.op trace (.intOp (.const i)) []] env s = (.val [.number i], s) := by
  rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyNumeric, doIntApp]

/-- Comparing a literal integer on the left uses the same dispatcher result
as the equal-constant operation. This is proof infrastructure. -/
private theorem equalIntLeft {C F : Type} (trace t : BackendCommon.Tra) (i : Int)
    (y : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [.op trace (.intOp (.const i)) [], y]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.int i))) [y]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ [y] env s s (.number i) (evalInt trace i env s)]
  cases run : evaluate [y] env s with
  | mk result next =>
    cases result with
    | err err => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value y env s next values run
      cases value <;> simp [doApp, applyBlock, ClosSem.doEq, eq_comm]

/-- Comparing a literal integer on the right has the same result, including
error and state behavior. This is proof infrastructure. -/
private theorem equalIntRight {C F : Type} (trace t : BackendCommon.Tra) (i : Int)
    (x : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [x, .op trace (.intOp (.const i)) []]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.int i))) [x]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  cases run : evaluate [x] env s with
  | mk result next =>
    cases result with
    | err err =>
      rw [ClosProps.evaluate_cons_error x _ env s next err run]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s next values run
      rw [ClosProps.evaluate_cons_value x _ env s next value run]
      cases value <;> simp [evalInt, doApp, applyBlock, ClosSem.doEq]

/-- Folding two integer constants preserves their comparison result. -/
private theorem evalEqualIntConst {C F : Type} (trace : BackendCommon.Tra) (i j : Int)
    (env : List Value) (s : State C F) :
    evaluate [.op .none (.blockOp (.equalConst (.int i))) [.op trace (.intOp (.const j)) []]] env s =
      evaluate [mkBool (i == j)] env s := by
  rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  simp [evalInt, doApp, applyBlock, mkBool]
  split <;> simp_all [evaluate_ordinaryOp_eq, evaluate, doApp, applyBlock, boolValue,
    BackendCommon.trueTag, BackendCommon.falseTag]

/-- Case of direct equality with an integer literal on the left. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmIntLeft {C F : Type} (trace : BackendCommon.Tra) (i : Int)
    (y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal) [.op trace (.intOp (.const i)) [], y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op trace (.intOp (.const i)) []) y = some z) :
    evaluate [z] env s = (res, s1) := by
  have stage : eqDirectConst (.op trace (.intOp (.const i)) []) y =
      match destOpNil destConst y with
      | some j => some (mkBool (i == j))
      | none => some (.op .none (.blockOp (.equalConst (.int i))) [y]) := by
    change (match some i, destOpNil destConst y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b)))
          [.op trace (.intOp (.const i)) []])
      | none, none => none) = _
    cases destOpNil destConst y <;> rfl
  cases hy : destOpNil destConst y with
  | none =>
    have hz := h.2.2
    simp [directEq, stage, hy] at hz
    subst z
    rw [← equalIntLeft trace t i y env s]
    exact h.1
  | some j =>
    have hz := h.2.2
    simp [directEq, stage, hy] at hz
    subst z
    have shape := hy
    rw [destOpConst_eq_previous] at shape
    cases y <;> try simp at shape
    case op ty op ys =>
      cases op <;> try simp at shape
      case intOp io =>
        cases io <;> try simp at shape
        case const v =>
          cases ys with
          | nil =>
            simp only [Option.some.injEq] at shape
            subst v
            rw [← evalEqualIntConst ty i j env s, ← equalIntLeft trace t i _ env s]
            exact h.1
          | cons arg rest => simp at shape

/-- Case of direct equality with an integer literal on the right. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmIntRight {C F : Type} (trace : BackendCommon.Tra) (i : Int)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal) [x, .op trace (.intOp (.const i)) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq x (.op trace (.intOp (.const i)) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  cases hx : destOpNil destConst x with
  | some j =>
    have shape := hx
    rw [destOpConst_eq_previous] at shape
    cases x <;> try simp at shape
    case op tx op xs =>
      cases op <;> try simp at shape
      case intOp io =>
        cases io <;> try simp at shape
        case const v =>
          cases xs with
          | nil => exact eqDirectThmIntLeft tx v _ env s s1 res t z h
          | cons arg rest => simp at shape
  | none =>
    have stage : eqDirectConst x (.op trace (.intOp (.const i)) []) =
        some (.op .none (.blockOp (.equalConst (.int i))) [x]) := by
      change (match destOpNil destConst x, some i with
        | some a, some b => some (mkBool (a == b))
        | some a, none => some (.op .none (.blockOp (.equalConst (.int a)))
            [.op trace (.intOp (.const i)) []])
        | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
        | none, none => none) = _
      rw [hx]
    have hz := h.2.2
    simp [directEq, stage] at hz
    subst z
    rw [← equalIntRight trace t i x env s]
    exact h.1

end Flapjack.Compiler.Backend.ClosOp
