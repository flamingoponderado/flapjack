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

/-- A nullary constructor evaluates without modifying the state. -/
private theorem evalNil {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (env : List Value) (s : State C F) :
    evaluate [.op trace (.blockOp (.cons tag)) []] env s = (.val [.block tag []], s) := by
  rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock]

/-- Equality with a nullary constructor on the left is a tag-and-length
test, including error and state behavior. This is proof infrastructure. -/
private theorem equalNilLeft {C F : Type} (trace t : BackendCommon.Tra) (tag : Nat)
    (y : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.cons tag)) [], y]] env s =
      evaluate [.op .none (.blockOp (.tagLenEq tag 0)) [y]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ [y] env s s (.block tag []) (evalNil trace tag env s)]
  cases run : evaluate [y] env s with
  | mk result next =>
    cases result with
    | err err => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value y env s next values run
      cases value with
      | block actual fields =>
        by_cases h : tag = actual
        · subst actual
          cases fields <;> simp [doApp, applyBlock, ClosSem.doEq, ClosSem.doEqList]
        · have h' : actual ≠ tag := Ne.symm h
          have hbeq : (actual == tag) = false := beq_eq_false_iff_ne.mpr h'
          cases fields <;> simp [doApp, applyBlock, ClosSem.doEq, hbeq, h']
      | _ => simp [doApp, applyBlock, ClosSem.doEq]

/-- Equality with a nullary constructor on the right is a tag-and-length
test, including error and state behavior. This is proof infrastructure. -/
private theorem equalNilRight {C F : Type} (trace t : BackendCommon.Tra) (tag : Nat)
    (x : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.cons tag)) []]] env s =
      evaluate [.op .none (.blockOp (.tagLenEq tag 0)) [x]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  cases run : evaluate [x] env s with
  | mk result next =>
    cases result with
    | err err => rw [ClosProps.evaluate_cons_error x _ env s next err run]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s next values run
      rw [ClosProps.evaluate_cons_value x _ env s next value run]
      cases value with
      | block actual fields =>
        by_cases h : tag = actual
        · subst actual
          cases fields <;> simp [evalNil, doApp, applyBlock, ClosSem.doEq, ClosSem.doEqList]
        · have h' : actual ≠ tag := Ne.symm h
          have hbeq : (actual == tag) = false := beq_eq_false_iff_ne.mpr h'
          cases fields <;> simp [evalNil, doApp, applyBlock, ClosSem.doEq, hbeq, h]
      | _ => simp [evalNil, doApp, applyBlock, ClosSem.doEq]

/-- Folding two nullary constructors preserves their comparison result. -/
private theorem evalEqualNil {C F : Type} (trace : BackendCommon.Tra) (i j : Nat)
    (env : List Value) (s : State C F) :
    evaluate [.op .none (.blockOp (.tagLenEq i 0)) [.op trace (.blockOp (.cons j)) []]] env s =
      evaluate [mkBool (i == j)] env s := by
  have evalBool (b : Bool) : evaluate [mkBool b] env s = (.val [boolValue b], s) := by
    cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
      simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]
  rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  by_cases h : i = j
  · subst j
    simp [evalNil, doApp, applyBlock, evalBool]
  · have h' : j ≠ i := Ne.symm h
    have hij : (i == j) = false := beq_eq_false_iff_ne.mpr h
    have hji : (j == i) = false := beq_eq_false_iff_ne.mpr h'
    simp [evalNil, doApp, applyBlock, evalBool, hij, hji]

/-- Nullary-constructor case of direct equality after both earlier source
recognizer stages fail on the other operand. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmNilLeft {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst y = none) (noConstant : destOpNil destConstant y = none)
    (h : evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.cons tag)) [], y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op trace (.blockOp (.cons tag)) []) y = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst (.op trace (.blockOp (.cons tag)) []) y = none := by
    change (match none, destOpNil destConst y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b)))
          [.op trace (.blockOp (.cons tag)) []])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant (.op trace (.blockOp (.cons tag)) []) y = none := by
    change (match none, destOpNil destConstant y with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a)) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst b))
          [.op trace (.blockOp (.cons tag)) []])
      | none, none => none) = _
    rw [noConstant]
  have nilStage : eqDirectNil (.op trace (.blockOp (.cons tag)) []) y =
      match destOpNil destCons y with
      | some j => some (mkBool (tag == j))
      | none => some (.op .none (.blockOp (.tagLenEq tag 0)) [y]) := by
    change (match some tag, destOpNil destCons y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.tagLenEq a 0)) [y])
      | none, some b => some (.op .none (.blockOp (.tagLenEq b 0))
          [.op trace (.blockOp (.cons tag)) []])
      | none, none => none) = _
    cases destOpNil destCons y <;> rfl
  cases hy : destOpNil destCons y with
  | none =>
    have hz := h.2.2
    simp [directEq, intStage, constantStage, nilStage, hy] at hz
    subst z
    rw [← equalNilLeft trace t tag y env s]
    exact h.1
  | some j =>
    have hz := h.2.2
    simp [directEq, intStage, constantStage, nilStage, hy] at hz
    subst z
    have shape := hy
    rw [destOpConsNil_eq_previous] at shape
    cases y <;> try simp at shape
    case op ty op ys =>
      cases op <;> try simp at shape
      case blockOp bo =>
        cases bo <;> try simp at shape
        case cons v =>
          cases ys with
          | nil =>
            simp only [Option.some.injEq] at shape
            subst v
            rw [← evalEqualNil ty tag j env s, ← equalNilLeft trace t tag _ env s]
            exact h.1
          | cons arg rest => simp at shape

/-- Symmetric nullary-constructor case after the earlier recognizer stages
fail on the other operand. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmNilRight {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst x = none) (noConstant : destOpNil destConstant x = none)
    (h : evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.cons tag)) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq x (.op trace (.blockOp (.cons tag)) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  cases hx : destOpNil destCons x with
  | some j =>
    have shape := hx
    rw [destOpConsNil_eq_previous] at shape
    cases x <;> try simp at shape
    case op tx op xs =>
      cases op <;> try simp at shape
      case blockOp bo =>
        cases bo <;> try simp at shape
        case cons v =>
          cases xs with
          | nil =>
            exact eqDirectThmNilLeft tx v _ env s s1 res t z rfl rfl h
          | cons arg rest => simp at shape
  | none =>
    have intStage : eqDirectConst x (.op trace (.blockOp (.cons tag)) []) = none := by
      change (match destOpNil destConst x, none with
        | some a, some b => some (mkBool (a == b))
        | some a, none => some (.op .none (.blockOp (.equalConst (.int a)))
            [.op trace (.blockOp (.cons tag)) []])
        | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
        | none, none => none) = _
      rw [noInt]
    have constantStage : eqDirectConstant x (.op trace (.blockOp (.cons tag)) []) = none := by
      change (match destOpNil destConstant x, none with
        | some a, some b => some (mkBool (decide (b = a)))
        | some a, none => some (.op .none (.blockOp (.equalConst a))
            [.op trace (.blockOp (.cons tag)) []])
        | none, some b => some (.op .none (.blockOp (.equalConst b)) [x])
        | none, none => none) = _
      rw [noConstant]
    have nilStage : eqDirectNil x (.op trace (.blockOp (.cons tag)) []) =
        some (.op .none (.blockOp (.tagLenEq tag 0)) [x]) := by
      change (match destOpNil destCons x, some tag with
        | some a, some b => some (mkBool (a == b))
        | some a, none => some (.op .none (.blockOp (.tagLenEq a 0))
            [.op trace (.blockOp (.cons tag)) []])
        | none, some b => some (.op .none (.blockOp (.tagLenEq b 0)) [x])
        | none, none => none) = _
      rw [hx]
    have hz := h.2.2
    simp [directEq, intStage, constantStage, nilStage] at hz
    subst z
    rw [← equalNilRight trace t tag x env s]
    exact h.1

end Flapjack.Compiler.Backend.ClosOp
