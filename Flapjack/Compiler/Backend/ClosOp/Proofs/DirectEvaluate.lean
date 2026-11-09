module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftEvaluate
public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend

@[expose] public section

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
recognizer stages fail on the other operand. This Flapjack proof helper includes branch-selection premises. -/
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
fail on the other operand. This Flapjack proof helper includes branch-selection premises. -/
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

/-- Word literal evaluation for the constant-recognizer cases. -/
private theorem evalWord {C F : Type} (trace : BackendCommon.Tra) (w : BitVec 64)
    (env : List Value) (s : State C F) :
    evaluate [.op trace (.blockOp (.constant (.constWord64 w))) []] env s =
      (.val [.word64 w], s) := by
  rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock, makeConst]

/-- Comparing a fixed-width word on the left is equivalent to the source
equal-constant operation, including its errors. This is proof infrastructure. -/
private theorem equalWordLeft {C F : Type} (trace t : BackendCommon.Tra) (w : BitVec 64)
    (y : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constWord64 w))) [], y]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.w64 w))) [y]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ [y] env s s (.word64 w) (evalWord trace w env s)]
  cases run : evaluate [y] env s with
  | mk result next =>
    cases result with
    | err err => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value y env s next values run
      cases value <;> simp [doApp, applyBlock, ClosSem.doEq, eq_comm]

/-- The symmetric fixed-width word comparison. This is proof infrastructure. -/
private theorem equalWordRight {C F : Type} (trace t : BackendCommon.Tra) (w : BitVec 64)
    (x : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constWord64 w))) []]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.w64 w))) [x]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  cases run : evaluate [x] env s with
  | mk result next =>
    cases result with
    | err err => rw [ClosProps.evaluate_cons_error x _ env s next err run]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s next values run
      rw [ClosProps.evaluate_cons_value x _ env s next value run]
      cases value <;> simp [evalWord, doApp, applyBlock, ClosSem.doEq]

/-- Source constant-recognizer case with a word literal on the left and
neither recognizer matching the other operand. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmWordLeft {C F : Type} (trace : BackendCommon.Tra) (w : BitVec 64)
    (y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst y = none) (noConstant : destOpNil destConstant y = none)
    (h : evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constWord64 w))) [], y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op trace (.blockOp (.constant (.constWord64 w))) []) y = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst (.op trace (.blockOp (.constant (.constWord64 w))) []) y = none := by
    change (match none, destOpNil destConst y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b)))
          [.op trace (.blockOp (.constant (.constWord64 w))) []])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant (.op trace (.blockOp (.constant (.constWord64 w))) []) y =
      some (.op .none (.blockOp (.equalConst (.w64 w))) [y]) := by
    change (match some (.w64 w), destOpNil destConstant y with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a)) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst b))
          [.op trace (.blockOp (.constant (.constWord64 w))) []])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalWordLeft trace t w y env s]
  exact h.1

/-- Symmetric source constant-recognizer case for a word literal. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmWordRight {C F : Type} (trace : BackendCommon.Tra) (w : BitVec 64)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst x = none) (noConstant : destOpNil destConstant x = none)
    (h : evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constWord64 w))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq x (.op trace (.blockOp (.constant (.constWord64 w))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst x (.op trace (.blockOp (.constant (.constWord64 w))) []) = none := by
    change (match destOpNil destConst x, none with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a)))
          [.op trace (.blockOp (.constant (.constWord64 w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant x (.op trace (.blockOp (.constant (.constWord64 w))) []) =
      some (.op .none (.blockOp (.equalConst (.w64 w))) [x]) := by
    change (match destOpNil destConstant x, some (.w64 w) with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a))
          [.op trace (.blockOp (.constant (.constWord64 w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst b)) [x])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalWordRight trace t w x env s]
  exact h.1

/-- Source constant-folding case for two fixed-width word literals. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmWordPair {C F : Type} (tx ty : BackendCommon.Tra) (x y : BitVec 64)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal)
        [.op tx (.blockOp (.constant (.constWord64 x))) [],
         .op ty (.blockOp (.constant (.constWord64 y))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op tx (.blockOp (.constant (.constWord64 x))) [])
        (.op ty (.blockOp (.constant (.constWord64 y))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have stage : directEq (.op tx (.blockOp (.constant (.constWord64 x))) [])
      (.op ty (.blockOp (.constant (.constWord64 y))) []) =
      some (mkBool (decide (y = x))) := by
    change some (mkBool (decide (ConstPart.w64 y = ConstPart.w64 x))) = _
    simp only [ConstPart.w64.injEq]
  rw [stage] at h
  have hz : z = mkBool (decide (y = x)) := by simpa using h.2.2.symm
  subst z
  have evalBool (b : Bool) : evaluate [mkBool b] env s = (.val [boolValue b], s) := by
    cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
      simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]
  rw [equalWordLeft tx t x _ env s, evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)] at h
  simp [evalWord, doApp, applyBlock] at h
  rw [evalBool]
  rcases h.1 with ⟨rfl, rfl⟩
  simp only [eq_comm]


/-- Block-encoded integer literal evaluation for the constant-recognizer cases. -/
private theorem evalBlockInt {C F : Type} (trace : BackendCommon.Tra) (w : Int)
    (env : List Value) (s : State C F) :
    evaluate [.op trace (.blockOp (.constant (.constInt w))) []] env s =
      (.val [.number w], s) := by
  rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock, makeConst]

/-- Comparing a block-encoded integer on the left is equivalent to the source
equal-constant operation, including its errors. This is proof infrastructure. -/
private theorem equalBlockIntLeft {C F : Type} (trace t : BackendCommon.Tra) (w : Int)
    (y : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constInt w))) [], y]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.int w))) [y]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ [y] env s s (.number w) (evalBlockInt trace w env s)]
  cases run : evaluate [y] env s with
  | mk result next =>
    cases result with
    | err err => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value y env s next values run
      cases value <;> simp [doApp, applyBlock, ClosSem.doEq, eq_comm]

/-- The symmetric block-encoded integer comparison. This is proof infrastructure. -/
private theorem equalBlockIntRight {C F : Type} (trace t : BackendCommon.Tra) (w : Int)
    (x : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constInt w))) []]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.int w))) [x]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  cases run : evaluate [x] env s with
  | mk result next =>
    cases result with
    | err err => rw [ClosProps.evaluate_cons_error x _ env s next err run]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s next values run
      rw [ClosProps.evaluate_cons_value x _ env s next value run]
      cases value <;> simp [evalBlockInt, doApp, applyBlock, ClosSem.doEq]

/-- Source constant-recognizer case with a block-encoded integer literal on the left and
neither recognizer matching the other operand. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmBlockIntLeft {C F : Type} (trace : BackendCommon.Tra) (w : Int)
    (y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst y = none) (noConstant : destOpNil destConstant y = none)
    (h : evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constInt w))) [], y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op trace (.blockOp (.constant (.constInt w))) []) y = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst (.op trace (.blockOp (.constant (.constInt w))) []) y = none := by
    change (match none, destOpNil destConst y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b)))
          [.op trace (.blockOp (.constant (.constInt w))) []])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant (.op trace (.blockOp (.constant (.constInt w))) []) y =
      some (.op .none (.blockOp (.equalConst (.int w))) [y]) := by
    change (match some (.int w), destOpNil destConstant y with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a)) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst b))
          [.op trace (.blockOp (.constant (.constInt w))) []])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalBlockIntLeft trace t w y env s]
  exact h.1

/-- Symmetric source constant-recognizer case for a block-encoded integer literal. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmBlockIntRight {C F : Type} (trace : BackendCommon.Tra) (w : Int)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst x = none) (noConstant : destOpNil destConstant x = none)
    (h : evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constInt w))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq x (.op trace (.blockOp (.constant (.constInt w))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst x (.op trace (.blockOp (.constant (.constInt w))) []) = none := by
    change (match destOpNil destConst x, none with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a)))
          [.op trace (.blockOp (.constant (.constInt w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant x (.op trace (.blockOp (.constant (.constInt w))) []) =
      some (.op .none (.blockOp (.equalConst (.int w))) [x]) := by
    change (match destOpNil destConstant x, some (.int w) with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a))
          [.op trace (.blockOp (.constant (.constInt w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst b)) [x])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalBlockIntRight trace t w x env s]
  exact h.1

/-- Source constant-folding case for two block-encoded integer literals. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmBlockIntPair {C F : Type} (tx ty : BackendCommon.Tra) (x y : Int)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal)
        [.op tx (.blockOp (.constant (.constInt x))) [],
         .op ty (.blockOp (.constant (.constInt y))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op tx (.blockOp (.constant (.constInt x))) [])
        (.op ty (.blockOp (.constant (.constInt y))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have stage : directEq (.op tx (.blockOp (.constant (.constInt x))) [])
      (.op ty (.blockOp (.constant (.constInt y))) []) =
      some (mkBool (decide (y = x))) := by
    change some (mkBool (decide (ConstPart.int y = ConstPart.int x))) = _
    simp only [ConstPart.int.injEq]
  rw [stage] at h
  have hz : z = mkBool (decide (y = x)) := by simpa using h.2.2.symm
  subst z
  have evalBool (b : Bool) : evaluate [mkBool b] env s = (.val [boolValue b], s) := by
    cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
      simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]
  rw [equalBlockIntLeft tx t x _ env s, evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)] at h
  simp [evalBlockInt, doApp, applyBlock] at h
  rw [evalBool]
  rcases h.1 with ⟨rfl, rfl⟩
  simp only [eq_comm]


/-- String literal evaluation for the constant-recognizer cases. -/
private theorem evalString {C F : Type} (trace : BackendCommon.Tra) (w : Flapjack.Basis.Pure.MlString.MlString)
    (env : List Value) (s : State C F) :
    evaluate [.op trace (.blockOp (.constant (.constStr w))) []] env s =
      (.val [.byteVector w.explode], s) := by
  rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock, makeConst]

/-- Comparing a byte string on the left is equivalent to the source
equal-constant operation, including its errors. This is proof infrastructure. -/
private theorem equalStringLeft {C F : Type} (trace t : BackendCommon.Tra) (w : Flapjack.Basis.Pure.MlString.MlString)
    (y : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constStr w))) [], y]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.str w))) [y]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ [y] env s s (.byteVector w.explode) (evalString trace w env s)]
  cases run : evaluate [y] env s with
  | mk result next =>
    cases result with
    | err err => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value y env s next values run
      cases value <;> simp [doApp, applyBlock, ClosSem.doEq]

/-- The symmetric byte string comparison. This is proof infrastructure. -/
private theorem equalStringRight {C F : Type} (trace t : BackendCommon.Tra) (w : Flapjack.Basis.Pure.MlString.MlString)
    (x : ClosLang.Exp) (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constStr w))) []]] env s =
      evaluate [.op .none (.blockOp (.equalConst (.str w))) [x]] env s := by
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp),
    evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)]
  cases run : evaluate [x] env s with
  | mk result next =>
    cases result with
    | err err => rw [ClosProps.evaluate_cons_error x _ env s next err run]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value x env s next values run
      rw [ClosProps.evaluate_cons_value x _ env s next value run]
      cases value <;> simp [evalString, doApp, applyBlock, ClosSem.doEq, eq_comm]

/-- Source constant-recognizer case with a string literal on the left and
neither recognizer matching the other operand. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmStringLeft {C F : Type} (trace : BackendCommon.Tra) (w : Flapjack.Basis.Pure.MlString.MlString)
    (y : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst y = none) (noConstant : destOpNil destConstant y = none)
    (h : evaluate [.op t (.blockOp .equal) [.op trace (.blockOp (.constant (.constStr w))) [], y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op trace (.blockOp (.constant (.constStr w))) []) y = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst (.op trace (.blockOp (.constant (.constStr w))) []) y = none := by
    change (match none, destOpNil destConst y with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b)))
          [.op trace (.blockOp (.constant (.constStr w))) []])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant (.op trace (.blockOp (.constant (.constStr w))) []) y =
      some (.op .none (.blockOp (.equalConst (.str w))) [y]) := by
    change (match some (.str w), destOpNil destConstant y with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a)) [y])
      | none, some b => some (.op .none (.blockOp (.equalConst b))
          [.op trace (.blockOp (.constant (.constStr w))) []])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalStringLeft trace t w y env s]
  exact h.1

/-- Symmetric source constant-recognizer case for a string literal. This Flapjack proof helper includes branch-selection premises. -/
theorem eqDirectThmStringRight {C F : Type} (trace : BackendCommon.Tra) (w : Flapjack.Basis.Pure.MlString.MlString)
    (x : ClosLang.Exp) (env : List Value) (s s1 : State C F)
    (res : Result (List Value) Value) (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (noInt : destOpNil destConst x = none) (noConstant : destOpNil destConstant x = none)
    (h : evaluate [.op t (.blockOp .equal) [x, .op trace (.blockOp (.constant (.constStr w))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq x (.op trace (.blockOp (.constant (.constStr w))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have intStage : eqDirectConst x (.op trace (.blockOp (.constant (.constStr w))) []) = none := by
    change (match destOpNil destConst x, none with
      | some a, some b => some (mkBool (a == b))
      | some a, none => some (.op .none (.blockOp (.equalConst (.int a)))
          [.op trace (.blockOp (.constant (.constStr w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
      | none, none => none) = _
    rw [noInt]
  have constantStage : eqDirectConstant x (.op trace (.blockOp (.constant (.constStr w))) []) =
      some (.op .none (.blockOp (.equalConst (.str w))) [x]) := by
    change (match destOpNil destConstant x, some (.str w) with
      | some a, some b => some (mkBool (decide (b = a)))
      | some a, none => some (.op .none (.blockOp (.equalConst a))
          [.op trace (.blockOp (.constant (.constStr w))) []])
      | none, some b => some (.op .none (.blockOp (.equalConst b)) [x])
      | none, none => none) = _
    rw [noConstant]
  have hz := h.2.2
  simp [directEq, intStage, constantStage] at hz
  subst z
  rw [← equalStringRight trace t w x env s]
  exact h.1

/-- Source constant-folding case for two byte string literals. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThmStringPair {C F : Type} (tx ty : BackendCommon.Tra) (x y : Flapjack.Basis.Pure.MlString.MlString)
    (env : List Value) (s s1 : State C F) (res : Result (List Value) Value)
    (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal)
        [.op tx (.blockOp (.constant (.constStr x))) [],
         .op ty (.blockOp (.constant (.constStr y))) []]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧
      directEq (.op tx (.blockOp (.constant (.constStr x))) [])
        (.op ty (.blockOp (.constant (.constStr y))) []) = some z) :
    evaluate [z] env s = (res, s1) := by
  have stage : directEq (.op tx (.blockOp (.constant (.constStr x))) [])
      (.op ty (.blockOp (.constant (.constStr y))) []) =
      some (mkBool (decide (y = x))) := by
    change some (mkBool (decide (ConstPart.str y = ConstPart.str x))) = _
    simp only [ConstPart.str.injEq]
  rw [stage] at h
  have hz : z = mkBool (decide (y = x)) := by simpa using h.2.2.symm
  subst z
  have evalBool (b : Bool) : evaluate [mkBool b] env s = (.val [boolValue b], s) := by
    cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
      simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]
  rw [equalStringLeft tx t x _ env s, evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp)] at h
  simp [evalString, doApp, applyBlock] at h
  rw [evalBool]
  rcases h.1 with ⟨rfl, rfl⟩
  cases x
  cases y
  simp [Flapjack.Basis.Pure.MlString.MlString.explode, eq_comm]

/-- Recover an integer literal from the source matcher. -/
private theorem intSome (x : ClosLang.Exp) (i : Int) (h : destOpNil destConst x = some i) :
    ∃ trace, x = .op trace (.intOp (.const i)) [] := by
  rw [destOpConst_eq_previous] at h
  cases x <;> try simp at h
  case op trace op args =>
    cases op <;> try simp at h
    case intOp op =>
      cases op <;> try simp at h
      case const v =>
        cases args <;> simp_all

/-- Recover one of the three source constant forms from the matcher. -/
private theorem constantSome (x : ClosLang.Exp) (c : ConstPart)
    (h : destOpNil destConstant x = some c) :
    (∃ trace i, x = .op trace (.blockOp (.constant (.constInt i))) []) ∨
    (∃ trace str, x = .op trace (.blockOp (.constant (.constStr str))) []) ∨
    (∃ trace w, x = .op trace (.blockOp (.constant (.constWord64 w))) []) := by
  rw [destOpConstant_eq_previous] at h
  cases x <;> try simp at h
  case op trace op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case constant value =>
        cases value <;> cases args <;> simp_all

/-- Recover a nullary constructor from the source matcher. -/
private theorem nilSome (x : ClosLang.Exp) (tag : Nat) (h : destOpNil destCons x = some tag) :
    ∃ trace, x = .op trace (.blockOp (.cons tag)) [] := by
  rw [destOpConsNil_eq_previous] at h
  cases x <;> try simp at h
  case op trace op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons v => cases args <;> simp_all

/-- Different constant kinds cause the original equality type error. -/
private theorem constPairError {C F : Type} (tx ty t : BackendCommon.Tra)
    (x y : ClosLang.Const) (env : List Value) (s : State C F)
    (bad : ClosSem.doEq (makeConst y) (makeConst x) = .typeError) :
    evaluate [.op t (.blockOp .equal)
      [.op tx (.blockOp (.constant x)) [], .op ty (.blockOp (.constant y)) []]] env s =
        (.err (.abort .typeError), s) := by
  have evalConst (trace : BackendCommon.Tra) (c : ClosLang.Const) :
      evaluate [.op trace (.blockOp (.constant c)) []] env s = (.val [makeConst c], s) := by
    rw [evaluate_ordinaryOp_eq trace _ [] env s (by simp) (by simp)]
    simp [evaluate, doApp, applyBlock]
  rw [evaluate_ordinaryOp_eq t _ _ env s (by simp) (by simp)]
  rw [ClosProps.evaluate_cons_value _ _ env s s (makeConst x) (evalConst tx x)]
  simp [evalConst, doApp, applyBlock, bad]

/-- Source direct equality preserves evaluation outside type errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_direct_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqDirectThm {C F : Type} (x y : ClosLang.Exp) (env : List Value)
    (s : State C F) (res : Result (List Value) Value) (s1 : State C F)
    (t : BackendCommon.Tra) (z : ClosLang.Exp)
    (h : evaluate [.op t (.blockOp .equal) [x, y]] env s = (res, s1) ∧
      res ≠ .err (.abort .typeError) ∧ directEq x y = some z) :
    evaluate [z] env s = (res, s1) := by
  cases ix : destOpNil destConst x with
  | some i =>
    obtain ⟨trace, rfl⟩ := intSome x i ix
    exact eqDirectThmIntLeft trace i y env s s1 res t z h
  | none =>
    cases iy : destOpNil destConst y with
    | some i =>
      obtain ⟨trace, rfl⟩ := intSome y i iy
      exact eqDirectThmIntRight trace i x env s s1 res t z h
    | none =>
      cases cx : destOpNil destConstant x with
      | some a =>
        cases cy : destOpNil destConstant y with
        | none =>
          rcases constantSome x a cx with ⟨trace, i, rfl⟩ | ⟨trace, str, rfl⟩ | ⟨trace, w, rfl⟩
          · exact eqDirectThmBlockIntLeft trace i y env s s1 res t z iy cy h
          · exact eqDirectThmStringLeft trace str y env s s1 res t z iy cy h
          · exact eqDirectThmWordLeft trace w y env s s1 res t z iy cy h
        | some b =>
          rcases constantSome x a cx with ⟨tx, i, rfl⟩ | ⟨tx, str, rfl⟩ | ⟨tx, w, rfl⟩ <;>
            rcases constantSome y b cy with ⟨ty, j, rfl⟩ | ⟨ty, str2, rfl⟩ | ⟨ty, w2, rfl⟩
          all_goals first
            | exact eqDirectThmBlockIntPair _ _ _ _ env s s1 res t z h
            | exact eqDirectThmStringPair _ _ _ _ env s s1 res t z h
            | exact eqDirectThmWordPair _ _ _ _ env s s1 res t z h
            | rw [constPairError tx ty t (.constInt i) (.constStr str2) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
            | rw [constPairError tx ty t (.constInt i) (.constWord64 w2) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
            | rw [constPairError tx ty t (.constStr str) (.constInt j) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
            | rw [constPairError tx ty t (.constStr str) (.constWord64 w2) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
            | rw [constPairError tx ty t (.constWord64 w) (.constInt j) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
            | rw [constPairError tx ty t (.constWord64 w) (.constStr str2) env s (by simp [makeConst, ClosSem.doEq])] at h; simp at h
          all_goals exact (h.2.1 h.1.1.symm).elim
      | none =>
        cases cy : destOpNil destConstant y with
        | some b =>
          rcases constantSome y b cy with ⟨trace, i, rfl⟩ | ⟨trace, str, rfl⟩ | ⟨trace, w, rfl⟩
          · exact eqDirectThmBlockIntRight trace i x env s s1 res t z ix cx h
          · exact eqDirectThmStringRight trace str x env s s1 res t z ix cx h
          · exact eqDirectThmWordRight trace w x env s s1 res t z ix cx h
        | none =>
          cases nx : destOpNil destCons x with
          | some tag =>
            obtain ⟨trace, rfl⟩ := nilSome x tag nx
            exact eqDirectThmNilLeft trace tag y env s s1 res t z iy cy h
          | none =>
            cases ny : destOpNil destCons y with
            | some tag =>
              obtain ⟨trace, rfl⟩ := nilSome y tag ny
              exact eqDirectThmNilRight trace tag x env s s1 res t z ix cx h
            | none =>
              have impossible : directEq x y = none := by
                have intStage : eqDirectConst x y = none := by
                  change (match destOpNil destConst x, destOpNil destConst y with
                    | some a, some b => some (mkBool (a == b))
                    | some a, none => some (.op .none (.blockOp (.equalConst (.int a))) [y])
                    | none, some b => some (.op .none (.blockOp (.equalConst (.int b))) [x])
                    | none, none => none) = _
                  rw [ix, iy]
                have constantStage : eqDirectConstant x y = none := by
                  change (match destOpNil destConstant x, destOpNil destConstant y with
                    | some a, some b => some (mkBool (decide (b = a)))
                    | some a, none => some (.op .none (.blockOp (.equalConst a)) [y])
                    | none, some b => some (.op .none (.blockOp (.equalConst b)) [x])
                    | none, none => none) = _
                  rw [cx, cy]
                have nilStage : eqDirectNil x y = none := by
                  change (match destOpNil destCons x, destOpNil destCons y with
                    | some a, some b => some (mkBool (a == b))
                    | some a, none => some (.op .none (.blockOp (.tagLenEq a 0)) [y])
                    | none, some b => some (.op .none (.blockOp (.tagLenEq b 0)) [x])
                    | none, none => none) = _
                  rw [nx, ny]
                simp [directEq, intStage, constantStage, nilStage]
              rw [impossible] at h
              simp at h

end Flapjack.Compiler.Backend.ClosOp
