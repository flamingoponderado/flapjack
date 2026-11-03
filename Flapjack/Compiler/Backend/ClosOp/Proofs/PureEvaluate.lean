import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftCorrect
import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean

/-! Pure-expression evaluation facts used by closure smart operations. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace PureEvaluatePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end PureEvaluatePort

/-- A successful pure list evaluation agrees with evaluation of every
in-range expression in isolation. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_EL"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateEl {C F : Type} (xs : List ClosLang.Exp) (i : Nat) (vs : List Value)
    (env : List Value) (s : State C F)
    (h : evaluate xs env s = (.val vs, s) ∧ i < xs.length ∧
      ∀ x ∈ xs, ClosLang.pure x = true) :
    evaluate [@Flapjack.holEl ClosLang.Exp ⟨.var .none 0⟩ i xs] env s =
      (.val [@Flapjack.holEl Value ⟨.number 0⟩ i vs], s) := by
  induction xs generalizing i vs with
  | nil => simp at h
  | cons x xs ih =>
    rcases h with ⟨run, bound, pure⟩
    have headPure : pureList [x] = true := by simp [pureList, pure x (by simp)]
    cases headRun : evaluate [x] env s with
    | mk headResult headState =>
      cases headResult with
      | err err =>
        rw [ClosProps.evaluate_cons_error x xs env s headState err headRun] at run
        cases run
      | val headValues =>
        obtain ⟨headValue, rfl⟩ := evaluate_singleton_value x env s headState headValues headRun
        obtain ⟨_, _, stateEq⟩ := ClosProps.evaluate_pure [x] env s headState (.val [headValue])
          headPure headRun (by simp)
        subst headState
        rw [ClosProps.evaluate_cons_value x xs env s s headValue headRun] at run
        cases tailRun : evaluate xs env s with
        | mk tailResult tailState =>
          cases tailResult with
          | err err => simp [tailRun] at run
          | val tailValues =>
            simp only [tailRun, Prod.mk.injEq, Result.val.injEq] at run
            rcases run with ⟨rfl, rfl⟩
            cases i with
            | zero => simpa [Flapjack.holEl, Flapjack.holHd] using headRun
            | succ i =>
              simp only [Flapjack.holEl, List.tail_cons]
              apply ih i tailValues
              exact ⟨tailRun, by simpa using bound, fun y hy => pure y (by simp [hy])⟩

/-- Each child of a simple constructor expression is simple. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "simpl_exp_Cons_EL"]
theorem simpleExpConsEl (trace : BackendCommon.Tra) (tag : Nat)
    (xs : List ClosLang.Exp) (i : Nat)
    (h : SimpleExp (.op trace (.blockOp (.cons tag)) xs) ∧ i < xs.length) :
    SimpleExp (@Flapjack.holEl ClosLang.Exp ⟨.var .none 0⟩ i xs) := by
  cases h.1 with
  | cons _ _ _ children =>
    rw [@Flapjack.holEl_eq_getElem ClosLang.Exp ⟨.var .none 0⟩ i xs h.2]
    exact children _ (List.getElem_mem h.2)

/-- Evaluation of a constructed boolean. This is proof infrastructure. -/
private theorem evaluateMkBool {C F : Type} (b : Bool) (env : List Value) (s : State C F) :
    evaluate [mkBool b] env s = (.val [boolValue b], s) := by
  cases b <;> rw [mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)] <;>
    simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag, BackendCommon.trueTag]

/-- A false head makes a conjunction false. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_ConjList_F"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateConjListFalse {C F : Type} (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List Value) (s : State C F)
    (h : evaluate [x] env s = (.val [boolValue false], s)) :
    evaluate [conjList (x :: xs)] env s = (.val [boolValue false], s) := by
  cases xs with
  | nil => exact h
  | cons y ys =>
    simp only [conjList]
    rw [evaluate, fixClock_evaluate, h]
    simpa [asBool, boolValue, BackendCommon.falseTag] using evaluateMkBool false env s

/-- A true head leaves evaluation to the remaining conjunction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_ConjList_T"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateConjListTrue {C F : Type} (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List Value) (s : State C F) (res : Result (List Value) Value × State C F)
    (h : evaluate [x] env s = (.val [boolValue true], s) ∧
      evaluate [conjList xs] env s = res) :
    evaluate [conjList (x :: xs)] env s = res := by
  cases xs with
  | nil =>
    have : evaluate [conjList []] env s = (.val [boolValue true], s) := evaluateMkBool true env s
    simp only [conjList] at ⊢
    rw [h.2.symm, this, h.1]
  | cons y ys =>
    simp only [conjList]
    rw [evaluate, fixClock_evaluate, h.1]
    simpa [asBool, boolValue, BackendCommon.trueTag] using h.2

/-- A successful pure conjunction exposes its head boolean and the result
of the remaining conjunction. This is proof infrastructure. -/
private theorem conjunctionHead {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List Value) (s : State C F) (b : Bool)
    (pure : ClosLang.pure x = true)
    (run : evaluate [conjList (x :: y :: xs)] env s = (.val [boolValue b], s)) :
    (evaluate [x] env s = (.val [boolValue false], s) ∧ b = false) ∨
      (evaluate [x] env s = (.val [boolValue true], s) ∧
       evaluate [conjList (y :: xs)] env s = (.val [boolValue b], s)) := by
  have headPure : pureList [x] = true := by simp [pureList, pure]
  cases headRun : evaluate [x] env s with
  | mk headResult headState =>
    cases headResult with
    | err err =>
      simp only [conjList] at run
      rw [evaluate, fixClock_evaluate, headRun] at run
      cases run
    | val headValues =>
      obtain ⟨v, rfl⟩ := evaluate_singleton_value x env s headState headValues headRun
      obtain ⟨_, _, stateEq⟩ := ClosProps.evaluate_pure [x] env s headState (.val [v])
        headPure headRun (by simp)
      subst headState
      simp only [conjList] at run
      rw [evaluate, fixClock_evaluate, headRun] at run
      cases dec : asBool v with
      | none => simp [dec] at run
      | some flag =>
        have valueEq := (asBool_eq_some v flag).mp dec
        subst v
        cases flag with
        | false =>
          simp [asBool, boolValue, BackendCommon.falseTag, evaluateMkBool] at run
          cases b with
          | false => exact Or.inl ⟨rfl, rfl⟩
          | true => simp [BackendCommon.trueTag] at run
        | true =>
          simp [asBool, boolValue, BackendCommon.trueTag] at run
          exact Or.inr ⟨rfl, run⟩

/-- Boolean-parametric conjunction append proof infrastructure. -/
private theorem conjunctionAppend {C F : Type} (xs ys : List ClosLang.Exp)
    (env : List Value) (s : State C F) (b : Bool)
    (h : evaluate [conjList xs] env s = (.val [boolValue b], s) ∧
      ∀ x ∈ xs, ClosLang.pure x = true) :
    evaluate [conjList (xs ++ ys)] env s =
      if b then evaluate [conjList ys] env s else (.val [boolValue false], s) := by
  induction xs generalizing b with
  | nil =>
    cases b with
    | false =>
      have trueRun := evaluateMkBool true env s
      simp only [conjList] at h
      rw [trueRun] at h
      simp [boolValue, BackendCommon.trueTag, BackendCommon.falseTag] at h
    | true => rfl
  | cons x xs ih =>
    rcases h with ⟨run, pure⟩
    cases xs with
    | nil =>
      cases b with
      | false =>
        exact evaluateConjListFalse x ys env s (by simpa [conjList] using run)
      | true =>
        exact evaluateConjListTrue x ys env s _ ⟨by simpa [conjList] using run, rfl⟩
    | cons y rest =>
      have headPure := pure x (by simp)
      have tailPure : ∀ z ∈ y :: rest, ClosLang.pure z = true :=
        fun z hz => pure z (by simp [hz])
      rcases conjunctionHead x y rest env s b headPure run with ⟨head, rfl⟩ | ⟨head, tail⟩
      · exact evaluateConjListFalse x ((y :: rest) ++ ys) env s head
      · have tailAppend := ih b ⟨tail, tailPure⟩
        exact evaluateConjListTrue x ((y :: rest) ++ ys) env s _ ⟨head, tailAppend⟩

/-- A false pure prefix short-circuits an appended conjunction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_ConjList_append_F"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateConjListAppendFalse {C F : Type} (xs ys : List ClosLang.Exp)
    (env : List Value) (s : State C F)
    (h : evaluate [conjList xs] env s = (.val [boolValue false], s) ∧
      ∀ x ∈ xs, ClosLang.pure x = true) :
    evaluate [conjList (xs ++ ys)] env s = (.val [boolValue false], s) :=
  conjunctionAppend xs ys env s false h

/-- A true pure prefix continues with the appended conjunction. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_ConjList_append_T"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateConjListAppendTrue {C F : Type} (xs ys : List ClosLang.Exp)
    (env : List Value) (s : State C F)
    (h : evaluate [conjList xs] env s = (.val [boolValue true], s) ∧
      ∀ x ∈ xs, ClosLang.pure x = true) :
    evaluate [conjList (xs ++ ys)] env s = evaluate [conjList ys] env s :=
  conjunctionAppend xs ys env s true h

end Flapjack.Compiler.Backend.ClosOp
