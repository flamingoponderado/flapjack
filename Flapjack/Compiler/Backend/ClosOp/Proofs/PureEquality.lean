import Flapjack.Compiler.Backend.ClosOp.Proofs.DirectEvaluate
import Flapjack.Compiler.Backend.ClosOp.Proofs.PureEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.EqualitySym

/-! Semantic cases for the source pure-equality optimization. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem

namespace PureEqualityPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end PureEqualityPort

/-- Successful operand evaluation and source value equality evaluate the
ordinary equality operation. This is proof infrastructure. -/
private theorem evaluateEqual {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool)
    (run : evaluate [x, y] env s = (.val [vx, vy], s))
    (eq : doEq vx vy = .val b) :
    evaluate [.op .none (.blockOp .equal) [x, y]] env s = (.val [boolValue b], s) := by
  rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp), run]
  have reverseEq : doEq vy vx = .val b := by rw [ClosProps.doEqSym.1, eq]
  simp [doApp, applyBlock, reverseEq]

/-- Direct-recognizer case of pure-equality correctness. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmDirect {C F : Type} (x y z : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool) (direct : directEq x y = some z)
    (h : evaluate [x, y] env s = (.val [vx, vy], s) ∧ SimpleExp x ∧ SimpleExp y ∧
      doEq vx vy = .val b) :
    evaluate [eqPure x y] env s = (.val [boolValue b], s) := by
  have original := evaluateEqual x y vx vy env s b h.1 h.2.2.2
  have optimized := eqDirectThm x y env s (.val [boolValue b]) s .none z
    ⟨original, by simp, direct⟩
  have result : eqPure x y = z := by
    simp [eqPure, eqPureList, direct, Flapjack.appListAppend, Flapjack.appendAux, conjList]
  simpa [result] using optimized

/-- Fallback case of pure-equality correctness when neither operand is a
constructor and the direct recognizer does not match. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmFallback {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool) (direct : directEq x y = none)
    (noX : cons x = none) (noY : cons y = none)
    (h : evaluate [x, y] env s = (.val [vx, vy], s) ∧ SimpleExp x ∧ SimpleExp y ∧
      doEq vx vy = .val b) :
    evaluate [eqPure x y] env s = (.val [boolValue b], s) := by
  have result : eqPure x y = .op .none (.blockOp .equal) [x, y] := by
    unfold eqPure
    rw [eqPureList, direct]
    dsimp only
    split
    all_goals simp_all [Flapjack.appListAppend, Flapjack.appendAux, conjList]
  rw [result]
  exact evaluateEqual x y vx vy env s b h.1 h.2.2.2

/-- A successful pure pair evaluates each component in the original state.
This is proof infrastructure. -/
private theorem purePair {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F)
    (hx : SimpleExp x) (run : evaluate [x, y] env s = (.val [vx, vy], s)) :
    evaluate [x] env s = (.val [vx], s) ∧ evaluate [y] env s = (.val [vy], s) := by
  have headPure : pureList [x] = true := by simp [pureList, simpleExpPure x hx]
  cases headRun : evaluate [x] env s with
  | mk headResult headState =>
    cases headResult with
    | err err =>
      rw [ClosProps.evaluate_cons_error x [y] env s headState err headRun] at run
      cases run
    | val headValues =>
      obtain ⟨v, rfl⟩ := evaluate_singleton_value x env s headState headValues headRun
      obtain ⟨_, _, stateEq⟩ := ClosProps.evaluate_pure [x] env s headState (.val [v])
        headPure headRun (by simp)
      subst headState
      rw [ClosProps.evaluate_cons_value x [y] env s s v headRun] at run
      cases tailRun : evaluate [y] env s with
      | mk tailResult tailState =>
        cases tailResult with
        | err err => simp [tailRun] at run
        | val tailValues =>
          obtain ⟨v', rfl⟩ := evaluate_singleton_value y env s tailState tailValues tailRun
          simp only [tailRun, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
            List.cons.injEq] at run
          rcases run with ⟨⟨rfl, rfl, _⟩, rfl⟩
          exact ⟨rfl, rfl⟩

/-- Successful evaluation of a constructor exposes the values and length
of its argument list. This is proof infrastructure. -/
private theorem pureConstructor {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (args : List ClosLang.Exp) (env : List Value) (s : State C F) (v : Value)
    (run : evaluate [.op trace (.blockOp (.cons tag)) args] env s = (.val [v], s)) :
    ∃ values, evaluate args env s = (.val values, s) ∧
      v = .block tag values.reverse ∧ values.length = args.length := by
  rw [evaluateConstructor] at run
  cases argsRun : evaluate args env s with
  | mk result next =>
    cases result with
    | err err => simp [argsRun] at run
    | val values =>
      simp only [argsRun, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
        List.cons.injEq] at run
      rcases run with ⟨⟨rfl, _⟩, rfl⟩
      exact ⟨values, rfl, rfl, evaluate_length.1 args env _ _ values argsRun⟩

/-- Constructor mismatch case of the source pure-equality theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmConstructorMismatch {C F : Type} (tx ty : BackendCommon.Tra)
    (tagX tagY : Nat) (xs ys : List ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool)
    (direct : directEq (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys) = none)
    (different : (tagX != tagY || xs.length != ys.length) = true)
    (h : evaluate [.op tx (.blockOp (.cons tagX)) xs, .op ty (.blockOp (.cons tagY)) ys] env s =
        (.val [vx, vy], s) ∧
      SimpleExp (.op tx (.blockOp (.cons tagX)) xs) ∧
      SimpleExp (.op ty (.blockOp (.cons tagY)) ys) ∧ doEq vx vy = .val b) :
    evaluate [eqPure (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys)] env s = (.val [boolValue b], s) := by
  obtain ⟨runX, runY⟩ := purePair _ _ vx vy env s h.2.1 h.1
  obtain ⟨valuesX, _, rfl, lenX⟩ := pureConstructor tx tagX xs env s vx runX
  obtain ⟨valuesY, _, rfl, lenY⟩ := pureConstructor ty tagY ys env s vy runY
  have mismatch : ¬(tagX = tagY ∧ valuesX.reverse.length = valuesY.reverse.length) := by
    simp only [Bool.or_eq_true, bne_iff_ne] at different
    simp only [List.length_reverse, lenX, lenY]
    rcases different with hd | hl
    · exact fun h => hd h.1
    · exact fun h => hl h.2
  have bFalse : b = false := by
    have eq := h.2.2.2
    rw [doEq, if_neg mismatch] at eq
    cases eq
    rfl
  subst b
  have result : eqPure (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys) = mkBool false := by
    unfold eqPure
    rw [eqPureList, direct]
    simp [cons, destOp, destCons, different, Flapjack.appListAppend, Flapjack.appendAux, conjList]
  rw [result, mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag]

end Flapjack.Compiler.Backend.ClosOp
