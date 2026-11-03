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

end Flapjack.Compiler.Backend.ClosOp
