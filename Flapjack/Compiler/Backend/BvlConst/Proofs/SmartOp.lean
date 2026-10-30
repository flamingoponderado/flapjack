import Flapjack.Compiler.Backend.BvlConst
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Correctness prerequisites for BVL constant operation rewrites. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem

namespace SmartOpCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SmartOpCarrier

/-- A recognized simple expression is exactly an argument-free integer
constant. This local theorem is tagged after the typed original proof replay. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "dest_simple_eq"]
theorem simple_eq (expression : Bvl.Exp) (n : Int) :
    simple expression = some n ↔ expression = .op (.intOp (.const n)) [] := by
  cases expression <;> try simp [simple]
  case op op args =>
    cases op <;> try simp
    case intOp operation =>
      cases operation <;> try simp
      case const value => cases args <;> simp

/-- The unary operation rewrite preserves the original evaluation whenever
that evaluation is not a type error. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp1_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp1_correct {C F : Type} (op : ClosLang.Op) (x : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op op [x]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp1 op x], env, state) = (result, final) := by
  cases op <;> try (simpa [smartOp1] using run)
  case blockOp operation =>
    cases operation <;> try (simpa [smartOp1] using run)
    case equalConst part =>
      cases part <;> try (simpa [smartOp1] using run)
      case int a =>
        cases hx : simple x with
        | none => simpa [smartOp1, hx] using run
        | some b =>
          have xeq := (simple_eq x b).1 hx
          subst x
          by_cases same : b = a
          · subst b
            simp [smartOp1, simple, BvlConst.bool, evaluateTuple, evaluate,
              fixClock, doApp, applyNumeric, doIntApp, applyBlock, boolValue,
              BackendCommon.boolToTag, BackendCommon.trueTag] at run ⊢
            exact run
          · have reverse : a ≠ b := Ne.symm same
            simp [smartOp1, simple, BvlConst.bool, evaluateTuple, evaluate,
              fixClock, doApp, applyNumeric, doIntApp, applyBlock, boolValue,
              BackendCommon.boolToTag, BackendCommon.falseTag,
              same, reverse] at run ⊢
            exact run

end Flapjack.Compiler.Backend.BvlConst.Proofs
