module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateCodeGrowth
@[expose] public section

/-! Code growth across a complete closure application. -/
namespace Flapjack.Compiler.Backend.ClosCall.ApplicationGrowth
open Flapjack ClosSem

/-- The closure state has the canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
/-- A closure application preserves all pre-existing code entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "evaluate_app_mono"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_mono {C F : Type} (x : Option Nat) (y : Value) (z : List Value)
    (s1 : ClosSem.State C F) (vs : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (s2 : ClosSem.State C F) (h : evaluateApp x y z s1 = (vs, s2)) :
    s1.code.submap s2.code :=
  evaluate_code_growth.2 (s1.clock + 1) x y z s1 s2 vs (Nat.lt_succ_self _) h
end Flapjack.Compiler.Backend.ClosCall.ApplicationGrowth
