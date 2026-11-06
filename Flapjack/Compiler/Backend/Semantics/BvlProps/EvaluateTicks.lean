import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Evaluation of repeated BVL ticks. -/
namespace Flapjack.Compiler.Backend.BvlProps
open BvlSem Flapjack.SemanticPrimitivesHOL

namespace TickCarrier
/-- The canonical BVL reference-map state representation roundtrips. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end TickCarrier

/-- Repeated ticks either exhaust the clock or evaluate the body after
subtracting the exact tick count. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_mk_tick"
  (fmap_as_finite_support := [refs])]
theorem evaluateMkTick {C F : Type} (expression : Bvl.Exp) (env : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (n : Nat) :
    evaluateTuple ([Bvl.mkTick n expression], env, state) =
      if state.clock < n then (.err (.abort .timeoutError), { state with clock := 0 })
      else evaluateTuple ([expression], env, decClock n state) := by
  induction n generalizing state with
  | zero => simp [Bvl.mkTick, decClock]
  | succ n ih =>
    by_cases zero : state.clock = 0
    · simp [Bvl.mkTick, evaluateTuple, evaluate, zero]
      cases state
      simp_all
    · have less : state.clock - 1 < n ↔ state.clock < n + 1 := by omega
      have less' : (decClock 1 state).clock < n ↔ state.clock < n + 1 := by
        simpa [decClock] using less
      have dec : decClock n (decClock 1 state) = decClock (n + 1) state := by
        simp only [decClock]
        congr 1
        omega
      have exhausted : { decClock 1 state with clock := 0 } = { state with clock := 0 } := by
        simp [decClock]
      simp only [Bvl.mkTick, evaluateTuple, evaluate, zero, if_false]
      change evaluateTuple ([Bvl.mkTick n expression], env, decClock 1 state) = _
      rw [ih]
      simp only [less', dec, exhausted, evaluateTuple]

end Flapjack.Compiler.Backend.BvlProps
