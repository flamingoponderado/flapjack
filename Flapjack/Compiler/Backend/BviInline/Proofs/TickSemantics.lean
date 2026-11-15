module

public import Flapjack.Compiler.Backend.BviInline.Proofs.ExpRelation

@[expose] public section

/-! Clock behavior of ticks inserted by the BVI inliner. -/
namespace Flapjack.Compiler.Backend.BviInline

namespace TickSemanticsCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end TickSemanticsCarrier

/-- Evaluating inserted ticks either exhausts the clock or evaluates the body
after the corresponding decrement. The evaluator inherits the real-model
assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_bvi_mk_tick"
  (fmap_as_finite_support := [refs])]
theorem evaluate_mkTick {C F : Type} (expression : Bvi.Exp) (env : List BvlSem.Value)
    (state : BviSem.BviState C F) (n : Nat) :
    BviSem.evaluate [mkTick n expression] env state =
      if state.clock < n then (.err (.abort .timeoutError), { state with clock := 0 })
      else BviSem.evaluate [expression] env (BviSem.decClock n state) := by
  induction n generalizing state with
  | zero => simp [mkTick, BviSem.decClock]
  | succ n ih =>
    rw [mkTick, BviSem.evaluate]
    by_cases zero : state.clock = 0
    · have same : { state with clock := 0 } = state := by cases state; simp_all
      simp [zero, same]
    · simp only [zero, ↓reduceIte]
      rw [ih]
      have small : (BviSem.decClock 1 state).clock < n ↔ state.clock < n + 1 := by
        simp [BviSem.decClock]
        omega
      by_cases under : state.clock < n + 1
      · have under' : (BviSem.decClock 1 state).clock < n := small.mpr under
        have under'' : state.clock - 1 < n := by simpa [BviSem.decClock] using under'
        simp [under, under'', BviSem.decClock]
      · have under' : ¬(BviSem.decClock 1 state).clock < n := fun h => under (small.mp h)
        have dec : BviSem.decClock n (BviSem.decClock 1 state) = BviSem.decClock (n + 1) state := by
          simp [BviSem.decClock, Nat.sub_sub, Nat.add_comm]
        simp [under, under', dec]

end Flapjack.Compiler.Backend.BviInline
