import Flapjack.Pancake.Semantics.PanSem.Semantics

/-! Shared observation-witness reduction for the Pan semantics: a terminating
behaviour of a run pair is witnessed by its result and post-state, and
conversely. Flapjack proof infrastructure; no separately named HOL original. -/
namespace Flapjack

/-- A `terminate` behaviour is witnessed by the run's result and post-state
exactly when it is witnessed by the result and the post-state's IO events. -/
theorem terminationWitnessReduced {width : Nat} {σ : Type} [NeZero width]
    (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (outcomeRelation : Option (PanSemResultExact width) → HolOutcome → Prop)
    (behaviour : HolBehaviour) :
    (∃ post result outcome, run = (result,post) ∧
      outcomeRelation result outcome ∧
      behaviour = HolBehaviour.terminate outcome post.ffi.ioEvents) ↔
    (∃ outcome, outcomeRelation run.1 outcome ∧
      behaviour = HolBehaviour.terminate outcome run.2.ffi.ioEvents) := by
  rcases run with ⟨result,post⟩
  constructor
  · rintro ⟨post',result',outcome,hpair,houtcome,hbehaviour⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hpair
    exact ⟨outcome,houtcome,hbehaviour⟩
  · rintro ⟨outcome,houtcome,hbehaviour⟩
    exact ⟨post,result,outcome,rfl,houtcome,hbehaviour⟩

end Flapjack
