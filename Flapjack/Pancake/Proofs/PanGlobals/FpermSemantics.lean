import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Prime
import Flapjack.Pancake.Semantics.PanSem.Semantics

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermSemanticsSupport
/-- Imported canonical state roundtrips; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Flapjack predicate normalization: eliminate evaluator pair aliases from
HOL's classical termination-choice predicate. No independent HOL declaration. -/
private theorem terminationWitnessReduced {width : Nat} {σ : Type} [NeZero width]
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
end FpermSemanticsSupport

/-- Original semantics_fperm: swapping function names in the complete code map
and entry name preserves the entire faithful HOL behaviour, including Fail.
The clock-update evaluation theorem proves equal results and FFI event lists
at every clock, so failure, classical termination choice and divergence LUB
predicates coincide. There is no non-Fail, successful-run or trace premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsFpermHOL {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ) (start : MlS) :
    semantics { state with code := fpermCodeHOL f g state.code } (fpermName f g start) =
      semantics state start := by
  classical
  have runs (clock : Nat) :
      evaluateHOLFiniteState
          { state with code := fpermCodeHOL f g state.code, clock := clock }
          (.call none (fpermName f g start) []) =
        (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
          (outcome.1, { outcome.2 with code := fpermCodeHOL f g outcome.2.code }))
          (evaluateHOLFiniteState { state with clock := clock } (.call none start [])) := by
    simpa [fpermHOL] using evaluateFpermPrimeHOL f g (.call none start []) state clock
  have results (clock : Nat) :
      (evaluateHOLFiniteState
        { state with code := fpermCodeHOL f g state.code, clock := clock }
        (.call none (fpermName f g start) [])).1 =
      (evaluateHOLFiniteState { state with clock := clock } (.call none start [])).1 := by
    have h := congrArg (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
      outcome.1) (runs clock)
    exact h
  have events (clock : Nat) :
      (evaluateHOLFiniteState
        { state with code := fpermCodeHOL f g state.code, clock := clock }
        (.call none (fpermName f g start) [])).2.ffi.ioEvents =
      (evaluateHOLFiniteState { state with clock := clock } (.call none start [])).2.ffi.ioEvents := by
    have h := congrArg (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
      outcome.2.ffi.ioEvents) (runs clock)
    exact h
  unfold semantics
  dsimp only
  simp only [FpermSemanticsSupport.terminationWitnessReduced, results, events]

end Flapjack
