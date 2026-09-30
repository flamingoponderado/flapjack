import Flapjack.Pancake.Semantics.PanSem.ClockTimeout

/-! Exact counterpart of panPropsScript.sml:881 evaluate_add_clock_io_events_mono. -/

namespace Flapjack

open PanSemStateFiniteExact

namespace PanPropsAddClockEventsSupport

/-- Canonical finite-support roundtrip for the four state map fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanPropsAddClockEventsSupport

/-- Exact HOL clock-increase event monotonicity. The program, state and extra
    clock are universally quantified in HOL order, with no premises. Both
    runs use the finite evaluator whose 21 constructor equations were reviewed
    against the rebound `panSem$evaluate_def` at line 780. The finite-to-broad
    proof supplies domain deciders internally and proves the assembly markers
    total; neither becomes an assumption or a branch in this statement. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_add_clock_io_events_mono"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem panPropsEvaluateAddClockIoEventsMono {width : Nat} {σ : Type} [NeZero width] :
    ∀ (exps : Pancake.PanLang.ProgHOL width) (s : PanSemStateFiniteExact width σ) (extra : Nat),
      (evaluateHOLFiniteState s exps).2.ffi.ioEvents <+:
        (evaluateHOLFiniteState { s with clock := s.clock + extra } exps).2.ffi.ioEvents := by
  intro exps s extra
  exact evaluateHOLFiniteState_add_clock_ioEvents_prefix s exps extra

end Flapjack
