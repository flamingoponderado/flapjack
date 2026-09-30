import Flapjack.Pancake.Proofs.PanGlobals.CallObservation
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsCongruence

namespace Flapjack.PanGlobalsSemanticsEmptyLocals

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-support state roundtrip for the four translated HOL
finite-map fields in the theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- HOL `semantics_empty_locals` (`pan_globalsProofScript.sml:2862-2889`).
For every source state and entry name, clearing locals leaves the complete
observational semantics unchanged. There are no logical premises.

Source review: the entry is `Call NONE start []`; code lookup and timeout
do not inspect caller locals, and successful calls replace them with callee
locals before body evaluation. Both states have identical clocked results
and FFI events, with the original `fix_clock` behavior retained. The failure
existential, full termination-choice predicate and divergence prefix set are
therefore equal. Only HOL's four finite-map state fields and positive word
dimension use the named representation translations; `start` uses faithful
`MlS`, and the tagged source `semantics` definition is used directly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_empty_locals"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsEmptyLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS) :
    semantics state start = semantics (emptyLocalsHOLFinite state) start := by
  apply Flapjack.panGlobals_semantics_of_clock_observations
  intro clock
  simpa only [emptyLocalsHOLFinite] using
    Flapjack.panGlobals_call_emptyLocals_observation { state with clock := clock } start

end Flapjack.PanGlobalsSemanticsEmptyLocals
