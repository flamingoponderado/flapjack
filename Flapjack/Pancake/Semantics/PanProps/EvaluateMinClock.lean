import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAssembly

namespace Flapjack

open Pancake.PanLang PanPropsEvalStateFiniteExact

namespace EvaluateMinClockWitness
/-- Canonical finite-state roundtrip support; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
      PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateMinClockWitness

/-- Exact source minimum-clock theorem: a non-timeout run admits an input
clock that preserves its result and every post-state component except clock,
which becomes zero. As in HOL822-830, apply evaluate_clock_sub to the
zero-clock post-state and subtract the original remaining clock. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_min_clock"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateMinClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (state : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanPropsEvalStateFiniteExact width σ) :
    evaluateHOLFinitePair state program = (result, post) ∧ result ≠ some .timeOut →
      ∃ clock, evaluateHOLFinitePair { state with clock := clock } program =
        (result, { post with clock := 0 }) := by
  intro ⟨hRun, hnt⟩
  refine ⟨state.clock - post.clock, ?_⟩
  have hRun' : evaluateHOLFinitePair state program =
      (result, { ({ post with clock := 0 } : PanPropsEvalStateFiniteExact width σ)
        with clock := 0 + post.clock }) := by
    simpa using hRun
  exact evaluateClockSubHOLFinite program state result { post with clock := 0 }
    post.clock hRun' hnt

end Flapjack
