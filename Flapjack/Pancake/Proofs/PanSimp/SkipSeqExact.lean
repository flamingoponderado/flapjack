import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace PanSimpSkipSeqSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end PanSimpSkipSeqSupport

/-- Prefixing Skip leaves the complete result and state unchanged. HOL uses
its unconditional evaluate_def equation. The finite-state Seq equation preserves
fix_clock behavior through its proved clock rewrite; no extra premise is needed. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_skip_seq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSkipSeqHOL {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.seq .skip program) =
      evaluateHOLFiniteState state program := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]

end Flapjack
