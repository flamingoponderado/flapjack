import Flapjack.Pancake.Proofs.PanSimp.StateRel

namespace Flapjack.PanSimp

open Flapjack.Pancake.PanLang

/-- Flapjack-only canonical state codec witness. HOL has no declaration about
the finite-support carrier's Lean roundtrip. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- HOL's expression stability under the code-only state relation. Expression
evaluation never reads code; all other state fields agree. Classical domain
deciders implement HOL set membership without adding any logical premise.
The expression and value carriers retain HOL's constructor payloads. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_eval_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileEvalCorrect {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (e : ExpHOL width)
    (v : ValueHOL width) (t : PanSemStateFiniteExact width σ) :
    (@PanSemStateFiniteExact.evalHOLFinite width σ _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) e = some v ∧ stateRel s t t.code) →
    @PanSemStateFiniteExact.evalHOLFinite width σ _ t
      (fun address => Classical.propDecidable (t.memaddrs address)) e = some v := by
  intro ⟨heval, hrel⟩
  rw [hrel.1]
  simpa only [PanSemStateFiniteExact.evalHOLFinite_upd_code_eq] using heval

end Flapjack.PanSimp
