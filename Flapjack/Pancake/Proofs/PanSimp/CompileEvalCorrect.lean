module

public import Flapjack.Pancake.Proofs.PanSimp.StateRel

@[expose] public section

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

/-- HOL `pan_simpProof$OPT_MMAP_eval_some_eq` (`pan_simpProofScript.sml:518`):
a successful list evaluation under the source state carries over to the related
target state, because expression evaluation never reads code.  The typed
capture `OPT_MMAP_eval_some_eq_typed` (`pancake_pan_simp_proof_typed_probe.out`)
keeps HOL's conjunction as one premise and the relation argument at `t.code`. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "OPT_MMAP_eval_some_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalSomeEq {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (es : List (ExpHOL width))
    (vs : List (ValueHOL width)) (t : PanSemStateFiniteExact width σ) :
    (es.mapM (fun a => @PanSemStateFiniteExact.evalHOLFinite width σ _
        s (fun address => Classical.propDecidable (s.memaddrs address)) a) = some vs ∧
      stateRel s t t.code) →
    es.mapM (fun a => @PanSemStateFiniteExact.evalHOLFinite width σ _
        t (fun address => Classical.propDecidable (t.memaddrs address)) a) = some vs := by
  rintro ⟨hmap, hrel⟩
  obtain ⟨hlen, hpoint⟩ :=
    (list_mapM_eq_some_iff (fun a => @PanSemStateFiniteExact.evalHOLFinite width σ _
      s (fun address => Classical.propDecidable (s.memaddrs address)) a) es vs).mp hmap
  refine
    (list_mapM_eq_some_iff (fun a => @PanSemStateFiniteExact.evalHOLFinite width σ _
      t (fun address => Classical.propDecidable (t.memaddrs address)) a) es vs).mpr
      ⟨hlen, ?_⟩
  intro n hn
  have hfn := hpoint n hn
  cases hx : es[n]? with
  | none =>
      have hnone : vs[n]? = none := by simpa only [hx, Option.bind_none] using hfn.symm
      rw [List.getElem?_eq_none_iff] at hnone
      omega
  | some a =>
      simp only [hx, Option.bind_some] at hfn
      have hvs : vs[n]? = some vs[n] := List.getElem?_eq_getElem hn
      rw [hvs] at hfn
      rw [Option.bind_some, hvs]
      exact compileEvalCorrect s a vs[n] t ⟨hfn, hrel⟩

end Flapjack.PanSimp
