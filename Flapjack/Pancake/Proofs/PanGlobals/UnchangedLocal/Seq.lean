import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalSeq
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Seq case of HOL evaluate_unchanged_local1107-1137. The two IHs
are the literal evaluate_ind Seq conjunction: second-child P at a first-child
NONE output, and first-child P. Each P is expanded to the original theorem
predicate. The unused value binder is retained. The line780 Seq equation
already derives removal of fix_clock using the reviewed fix_clock_evaluate;
no clock-bound premise is introduced here. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Seq {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (first second : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ih :
      (∀ (firstResult : Option (PanSemResultExact width)) (middle : PanSemStateFiniteExact width σ),
        (firstResult, middle) = evaluateHOLFiniteState state first ∧ firstResult = none →
        ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
          name ∉ freeVarIdsHOL second ∧ evaluateHOLFiniteState middle second = (result, post) ∧
          goodResHOL result = true ∧ result ≠ some .error →
          post.locals.lookup name = middle.locals.lookup name) ∧
      (∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL first ∧ evaluateHOLFiniteState state first = (result, post) ∧
        goodResHOL result = true ∧ result ≠ some .error →
        post.locals.lookup name = state.locals.lookup name)) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.seq first second) ∧
      evaluateHOLFiniteState state (.seq first second) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  intro result post ⟨hfresh, heval, hgood, herror⟩
  have hf : name ∉ freeVarIdsHOL first ∧ name ∉ freeVarIdsHOL second := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using hfresh
  rw [evaluateHOLFiniteState_seq_line780] at heval
  have hex : ∃ firstResult middle,
      evaluateHOLFiniteState state first = (firstResult, middle) :=
    ⟨_, _, rfl⟩
  obtain ⟨firstResult, middle, hfirst⟩ := hex
  cases firstResult with
  | none =>
      simp only [hfirst] at heval
      have hmiddle := ih.2 none middle ⟨hf.1, hfirst, rfl, by simp⟩
      exact (ih.1 none middle ⟨hfirst.symm, rfl⟩ result post
        ⟨hf.2, heval, hgood, herror⟩).trans hmiddle
  | some firstResult =>
      simp only [hfirst] at heval
      exact ih.2 result post ⟨hf.1, hfirst.trans heval, hgood, herror⟩

end Flapjack.PanGlobalsUnchangedLocalSeq
