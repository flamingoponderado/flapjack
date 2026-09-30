import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalTailCall
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original tail Call NONE case of evaluate_unchanged_local. The total
source tail-call clauses admit no good nonerror result. This specializes
HOL's Call conjunct to caltyp = NONE and omits the unused callee-body IH;
it is therefore a stronger specialized case lemma, not the literal full Call
conjunct. The original public evaluation/good-result premises are retained. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_CallNone {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (function : MlS)
    (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.call none function arguments) ∧
      evaluateHOLFiniteState state (.call none function arguments) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_call] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals simp_all [goodResHOL]
  all_goals cases ‹PanSemResultExact width› <;> simp_all

end Flapjack.PanGlobalsUnchangedLocalTailCall
