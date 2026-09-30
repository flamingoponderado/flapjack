import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalExtCall
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original ExtCall leaf of evaluate_unchanged_local. The returning FFI
branch preserves locals; final events fail original good_res. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_ExtCall {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL
        (.extCall function configuration configurationLength array arrayLength) ∧
      evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_extCall_source] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

end Flapjack.PanGlobalsUnchangedLocalExtCall
