import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalLeaves
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original Skip leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Skip {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) 
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.skip : ProgHOL width) ∧
      evaluateHOLFiniteState state .skip = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_skip] at heval
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  rfl

/-- Original Break leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Break {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) 
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.break : ProgHOL width) ∧
      evaluateHOLFiniteState state .break = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_break] at heval
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  rfl

/-- Original Continue leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Continue {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) 
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.continue : ProgHOL width) ∧
      evaluateHOLFiniteState state .continue = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_continue] at heval
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  rfl

/-- Original Annot leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Annot {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (tag text : MlS)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL ((.annot tag text) : ProgHOL width) ∧
      evaluateHOLFiniteState state (.annot tag text) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_annot] at heval
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  rfl

/-- Original Tick leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Tick {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) 
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.tick : ProgHOL width) ∧
      evaluateHOLFiniteState state .tick = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_tick] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

/-- Original Store leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Store {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL ((.store destination source) : ProgHOL width) ∧
      evaluateHOLFiniteState state (.store destination source) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_store] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

/-- Original Store32 leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Store32 {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL ((.store32 destination source) : ProgHOL width) ∧
      evaluateHOLFiniteState state (.store32 destination source) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_store32] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

/-- Original StoreByte leaf of evaluate_unchanged_local, without added premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_StoreByte {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL ((.storeByte destination source) : ProgHOL width) ∧
      evaluateHOLFiniteState state (.storeByte destination source) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨_, heval, hgood, herror⟩ := h
  rw [evaluateHOLFiniteState_storeByte] at heval
  repeat' split at heval
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
  all_goals first | rfl | simp_all [goodResHOL]

end Flapjack.PanGlobalsUnchangedLocalLeaves
