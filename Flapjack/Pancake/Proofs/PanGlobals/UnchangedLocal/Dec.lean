import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanGlobalsUnchangedLocalDec
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export; no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Dec case of HOL evaluate_unchanged_local1107-1137. The sole IH
is the initializer-value/shape-gated body predicate from evaluate_ind. The
original unused value binder is retained. Bound-name restoration is derived
from res_var; distinct-name body freshness is derived from free_var_ids's
filter, rather than assumed as an extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Dec {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (bound : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ih : ∀ value : ValueHOL width,
      @evalHOLExact width σ _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) initializer = some value ∧
        shape = shapeOfHOLExact value →
      ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL body ∧
        evaluateHOLFiniteState (setVarHOLFinite bound value state) body = (result, post) ∧
        goodResHOL result = true ∧ result ≠ some .error →
        post.locals.lookup name = (setVarHOLFinite bound value state).locals.lookup name) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.dec bound shape initializer body) ∧
      evaluateHOLFiniteState state (.dec bound shape initializer body) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hfresh, heval, hgood, herror⟩
  rw [evaluateHOLFiniteState_dec_total] at heval
  dsimp only at heval
  cases he : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) initializer with
  | none =>
      simp only [he] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)
  | some value =>
      by_cases hs : shape = shapeOfHOLExact value
      · have hshape : shapeEqHOL shape (shapeOfHOLExact value) = true :=
          (shapeEqHOL_eq_true _ _).mpr hs
        simp only [he, hshape, ↓reduceIte] at heval
        have hex : ∃ r st, evaluateHOLFiniteState (setVarHOLFinite bound value state) body =
            (r, st) := ⟨_, _, rfl⟩
        obtain ⟨r, st, hb⟩ := hex
        simp only [hb] at heval
        obtain ⟨hr, hp⟩ := Prod.mk.inj heval
        subst result
        subst post
        by_cases hn : name = bound
        · subst name
          rw [lookup_resVarEq_toExact]
          cases state.locals.lookup bound <;> simp [resVarHOLExact]
        · have hbody : name ∉ freeVarIdsHOL body := by
            intro hm
            apply hfresh
            simp [freeVarIdsHOL, List.mem_filter, hm, hn]
          have hi := ih value ⟨he, hs⟩ r st ⟨hbody, hb, hgood, herror⟩
          simp [setVarHOLFinite, FUPDATE, Ne.symm hn] at hi
          rw [lookup_resVarEq_toExact]
          cases hl : state.locals.lookup bound <;>
            simpa [resVarHOLExact, hn] using hi
      · have hshape : shapeEqHOL shape (shapeOfHOLExact value) = false := by
          cases hh : shapeEqHOL shape (shapeOfHOLExact value)
          · rfl
          · exact False.elim (hs ((shapeEqHOL_eq_true _ _).mp hh))
        simp only [he, hshape] at heval
        exact False.elim (herror (Prod.mk.inj heval).1.symm)

end Flapjack.PanGlobalsUnchangedLocalDec
