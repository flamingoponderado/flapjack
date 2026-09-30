import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanGlobalsUnchangedLocalAssignPrimitive
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export; no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Assign case of the original unchanged-local theorem; no IH or extra premise.
    Local-name inequality follows from freshness; global writes preserve locals. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Assign {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (kind : VarKind) (bound : MlS)
    (expression : ExpHOL width) (state : PanSemStateFiniteExact width σ) :
    ∀ result (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.assign kind bound expression) ∧
      evaluateHOLFiniteState state (.assign kind bound expression) = (result,post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hf,he,hgood,herror⟩
  rw [evaluateHOLFiniteState_assign] at he
  split at he
  · exact False.elim (herror (Prod.mk.inj he).1.symm)
  · split at he
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      cases kind with
      | «local» =>
        have hn : name ≠ bound := by intro h; subst name; apply hf; simp [freeVarIdsHOL]
        simp [setKvarHOLFinite,setVarHOLFinite,FUPDATE,Ne.symm hn]
      | global => rfl
    · exact False.elim (herror (Prod.mk.inj he).1.symm)

/-- Primitive case of the original unchanged-local theorem. Freshness supplies
    the unequal destination name; failures are excluded by original nonError. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_Primitive {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (bound : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ) :
    ∀ result (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.primitive bound operator arguments) ∧
      evaluateHOLFiniteState state (.primitive bound operator arguments) = (result,post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hf,he,hgood,herror⟩
  have hn : name ≠ bound := by intro h; subst name; apply hf; simp [freeVarIdsHOL]
  rw [evaluateHOLFiniteState_primitive] at he
  split at he
  · exact False.elim (herror (Prod.mk.inj he).1.symm)
  · split at he
    · exact False.elim (herror (Prod.mk.inj he).1.symm)
    · split at he
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        simp [setVarHOLFinite,FUPDATE,Ne.symm hn]
      · exact False.elim (herror (Prod.mk.inj he).1.symm)

end Flapjack.PanGlobalsUnchangedLocalAssignPrimitive
