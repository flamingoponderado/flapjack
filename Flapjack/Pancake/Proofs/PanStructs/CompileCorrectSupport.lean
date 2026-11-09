module

public import Flapjack.Pancake.Proofs.PanStructs.FupdateElim2
public import Flapjack.Pancake.Proofs.PanStructs.MapRestoration
public import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
public import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
public import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
public import Flapjack.Pancake.PanStructs.CompileProgExact

@[expose] public section

/-!
# Shared finite-map helpers for the `pan_structs` `compile_correct` cases

The Assign, Call, Dec and DecCall case modules used verbatim private copies of
these lookup/update helpers. They are Flapjack-specific infrastructure over
the canonical finite-map carriers, with no HOL original.
-/

namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectSupport

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Lookup extensionality for proof plumbing; no independent HOL original. -/
theorem mapExt {α β : Type} (a b : HolFiniteMapExact α β)
    (h : ∀ k, a.lookup k = b.lookup k) : a = b := by
  cases a with | mk al af =>
    cases b with | mk bl bf =>
      have he : al = bl := funext h
      subst bl
      rfl

/-- Map/update commutation for proof plumbing; no independent HOL original. -/
theorem mapUpdate {α β γ : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (f : α × β → γ) (k : α) (v : β) :
    (fm.update (k,v)).map2 f = (fm.map2 f).update (k,f (k,v)) := by
  apply mapExt
  intro key
  simp only [HolFiniteMapExact.lookup_map2, HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hk : k == key
  · have he := beq_iff_eq.mp hk
    subst key
    simp
  · simp [hk]

/-- Existing-binding neutrality for the executed update; no independent HOL original. -/
theorem updateNeutral {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (k : α) (v : β) (h : fm.lookup k = some v) :
    fm.update (k,v) = fm := by
  classical
  have he : fm.update (k,v) = fm.updateEq (k,v) := by
    apply mapExt
    intro key
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL_eq_FUPDATE]
  rw [he]
  exact FupdateElim2.fupdateElim2 fm k v h

/-- Updated-map validity for proof plumbing; no independent HOL original. -/
theorem everyUpdate {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (P : α × β → Bool) (k : α) (v : β)
    (h : feveryHOL P fm) (hv : P (k,v) = true) : feveryHOL P (fm.update (k,v)) := by
  intro key value he
  simp only [HolFiniteMapExact.lookup_update, FUPDATE] at he
  split at he
  next hk =>
    have heq := beq_iff_eq.mp hk
    subst key
    cases he
    exact hv
  next => exact h key value he

/-- Local context bindings are overwritten by every code entry's own params.
Flapjack proof plumbing; no independent HOL declaration. -/
theorem convertStateLocalContext {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (locals : List (MlS × ShapeHOL))
    (state : PanSemStateFiniteExact width σ) :
    convertStateExact {context with locals := locals} state = convertStateExact context state := by
  rfl

/-- Equality decisions for the same key proposition are unique. Flapjack proof
plumbing; no extra comparison assumption and no independent HOL declaration. -/
theorem resVarCanonical {α β : Type} (d : DecidableEq α)
    (fm : HolFiniteMapExact α β) (entry : α × Option β) :
    @HolFiniteMapExact.resVarEq α β d fm entry =
    @HolFiniteMapExact.resVarEq α β (Classical.typeDecidableEq α) fm entry := by
  have h : d = Classical.typeDecidableEq α := Subsingleton.elim _ _
  subst d
  rfl

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectSupport
