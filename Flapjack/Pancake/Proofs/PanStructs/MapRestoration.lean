import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace Flapjack.Pancake.Proofs.PanStructs.MapRestoration
open Flapjack
/-- Full original restoration/map2 commutation, with HOL equality internally
rendered by classical key equality and no public comparison premise. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "res_var_FMAP_MAP2_rev"
  (fmap_as_finite_support_relation := [fmap])]
theorem resVarFmapMap2Rev {α β γ : Type} (fmap : HolFiniteMapExact α β)
    (f : α × β → γ) (nm : α) (x : Option β) :
    (@HolFiniteMapExact.resVarEq α β (Classical.typeDecidableEq α) fmap (nm,x)).map2 f =
    @HolFiniteMapExact.resVarEq α γ (Classical.typeDecidableEq α)
      (fmap.map2 f) (nm,x.map (fun y => f (nm,y))) := by
  classical
  apply HolFiniteMapExact.ext
  funext key
  cases x with
  | none =>
    simp only [HolFiniteMapExact.map2, HolFiniteMapExact.resVarEq,
      HolFiniteMapExact.eraseEq, FDOMSUB_HOL, Option.map_none]
    by_cases hk : key=nm <;> simp [hk]
  | some value =>
    simp only [HolFiniteMapExact.map2, HolFiniteMapExact.resVarEq,
      HolFiniteMapExact.updateEq, FUPDATE_HOL, Option.map_some]
    by_cases hk : key=nm
    · subst key
      simp
    · simp [hk]

/-- The complement-singleton restriction is HOL DOMSUB at lookup level.
This spelling renders DRESTRICT fmap (COMPL {k}) with the exact unconditional
lookup `if query = k then NONE else FLOOKUP fmap query`; it introduces no
carrier or transition difference. -/
noncomputable def restrictExcept {α β : Type} (fmap : HolFiniteMapExact α β)
    (k : α) : HolFiniteMapExact α β :=
  @HolFiniteMapExact.eraseEq α β (Classical.typeDecidableEq α) fmap k

/-- Lookup witness for the literal HOL complement-singleton restriction.
Flapjack representation plumbing for the external finite_map operation. -/
theorem restrictExceptLookup {α β : Type} (fmap : HolFiniteMapExact α β)
    (k query : α) : (restrictExcept fmap k).lookup query =
      @ite (Option β) (query = k) (Classical.propDecidable (query = k))
        none (fmap.lookup query) := by
  classical
  rfl

/-- Exact original FEVERY restoration equivalence, retaining both the restricted
map predicate and the optional restored-binding predicate. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "FEVERY_res_var"
  (fmap_as_finite_support_relation := [fmap])]
theorem feveryResVar {α β : Type} (fmap : HolFiniteMapExact α β)
    (P : α × β → Bool) (k : α) (opt_v : Option β) :
    feveryHOL P (@HolFiniteMapExact.resVarEq α β (Classical.typeDecidableEq α)
      fmap (k,opt_v)) ↔
    feveryHOL P (restrictExcept fmap k) ∧
      (∀ v, opt_v = some v → P (k,v) = true) := by
  classical
  cases opt_v with
  | none =>
    simp only [HolFiniteMapExact.resVarEq, restrictExcept]
    simp
  | some value =>
    constructor
    · intro h
      constructor
      · intro key val he
        rw [restrictExceptLookup] at he
        by_cases hk : key=k
        · simp [hk] at he
        · apply h key val
          simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
          simpa [hk] using he
      · intro v he
        cases he
        apply h k value
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · rintro ⟨h, hv⟩ key val he
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL] at he
      by_cases hk : key=k
      · subst key
        simp only [ite_true, Option.some.injEq] at he
        subst val
        exact hv value rfl
      · apply h key val
        rw [restrictExceptLookup]
        simpa [hk] using he
end Flapjack.Pancake.Proofs.PanStructs.MapRestoration
