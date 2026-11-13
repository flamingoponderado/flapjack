module

public import Flapjack.Pancake.Semantics.PanProps
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-!
# `FLOOKUP_pan_res_var_thm` over the exact finite map

Exact port of HOL `panProps$FLOOKUP_pan_res_var_thm`
(`cakeml/pancake/semantics/panPropsScript.sml:236-242`), used by the
`pc_compile_correct` DecCall case (bead `flapjack-pxn.18.4.3.95.2`).
-/

namespace Flapjack

/-- Exact port of HOL `panProps$FLOOKUP_pan_res_var_thm`
    (`panPropsScript.sml:236-242`):
    `FLOOKUP (panSem$res_var l (m,v)) n = if n = m then v else FLOOKUP l n`.
    HOL `panSem$res_var_def` (`panSemScript.sml:505-508`) has the same two clauses
    as the tagged generic `HolFiniteMapExact.resVarEq`, which the exact Pan
    evaluator uses for its `Dec`/`DecCall` restoration, and `FLOOKUP` is
    `.lookup`. HOL's free variables `l m v n` are the explicit binders. The
    standalone map `l` is recorded as a bare relation-qualifier entry. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FLOOKUP_pan_res_var_thm"
  (fmap_as_finite_support_relation := [l])]
theorem flookupPanResVarThmHOL {α β : Type} [DecidableEq α] :
    ∀ (l : HolFiniteMapExact α β) (m : α) (v : Option β) (n : α),
      (HolFiniteMapExact.resVarEq l (m, v)).lookup n =
        if n = m then v else l.lookup n := by
  intro l m v n
  cases v <;> by_cases h : n = m <;>
    simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
      HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL, h]

/-- Exact port of HOL `panProps$flookup_res_var_diff_eq_org`
    (`panPropsScript.sml:228-230`): `n <> m ==>
    FLOOKUP (res_var lc (n,v)) m = FLOOKUP lc m`.  HOL's free variables are the
    explicit binders; `res_var` is the tagged `HolFiniteMapExact.resVarEq`
    (`panSem$res_var_def`) and `FLOOKUP` is `.lookup`.  The standalone map `lc`
    is recorded as a bare relation-qualifier entry. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "flookup_res_var_diff_eq_org"
  (fmap_as_finite_support_relation := [lc])]
theorem flookupResVarDiffEqOrgHOL {α β : Type} [DecidableEq α] :
    ∀ (lc : HolFiniteMapExact α β) (n m : α) (v : Option β), n ≠ m →
      (HolFiniteMapExact.resVarEq lc (n, v)).lookup m = lc.lookup m := by
  intro lc n m v h
  have h' : m ≠ n := fun hm => h hm.symm
  cases v <;>
    simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
      HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL, h']

/-- Exact port of HOL `panProps$flookup_res_var_some_eq_lookup`
    (`panPropsScript.sml:220-222`): `FLOOKUP (res_var lc (v,FLOOKUP lc' v)) v =
    SOME value ==> FLOOKUP lc' v = SOME value`.  Both maps are the tagged
    `HolFiniteMapExact` carrier and both are recorded as bare relation-qualifier
    entries. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "flookup_res_var_some_eq_lookup"
  (fmap_as_finite_support_relation := [lc, lc'])]
theorem flookupResVarSomeEqLookupHOL {α β : Type} [DecidableEq α] :
    ∀ (lc : HolFiniteMapExact α β) (lc' : HolFiniteMapExact α β)
      (v : α) (value : β),
      (HolFiniteMapExact.resVarEq lc (v, lc'.lookup v)).lookup v = some value →
      lc'.lookup v = some value := by
  intro lc lc' v value h
  cases hv : lc'.lookup v with
  | none =>
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
        FDOMSUB_HOL, hv] at h
  | some w =>
      have hw : some w = some value := by
        simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, hv] using h
      exact hw

end Flapjack
