import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.CrepSem.HOLState

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

end Flapjack
