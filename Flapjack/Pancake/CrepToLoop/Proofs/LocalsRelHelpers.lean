import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# crep_to_loop `locals_rel` lookup/insert helpers over the exact carriers

Exact ports of the `[local]` theorems `locals_rel_lookup_same` (3313) and
`locals_rel_inter_helper` (3322) of
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` over the exact
`crepToLoopLocalsRelExact` (bead `flapjack-pxn.18.5.6.33.13`).
-/

namespace Flapjack

namespace CrepToLoopLocalsRelHelpersWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the
    `fmap_as_finite_support_relation` qualifier on the helpers below. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopLocalsRelHelpersWitnesses

/-- Exact HOL `locals_rel_lookup_same` (`crep_to_loopProofScript.sml:3313-3320`):
    `locals_rel ctxt l locs1 locs2 ==> (!n. lookup n locs2 = lookup n locs3) ==>
      locals_rel ctxt l locs1 locs3`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_lookup_same"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars, locs1])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopLocalsRelExact_lookup_same {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (l : NumSet)
    (locs1 : HolFiniteMapExact Nat (HolWordLab width))
    (locs2 locs3 : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l locs1 locs2)
    (hs : ∀ n, sptLookup n locs2 = sptLookup n locs3) :
    crepToLoopLocalsRelExact ctxt l locs1 locs3 := by
  obtain ⟨hd, hm, hdom, hv⟩ := h
  refine ⟨hd, hm, fun n hn => ?_, fun vname value hl => ?_⟩
  · have := hdom n hn
    simp only [sptMem, sptDomain] at this ⊢
    rw [← hs n]; exact this
  · obtain ⟨n, h1, h2, h3⟩ := hv vname value hl
    exact ⟨n, h1, h2, by rw [← hs n]; exact h3⟩

/-- Exact HOL `locals_rel_inter_helper` (`crep_to_loopProofScript.sml:3322-3343`):
    `locals_rel ctxt l locs1 locs2 ==> EVERY (\i. lookup i l = NONE) xs ==>
      LENGTH xs = LENGTH ys ==>
      locals_rel ctxt l locs1 (inter (alist_insert xs ys locs2) l)`.
    HOL `EVERY P xs` is rendered as `∀ i ∈ xs, P i`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_inter_helper"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars, locs1])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopLocalsRelExact_inter_helper {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (l : NumSet)
    (locs1 : HolFiniteMapExact Nat (HolWordLab width))
    (locs2 : Spt (WordLocW width)) (xs : List Nat) (ys : List (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l locs1 locs2)
    (hxs : ∀ i ∈ xs, sptLookup i l = none)
    (_hlen : xs.length = ys.length) :
    crepToLoopLocalsRelExact ctxt l locs1
      (sptInter (LoopSemStateFiniteExact.sptAlistInsert xs ys locs2) l) := by
  have key : ∀ n, sptMem n l →
      sptLookup n (sptInter (LoopSemStateFiniteExact.sptAlistInsert xs ys locs2) l) =
        sptLookup n locs2 := by
    intro n hn
    have hn' : (sptLookup n l).isSome := hn
    have hnx : n ∉ xs := fun hm => by rw [hxs n hm] at hn'; simp at hn'
    rw [sptLookup_sptInter, if_pos hn']
    exact LoopSemStateFiniteExact.sptLookup_sptAlistInsert_not_mem n xs ys locs2 hnx
  obtain ⟨hd, hm, hdom, hv⟩ := h
  refine ⟨hd, hm, fun n hn => ?_, fun vname value hl => ?_⟩
  · have := hdom n hn
    simp only [sptMem, sptDomain] at this ⊢
    rw [key n hn]; exact this
  · obtain ⟨n, h1, h2, h3⟩ := hv vname value hl
    exact ⟨n, h1, h2, by rw [key n h2]; exact h3⟩

end Flapjack
