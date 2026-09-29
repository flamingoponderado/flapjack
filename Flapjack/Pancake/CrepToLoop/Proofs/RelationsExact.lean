import Flapjack.Pancake.CrepToLoop.StateRel

/-!
# crep_to_loop `wlab_wloc`, `mem_rel` and `globals_rel` over the exact carriers

Exact ports of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`wlab_wloc_def` (45), `mem_rel_def` (49), `globals_rel_def` (54),
`mem_rel_intro` (203) and `globals_rel_intro` (211) over the exact Crep/Loop
carriers `HolWordLab`/`WordLocW`, `CrepSemHOLState`/`LoopSemStateFiniteExact`
memories and `HolFiniteMapExact` globals (bead `flapjack-pxn.18.5.6.31.3`).  The
production-carrier renderings in `StateRel.lean` (`wlabWloc`,
`crepToLoopMemRel`, `crepToLoopGlobalsRel`) are over `PanWordLab`/`LoopValue`
and remain for the production bridge.  HOL's `'a word set` domain is the
predicate `BitVec width → Prop` used by the exact `crepSem$state.memaddrs`.
-/

namespace Flapjack

/-- Exact HOL `wlab_wloc_def` (`crep_to_loopProofScript.sml:45-47`):
    `wlab_wloc (panSem$Word w) = wordLang$Word w`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "wlab_wloc_def"
  (words_as_type_indexed_bitvec)]
def wlabWlocExact {width : Nat} [NeZero width] : HolWordLab width → WordLocW width
  | .word w => .word w

/-- Exact HOL `mem_rel_def` (`crep_to_loopProofScript.sml:49-52`):
    `mem_rel smem tmem dom <=> !ad. ad ∈ dom ⇒ wlab_wloc (smem ad) = tmem ad`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_def"
  (words_as_type_indexed_bitvec)]
def crepToLoopMemRelHOLExact {width : Nat} [NeZero width] (smem : BitVec width → HolWordLab width)
    (tmem : BitVec width → WordLocW width) (dom : BitVec width → Prop) : Prop :=
  ∀ ad, dom ad → wlabWlocExact (smem ad) = tmem ad

/-- Exact HOL `globals_rel_def` (`crep_to_loopProofScript.sml:54-58`):
    `globals_rel sglobals tglobals <=> !ad v. FLOOKUP sglobals ad = SOME v ==>
      FLOOKUP tglobals ad = SOME (wlab_wloc v)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_def"
  (fmap_as_finite_support_relation := [sglobals, tglobals]) (words_as_type_indexed_bitvec)]
def crepToLoopGlobalsRelHOLExact {width : Nat} [NeZero width] (sglobals : HolFiniteMapExact (BitVec 5) (HolWordLab width))
    (tglobals : HolFiniteMapExact (BitVec 5) (WordLocW width)) : Prop :=
  ∀ ad v, sglobals.lookup ad = some v → tglobals.lookup ad = some (wlabWlocExact v)

/-- Exact HOL `mem_rel_intro` (`crep_to_loopProofScript.sml:203-205`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_intro"
  (words_as_type_indexed_bitvec)]
theorem crepToLoopMemRelHOLExact_intro {width : Nat} [NeZero width] (smem : BitVec width → HolWordLab width)
    (tmem : BitVec width → WordLocW width) (dm : BitVec width → Prop) :
    crepToLoopMemRelHOLExact smem tmem dm →
      ∀ ad, dm ad → wlabWlocExact (smem ad) = tmem ad :=
  fun h => h

/-- Exact HOL `globals_rel_intro` (`crep_to_loopProofScript.sml:211-214`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_intro"
  (fmap_as_finite_support_relation := [sglobals, tglobals]) (words_as_type_indexed_bitvec)]
theorem crepToLoopGlobalsRelHOLExact_intro {width : Nat} [NeZero width]
    (sglobals : HolFiniteMapExact (BitVec 5) (HolWordLab width))
    (tglobals : HolFiniteMapExact (BitVec 5) (WordLocW width)) :
    crepToLoopGlobalsRelHOLExact sglobals tglobals →
      ∀ ad v, sglobals.lookup ad = some v → tglobals.lookup ad = some (wlabWlocExact v) :=
  fun h => h

end Flapjack
