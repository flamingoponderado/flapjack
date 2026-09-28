import Flapjack.Pancake.CrepToLoop.StateRel

/-!
# crep_to_loop `wlab_wloc`, `mem_rel` and `globals_rel` over the exact carriers

Exact ports of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`wlab_wloc_def` (45), `mem_rel_def` (49), `globals_rel_def` (54),
`mem_rel_intro` (203), `globals_rel_intro` (211), and `code_rel_intro` (187)
over the exact Crep/Loop
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

/-- Exact port of HOL `code_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:187-200`): assuming
    `code_rel`, expose its `distinct_funcs` conjunct and its universally
    quantified per-source-function existential. The exact carriers and
    `fmap_as_finite_support_relation`/word qualifiers are the same as
    `crepToLoopCodeRelExact` from the imported `StateRel` module; no target
    lookup result or extra context premise is assumed. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel_intro"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.funcs, s_code])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopCodeRelExact_intro {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact Pancake.PanLang.MlS (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width)) :
    crepToLoopCodeRelExact ctxt s_code t_code →
      crepToLoopDistinctFuncs ctxt.funcs.lookup ∧
        ∀ (f : Pancake.PanLang.MlS) (ns : List Nat) (prog : CrepProgHOL width),
          s_code.lookup f = some (ns, prog) →
            ∃ loc len : Nat,
              ctxt.funcs.lookup f = some (loc, len) ∧
                ns.length = len ∧
                  (let args := List.range len
                   let nctxt := ctxtFcExact ctxt.target ctxt.funcs ns args
                   sptLookup loc t_code =
                     some (args, ocompileHOLExact nctxt (listToNumSetHOLExact args) prog)) := by
  intro h
  rw [crepToLoopCodeRelExact] at h
  exact h

end Flapjack

namespace Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact

/-! The finite-map relation tag in this proof module needs its own local,
kernel-checked witness naming the imported carrier. This repeats the carrier's
canonical roundtrip theorem without changing or restating the carrier. -/

/-- Same-module finite-map relation witness for `CrepToLoopContextExact`.
    The imported carrier's canonical `toBroad`/`ofBroad` roundtrip is reused. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : Flapjack.CrepToLoopContextExact) :
    Flapjack.CrepToLoopContextExact.ofBroad
        (Flapjack.CrepToLoopContextExact.toBroad context) = context :=
  Flapjack.CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
