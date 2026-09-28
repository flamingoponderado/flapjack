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

/-! Same-module relation witness for the `fmap_as_finite_support_relation`
qualifier on `crepToLoopCodeRelIntro`: the owning carrier of the traversed
`funcs` field is `CrepToLoopContextExact`; the standalone `s_code` parameter is
validated directly at its `HolFiniteMapExact` binder and needs no owner
witness. -/
namespace CrepToLoopCodeRelIntroFiniteMapWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCodeRelIntroFiniteMapWitnesses

/-- Exact port of HOL `code_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:187-202`): the
    `code_rel_def` unfolding, preserving the HOL antecedent
    `code_rel ctxt s_code t_code` and the `distinct_funcs` plus
    universal-existential conclusion verbatim.  Every component is the reviewed
    exact translation used by `crepToLoopCodeRelExact` (`distinct_funcs_def`,
    `HolFiniteMapExact.lookup`, `sptLookup`, `List.range`, `ctxtFcExact`,
    `list_to_num_set` = `listToNumSetHOLExact`, `ocompile` = `ocompileHOLExact`).
    No simplified relation or target-result premise is added; the proof is the
    definitional unfolding, as in HOL (`rw [code_rel_def]`).

    The `@[hol]` tag is WITHDRAWN: the canonical integrated exact port of HOL
    `code_rel_intro` is `crepToLoopCodeRelExact_intro` in
    `Flapjack/Pancake/CrepToLoop/StateRel.lean`; this lemma is kept as untagged
    Flapjack infrastructure for comparison only. -/
theorem crepToLoopCodeRelIntro {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width)) :
    crepToLoopCodeRelExact ctxt s_code t_code →
      crepToLoopDistinctFuncs ctxt.funcs.lookup ∧
        ∀ (f : Flapjack.Pancake.PanLang.MlS) (ns : List Nat) (prog : CrepProgHOL width),
          s_code.lookup f = some (ns, prog) →
            ∃ loc len : Nat,
              ctxt.funcs.lookup f = some (loc, len) ∧
                ns.length = len ∧
                  (let args := List.range len
                   let nctxt := ctxtFcExact ctxt.target ctxt.funcs ns args
                   sptLookup loc t_code =
                     some (args, ocompileHOLExact nctxt (listToNumSetHOLExact args) prog)) :=
  fun h => h

end Flapjack
