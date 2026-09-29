import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.Proofs.LocalsRelHelpers
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.HolRef

/-!
# crep_to_loop `call_preserve_state_code_locals_rel`

Exact-carrier port of `crep_to_loopProofScript.sml:3133`.  This is the
Crep-to-Loop helper, distinct from the similarly named Pan-to-Crep theorem at
`pan_to_crepProofScript.sml:2355`.  The source statement and the exact call
context/finite-map carriers are compared in the linked bead
`flapjack-pxn.18.5.6.33.17`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

private theorem listToNumSetHOLExact_mem_iff (key : Nat) (keys : List Nat) :
    sptMem key (listToNumSetHOLExact keys) ↔ key ∈ keys := by
  induction keys with
  | nil => simp [listToNumSetHOLExact, sptMem, sptDomain]
  | cons head tail ih =>
      rw [listToNumSetHOLExact_cons, sptMem_sptInsert, ih]
      simp

private theorem getElem_le_foldr_max_zero (keys : List Nat) (index : Nat)
    (hindex : index < keys.length) :
    keys[index] ≤ keys.foldr max 0 := by
  induction keys generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem_cons_zero, List.foldr_cons]
          exact Nat.le_max_left _ _
      | succ index =>
          have hindex' : index < tail.length := by simpa using hindex
          simpa only [List.getElem_cons_succ, List.foldr_cons] using
            (Nat.le_trans (ih index hindex') (Nat.le_max_right head (tail.foldr max 0)))

namespace CrepToLoopCallPreserveWitnesses

/-- Flapjack-only re-export of the exact context finite-support roundtrip for
    this theorem's `fmap_as_finite_support_relation` qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

/-- Flapjack-only re-export of the exact Crep state finite-support roundtrip
    for this theorem's `fmap_as_finite_support_relation` qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Flapjack-only re-export of the exact Loop state finite-support roundtrip
    for this theorem's `fmap_as_finite_support_relation` qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end CrepToLoopCallPreserveWitnesses

/-- Exact HOL `call_preserve_state_code_locals_rel`
(`crep_to_loopProofScript.sml:3133-3175`).  In particular, the hypothesis is
the pre-call `locals_rel ctxt nl s.locals st.locals`; the conclusion relates
the freshly installed source/target callee locals under `ctxt_fc` and
`list_to_num_set lns`.  `MAP (eval s) argexps = MAP SOME args` is kept as a
map of per-expression results over the decider-free exact `evalCrepSemHOLExp`
(`eval_def`), and `MAP wlab_wloc args` uses the tagged `wlabWlocExact`
(definitionally the `wlabWlocHOL` inside the tagged `locals_rel`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml"
  "call_preserve_state_code_locals_rel"
  (fmap_as_finite_support_relation := [
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopCallPreserveStateCodeLocalsRelExact
    {width : Nat} [NeZero width] {σ : Type} :
    ∀ (ns lns : List Nat) (args : List (HolWordLab width))
      (s : CrepSemHOLState width σ) (st : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (nl : NumSet)
      (fname : Flapjack.Basis.Pure.MlString.MlString)
      (argexps : List (CrepExpHOL width)) (prog : CrepProgHOL width) (loc : Nat),
      ns.Nodup → lns.Nodup → ns.length = lns.length → args.length = lns.length →
      crepToLoopStateRelExact s st →
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs →
      crepToLoopGlobalsRelHOLExact s.globals st.globals →
      crepToLoopCodeRelExact ctxt s.code st.code →
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals →
      s.code.lookup fname = some (ns, prog) →
      ctxt.funcs.lookup fname = some (loc, lns.length) →
      List.map (evalCrepSemHOLExp s) argexps = List.map some args →
      let nctxt := ctxtFcExact ctxt.target ctxt.funcs ns lns
      crepToLoopStateRelExact
          ({ s with
            locals := HolFiniteMapExact.updateList HolFiniteMapExact.empty (ns.zip args),
            clock := s.clock - 1 })
          ({ st with
            locals := sptFromAList (lns.zip (args.map wlabWlocExact)),
            clock := st.clock - 1 }) ∧
        crepToLoopCodeRelExact nctxt s.code st.code ∧
        crepToLoopLocalsRelExact nctxt (listToNumSetHOLExact lns)
          (HolFiniteMapExact.updateList HolFiniteMapExact.empty (ns.zip args))
          (sptFromAList (lns.zip (args.map wlabWlocExact))) := by
  intro ns lns args s st ctxt nl fname argexps prog loc hns hlns hnslen hargslen
    hstate hmem hglobals hcode hlocals hsource hfunction hargs
  have hw : (wlabWlocExact : HolWordLab width → WordLocW width) = wlabWlocHOL := by
    funext v; cases v; rfl
  rw [hw]
  let nctxt : CrepToLoopContextExact := ctxtFcExact ctxt.target ctxt.funcs ns lns
  refine ⟨?_, ?_, ?_⟩
  · simp only [crepToLoopStateRelExact] at hstate ⊢
    rcases hstate with ⟨hmemaddrs, hshmemaddrs, hclock, hbe, hffi, hbase, htop⟩
    refine ⟨hmemaddrs, hshmemaddrs, ?_, hbe, hffi, hbase, htop⟩
    simp [hclock]
  · simpa [nctxt, ctxtFcExact, crepToLoopCodeRelExact] using hcode
  · -- The fresh local maps encode the same positional `ns`/`lns` bindings.
    simp only [ctxtFcExact]
    rw [crepToLoopLocalsRelExact_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y n m hx hy hnm
      simp only [HolFiniteMapExact.empty] at hx hy
      obtain ⟨i, hi, hix⟩ := fmEmptyZipFlookup ns lns x n hnslen hns hx
      obtain ⟨j, hj, hjy⟩ := fmEmptyZipFlookup ns lns y m hnslen hns hy
      have hni : lns[i]'(by omega) = n := by
        have := congrArg Prod.snd hix
        simpa only [List.getElem_zip, hnm] using this
      have hmi : lns[j]'(by omega) = m := by
        have := congrArg Prod.snd hjy
        simpa only [List.getElem_zip] using this
      have hij : i = j := (List.getElem_inj hlns).mp (hni.trans (hnm.trans hmi.symm))
      subst j
      have hzipBound : i < (ns.zip lns).length := by
        simp only [List.length_zip]
        omega
      have hxy : x = y := by
        have hfirst := congrArg Prod.fst hix
        have hsecond := congrArg Prod.fst hjy
        calc
          x = ((ns.zip lns)[i]'hzipBound).fst := by simpa using hfirst.symm
          _ = y := by simpa using hsecond
      exact hxy
    · intro x m hlookup
      simp only [HolFiniteMapExact.empty] at hlookup
      obtain ⟨i, hi, hpair⟩ := fmEmptyZipFlookup ns lns x m hnslen hns hlookup
      have hvalue : lns[i]'(by omega) = m := by
        have := congrArg Prod.snd hpair
        simpa only [List.getElem_zip] using this
      have hi' : i < lns.length := by omega
      simpa [ctxtFcExact, hvalue] using getElem_le_foldr_max_zero lns i hi'
    · intro key hkey
      have hkeymem : key ∈ lns := (listToNumSetHOLExact_mem_iff key lns).mp hkey
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hkeymem
      have hiLns : i < lns.length := by simpa using hi
      have hiArgs : i < args.length := by omega
      have hiMap : i < (args.map wlabWlocHOL).length := by simpa using hiArgs
      have hlenMap : (args.map wlabWlocHOL).length = lns.length := by simp [hargslen]
      have hiZip : i < (lns.zip (args.map wlabWlocHOL)).length := by
        simp only [List.length_zip]
        omega
      have hpair : (key, (args.map wlabWlocHOL)[i]'hiMap) ∈
          lns.zip (args.map wlabWlocHOL) := by
        have hgetZip : (lns.zip (args.map wlabWlocHOL))[i]'hiZip =
            (lns[i]'hiLns, (args.map wlabWlocHOL)[i]'hiMap) := by
          simp only [List.getElem_zip]
        have hmem := List.getElem_mem hiZip
        rw [hgetZip] at hmem
        simpa [hget] using hmem
      have hkeys : (lns.zip (args.map wlabWlocHOL)).map Prod.fst = lns :=
        List.map_fst_zip (Nat.le_of_eq hlenMap.symm)
      have hkeysNodup : ((lns.zip (args.map wlabWlocHOL)).map Prod.fst).Nodup := by
        rw [hkeys]
        exact hlns
      have hlookup := memLookupFromAListSomeExact
        (entries := lns.zip (args.map wlabWlocHOL)) (key := key)
        (value := (args.map wlabWlocHOL)[i]'hiMap)
        hkeysNodup hpair
      have hkeyi : key = lns[i]'hiLns := hget.symm
      simpa [hkeyi] using (sptMem_iff_lookup key _).mpr ⟨_, hlookup⟩
    · intro vname value hlookup
      simp only [HolFiniteMapExact.empty] at hlookup
      have hnsargs : ns.length = args.length := hnslen.trans hargslen.symm
      obtain ⟨i, hi, hsource⟩ := fmEmptyZipFlookup ns args vname value hnsargs hns hlookup
      have hiLns : i < lns.length := by omega
      have hiArgs : i < args.length := by omega
      have hsourceKey : vname = ns[i]'hi := by
        have := congrArg Prod.fst hsource
        simpa only [List.getElem_zip] using this.symm
      have hsourceValue : value = args[i]'hiArgs := by
        have := congrArg Prod.snd hsource
        simpa only [List.getElem_zip] using this.symm
      subst vname
      subst value
      refine ⟨lns[i]'(by omega), ?_, ?_, ?_⟩
      · simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.empty]
        exact updateEqZipFlookupHOL ns lns
          (FEMPTY : FiniteMap Nat Nat) i hns hnslen hi
      · exact (listToNumSetHOLExact_mem_iff _ _).mpr (List.getElem_mem hiLns)
      · have hiMap : i < (args.map wlabWlocHOL).length := by simpa using hiArgs
        have hlenMap : (args.map wlabWlocHOL).length = lns.length := by simp [hargslen]
        have hiZip : i < (lns.zip (args.map wlabWlocHOL)).length := by
          simp only [List.length_zip]
          omega
        have hmemPair : (lns[i]'hiLns, (args.map wlabWlocHOL)[i]'hiMap) ∈
            lns.zip (args.map wlabWlocHOL) := by
          have hgetZip : (lns.zip (args.map wlabWlocHOL))[i]'hiZip =
              (lns[i]'hiLns, (args.map wlabWlocHOL)[i]'hiMap) := by
            simp only [List.getElem_zip]
          simpa [hgetZip] using List.getElem_mem hiZip
        have hkeys : (lns.zip (args.map wlabWlocHOL)).map Prod.fst = lns :=
          List.map_fst_zip (Nat.le_of_eq hlenMap.symm)
        have hkeysNodup : ((lns.zip (args.map wlabWlocHOL)).map Prod.fst).Nodup := by
          rw [hkeys]
          exact hlns
        have hlookupTarget := memLookupFromAListSomeExact
          (entries := lns.zip (args.map wlabWlocHOL)) (key := lns[i]'(by omega))
          (value := (args.map wlabWlocHOL)[i]'hiMap)
          hkeysNodup hmemPair
        simpa using hlookupTarget

end Flapjack
