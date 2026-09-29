import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect
import Flapjack.Pancake.Semantics.ShMemBytesBridge

/-!
# crep_to_loop `ncompile_correct`, case `ShMem`

`Resume ncompile_correct[ShMem]` (`crep_to_loopProofScript.sml:2106-2239`) over
the exact carriers, using the shared statement helpers of
`Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect`.
-/

namespace Flapjack

namespace ShMemHelpers
/-! Flapjack helpers (no HOL declaration): the per-operator `sh_mem_load` /
`sh_mem_store` steps of HOL's ShMem case (`crepSemTheory.sh_mem_*_def`,
`loopSemTheory.sh_mem_*_def`), including the `lookup_insert` / `FLOOKUP_UPDATE`
`locals_rel` step for the loaded variable. -/

variable {width : Nat} [NeZero width] {σ : Type}

/-- Writing the same value to a source variable and its mapped target slot
    preserves `locals_rel`. -/
theorem locals_rel_setVar (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (name mn : Nat) (v : HolWordLab width)
    (h : crepToLoopLocalsRelExact ctxt l sl tl) (hn : ctxt.vars.lookup name = some mn)
    (hmn : sptMem mn l) :
    crepToLoopLocalsRelExact ctxt l (sl.updateEq (name, v)) (sptInsert mn (wlabWlocHOL v) tl) := by
  refine ⟨h.1, h.2.1, fun k hk => (sptMem_sptInsert k mn _ _).mpr (Or.inr (h.2.2.1 k hk)),
    fun vn val hval => ?_⟩
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hval
  by_cases hv : vn = name
  · subst hv
    simp only [if_true, Option.some.injEq] at hval
    subst hval
    refine ⟨mn, hn, hmn, ?_⟩
    rw [sptLookup_sptInsert, if_pos rfl]
  · rw [if_neg hv] at hval
    obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hne : n ≠ mn := fun e => hv (h.1 vn name n mn hn1 hn e)
    refine ⟨n, hn1, hn2, ?_⟩
    rw [sptLookup_sptInsert, if_neg hne]
    exact hn3


/-- A Crep shared-memory load and the Loop one at the mapped variable agree. -/
theorem shMemLoad_corresponds (v1 : CrepSemHOLState width σ) [DecidablePred v1.shMemaddrs]
    (st : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (name mn : Nat) (addr : BitVec width) (nb : Nat)
    (r : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (hs : crepToLoopStateRelExact v1 st)
    (hm : crepToLoopMemRelHOLExact v1.memory st.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals st.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code st.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals st.locals)
    (hn : ctxt.vars.lookup name = some mn) (hmn : sptMem mn l)
    (he : crepShMemLoadExactHOL name addr nb v1 = (r, s1)) (hne : r ≠ some .error) :
    ∃ t1 : LoopSemStateFiniteExact width σ,
      LoopSemStateFiniteExact.shMemLoad mn addr nb st = (crepToLoopResultHOL r, t1) ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals r := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
  unfold crepShMemLoadExactHOL at he
  unfold LoopSemStateFiniteExact.shMemLoad
  rw [riscvByteAlignHOL_eq_panByteAlignHOL, panWordToBytesHOL_eq_map_crepClockWordToBytes addr,
    ← hs5]
  by_cases hnb : nb = 0 <;> simp only [hnb, if_true, if_false] at he ⊢ <;>
  · split at he
    · rename_i hd
      rw [hs2] at hd
      rw [if_pos hd]
      split at he
      · rename_i e hcall
        rw [hcall]
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, rfl, ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩, hm, hg, hc, trivial⟩
      · rename_i nf nbs hcall
        rw [hcall]
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨_, rfl, ⟨hs1, hs2, hs3, hs4, rfl, hs6, hs7⟩, hm, hg, hc, ?_⟩
        show crepToLoopLocalsRelExact ctxt l _ (sptInsert mn _ st.locals)
        rw [panWordOfBytesHOL_eq_crepClockWordOfBytes]
        exact locals_rel_setVar ctxt l v1.locals st.locals name mn _ hl hn hmn
    · simp only [Prod.mk.injEq] at he
      exact absurd he.1.symm hne


/-- A Crep shared-memory store and the Loop one at the mapped variable agree. -/
theorem shMemStore_corresponds (v1 : CrepSemHOLState width σ) [DecidablePred v1.shMemaddrs]
    (st : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (name mn : Nat) (addr : BitVec width) (nb : Nat)
    (r : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (hs : crepToLoopStateRelExact v1 st)
    (hm : crepToLoopMemRelHOLExact v1.memory st.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals st.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code st.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals st.locals)
    (hn : ctxt.vars.lookup name = some mn)
    (he : crepShMemStoreExactHOL name addr nb v1 = (r, s1)) (hne : r ≠ some .error) :
    ∃ t1 : LoopSemStateFiniteExact width σ,
      LoopSemStateFiniteExact.shMemStore mn addr nb st = (crepToLoopResultHOL r, t1) ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals r := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
  unfold crepShMemStoreExactHOL at he
  unfold LoopSemStateFiniteExact.shMemStore
  cases hv : v1.locals.lookup name with
  | none => simp only [hv, Prod.mk.injEq] at he; exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word value =>
  obtain ⟨n, hn1, _, hn3⟩ := hl.2.2.2 name _ hv
  have hnn : n = mn := Option.some.inj (hn1.symm.trans hn)
  subst hnn
  simp only [hv] at he
  rw [hn3]
  simp only [wlabWlocHOL]
  rw [riscvByteAlignHOL_eq_panByteAlignHOL, panWordToBytesHOL_eq_map_crepClockWordToBytes addr,
    panWordToBytesHOL_eq_map_crepClockWordToBytes value, ← List.map_take, ← List.map_append,
    ← List.map_append, ← hs5]
  by_cases hnb : nb = 0 <;> simp only [hnb, if_true, if_false] at he ⊢ <;>
  · split at he
    · rename_i hd
      rw [hs2] at hd
      rw [if_pos hd]
      split at he
      · rename_i e hcall
        rw [hcall]
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, rfl, ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩, hm, hg, hc, trivial⟩
      · rename_i nf nbs hcall
        rw [hcall]
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, rfl, ⟨hs1, hs2, hs3, hs4, rfl, hs6, hs7⟩, hm, hg, hc, hl⟩
    · simp only [Prod.mk.injEq] at he
      exact absurd he.1.symm hne

end ShMemHelpers


/-! Owning carriers of the finite maps the statement traverses; same-module
witnesses for the `fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopNcompileCorrectShMemWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end CrepToLoopNcompileCorrectShMemWitnesses

open ShMemHelpers in
/-- `ncompile_correct`, case `ShMem op v e` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[ShMem]` at 2106-2239).  `evaluate_ind`
    gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_shMem {width : Nat} [NeZero width] {σ : Type} :
    ∀ (op : WordMemOp) (v : Nat) (ad : CrepExpHOL width) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.shMem op v ad) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.shMem op v ad))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro op v ad v1 res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  classical
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 ad with
  | none => simp only [hev, Prod.mk.injEq] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | word addr =>
  simp only [hev] at he
  cases hv : v1.locals.lookup v with
  | none => simp [hv] at he; exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word xv =>
  simp only [hv, ite_self] at he
  obtain ⟨mn, hmn1, hmn2, _⟩ := hl.2.2.2 v _ hv
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l ad with ⟨p, le, tmp, l'⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval v1 ad (.word addr) t ctxt (ctxt.vmax + 1) l p le tmp l'
      ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, _, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l ad p le tmp l' hC
  have hsub : sptSubspt l l' := hlA ▸ comp_syn_impl_cut_sets_subspt _ l hokA
  have hlst : crepToLoopLocalsRelExact ctxt l v1.locals st.locals :=
    crepToLoopLocalsRelExact_cutset_prop ctxt l l' v1.locals t.locals st.locals hl h1l hsub
  obtain ⟨n, hn1, _, hn3⟩ := hlst.2.2.2 v _ hv
  have hnn : n = mn := Option.some.inj (hn1.symm.trans hmn1)
  subst hnn
  obtain ⟨t1, hL, h2s, h2m, h2g, h2c, h2l⟩ : ∃ t1 : LoopSemStateFiniteExact width σ,
      LoopSemStateFiniteExact.shMemOp op n addr st = (crepToLoopResultHOL res, t1) ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
    cases op <;> simp only [crepShMemOpExactHOL] at he <;>
      simp only [LoopSemStateFiniteExact.shMemOp] <;>
      first
      | exact shMemLoad_corresponds v1 st ctxt l v n addr _ res s1 h1s h1m h1g h1c hlst hmn1 hmn2
          he hne
      | exact shMemStore_corresponds v1 st ctxt l v n addr _ res s1 h1s h1m h1g h1c hlst hmn1
          he hne
  refine ⟨ck, crepToLoopResultHOL res, t1, ?_, h2s, h2m, h2g, h2c, rfl, h2l⟩
  rw [compileHOLExact, hmn1]
  simp only [hC]
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none p _ _ _ h1]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
  simp only [LoopSemStateFiniteExact.evaluate, h1v, hn3, wlabWlocHOL, wlabWlocExact, ite_self]
  rw [hL]
  rcases res with _ | r
  · rfl
  · cases r <;> rfl
end Flapjack
