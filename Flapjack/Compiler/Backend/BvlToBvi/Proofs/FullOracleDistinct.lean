module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracle
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.WholeNames
@[expose] public section

/-! Distinct function names in the whole-pass incremental oracle. -/
open Flapjack Flapjack.Compiler.Backend
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
/-- The original oracle namespace conditions preserve all function-name distinctness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "ALL_DISTINCT_MAP_FST_SND_full_co"]
theorem fullCo_distinctNames {I C : Type} (c : BvlToBvi.Config)
    (co : I → (Spt (Nat × Bvl.Exp) × Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × C) ×
      List (Nat × Nat × Bvl.Exp)) (n : I)
    (assumptions : ((co n).2.map Prod.fst).Nodup ∧
      (co n).1.2.2.1 % bvlToBviNamespaces = 2 ∧
      (co n).1.2.2.2.1 % bvlToBviNamespaces = 3) :
    (((fullCo c co n).2).map Prod.fst).Nodup := by
  rcases h : co n with ⟨⟨cache, next1, next2, next3, bcache, cfg⟩, prog⟩
  simp only [h] at assumptions
  obtain ⟨inputDistinct, mod2, mod3⟩ := assumptions
  rcases hi : BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut cache prog with ⟨ic, pi⟩
  rcases hl : BvlToBvi.compileIncSource next1 pi with ⟨n1, p⟩
  rcases ht : BviTailrec.compileProgSource c.doTailrec next2 p with ⟨n2, pt⟩
  rcases hm : BviTmc.compileProgSource c.doTmc next3 pt with ⟨n3, pm⟩
  rcases hb : BviInline.compileIncSource bcache pm with ⟨bc, po⟩
  simp only [fullCo, BackendProps.stateCo, h, hi, hl, ht, hm, hb]
  have inlineKeys : po.map Prod.fst = pm.map Prod.fst := BviInline.Proofs.compileInc_mapFst bcache bc pm po hb
  rw [inlineKeys]
  have piKeys : pi.map Prod.fst = prog.map Prod.fst := by
    have hkeys := BvlInline.mapFstTickInlineAll c.inlineSizeLimit cache prog
    rcases hinline : BvlInline.tickInlineAll c.inlineSizeLimit cache prog [] with ⟨cached, inlined⟩
    simp only [hinline] at hkeys
    simp only [BvlInline.compileInc, BvlInline.tickCompileProg, hinline, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl, rfl⟩
    rw [BvlInline.Proofs.mapFstMapOptimise, hkeys]
  have piDistinct : (pi.map Prod.fst).Nodup := by simpa only [piKeys] using inputDistinct
  have pDistinct : (p.map Prod.fst).Nodup := by
    have h := compileIncSource_names_nodup next1 pi piDistinct
    simpa only [hl] using h
  have pNot2 : ∀ x ∈ p.map Prod.fst, ¬BviTailrec.inWorkerNamespace x := by
    intro x hx
    apply compileIncSource_outside_tailrec_namespace next1 pi x
    simpa only [hl] using hx
  have pNot3 : ∀ x ∈ p.map Prod.fst, ¬BviTmc.inWorkerNamespace x := by
    intro x hx
    apply compileIncSource_outside_tmc_namespace next1 pi x
    simpa only [hl] using hx
  have pFree : ∀ x ∈ p.map Prod.fst, BviTailrec.freeNames next2 x := by
    intro x hx
    exact freeNames_of_not_worker next2 x mod2 (pNot2 x hx)
  have ptDistinct : (pt.map Prod.fst).Nodup := by
    cases flag : c.doTailrec with
    | false =>
      simp [BviTailrec.compileProgSource, flag] at ht
      obtain ⟨_, rfl⟩ := ht
      exact pDistinct
    | true =>
      have tailEq : BviTailrec.compileEachSource next2 p = (n2, pt) := by
        simpa [BviTailrec.compileProgSource, flag] using ht
      have result := BviTailrec.compileEachSource_labels_nodup p next2 pDistinct pFree
      simpa only [tailEq] using result
  have ptNot3 : ∀ x ∈ pt.map Prod.fst, ¬BviTmc.inWorkerNamespace x := by
    intro x hx
    cases flag : c.doTailrec with
    | false =>
      simp [BviTailrec.compileProgSource, flag] at ht
      obtain ⟨_, rfl⟩ := ht
      exact pNot3 x hx
    | true =>
      have tailEq : BviTailrec.compileEachSource next2 p = (n2, pt) := by
        simpa [BviTailrec.compileProgSource, flag] using ht
      have member : x ∈ (BviTailrec.compileEachSource next2 p).2.map Prod.fst := by
        simpa only [tailEq] using hx
      rcases BviTailrec.compileEachSource_mem p next2 x member with old | ⟨_, _, k, equal⟩
      · exact pNot3 x old
      · rw [equal]
        unfold BviTmc.inWorkerNamespace
        simp only [bvlToBviNamespaces] at mod2 ⊢
        omega
  have ptFree : ∀ entry ∈ pt, BviTmc.freeNames next3 entry.1 := by
    intro entry mem k equal
    have outside := ptNot3 entry.1 (List.mem_map.mpr ⟨entry, mem, rfl⟩)
    apply outside
    rw [← equal]
    unfold BviTmc.inWorkerNamespace
    simp only [bvlToBviNamespaces] at mod3 ⊢
    omega
  exact (BviTmc.compileProgSource_distinct_and_free c.doTmc next3 n3 pt pm hm ptDistinct ptFree).1
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
