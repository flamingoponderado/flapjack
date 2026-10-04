import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Leaves

/-!
# `evaluate_remove_dead` store cases

The `Get`, `OpCurrHeap` and `Set` cases of `word_allocProofScript.sml:3900-4472`
`evaluate_remove_dead` (Resume blocks 4073, 4090, 4123).
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadStoreWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadStoreWitnesses

/-- Writing `v` to the locals of both sides re-establishes the relation on `live`
from the relation on `live \ {v}` (Flapjack infrastructure). -/
theorem slrSetVar {width : Nat} [NeZero width] (live : NumSet) (v : Nat) (x : WordLocW width)
    (s t : Spt (WordLocW width)) (h : strongLocalsRel id (sptDomain (sptDelete v live)) s t) :
    strongLocalsRel id (sptDomain live) (sptInsert v x s) (sptInsert v x t) :=
  strongLocalsRelIInsertInsert _ v _ _ _ _
    ⟨fun k w ⟨hk, hw⟩ => h k w ⟨(sptDomain_del _ _ _).mpr ⟨hk.2, hk.1⟩, hw⟩, rfl⟩

/-- A filtered dead-store list is contained in the original (Flapjack infrastructure). -/
theorem filterSub {α : Type} (p : α → Bool) (l : List α) : ∀ x, x ∈ l.filter p → x ∈ l :=
  fun _ hx => (List.mem_filter.mp hx).1

/-- HOL `evaluate_remove_dead`, `Get` case (Resume 4073). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateRemoveDead_Get {width : Nat} [NeZero width] {C F : Type} (v : Nat)
    (name : WordStoreHOL) :
    removeDeadGoal C F (.get v name : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [evaluate] at hev
  cases hg : getStore name st with
  | none => rw [hg] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some x =>
    rw [hg] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    by_cases hd : sptLookup v live = none
    · simp only [removeDead, hd, if_true, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      exact ⟨t, tstore, by rw [evaluate]; rfl,
        strongLocalsRelInsertNotin id _ _ _ v _ ⟨hl, by simp [sptDomain, hd]⟩, hs⟩
    · simp only [removeDead, hd, if_false, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      have htg : getStore name { st with locals := t, store := tstore } = some x := by
        have := liveStoreRelFlookupStore _ st.store tstore name
          ⟨hs, by simp⟩
        simp only [getStore] at hg ⊢
        rw [this]; exact hg
      refine ⟨sptInsert v x t, tstore, ?_, slrSetVar live v x _ _ hl,
        liveStoreRelLess _ _ _ _ ⟨hs, filterSub _ _⟩⟩
      rw [evaluate, htg]; rfl

/-- HOL `evaluate_remove_dead`, `OpCurrHeap` case (Resume 4090). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateRemoveDead_OpCurrHeap {width : Nat} [NeZero width] {C F : Type} (b : BinOp)
    (dst src : Nat) :
    removeDeadGoal C F (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [evaluate] at hev
  cases hw : wordExp st (.op b [.var src, .lookup .currHeap]) with
  | none => rw [hw] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some w =>
    rw [hw] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    by_cases hd : sptLookup dst live = none
    · simp only [removeDead, hd, if_true, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      exact ⟨t, tstore, by rw [evaluate]; rfl,
        strongLocalsRelInsertNotin id _ _ _ dst _ ⟨hl, by simp [sptDomain, hd]⟩, hs⟩
    · simp only [removeDead, hd, if_false, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      have htw : wordExp { st with locals := t, store := tstore }
          (.op b [.var src, .lookup .currHeap]) = some w := by
        refine strongLocalsRelIWordExp t (sptDelete dst live) _ tstore st _ w ⟨hw, ?_, hs, ?_⟩
        · intro k v ⟨hk, hv⟩
          refine hl k v ⟨?_, hv⟩
          rw [sptDomain_sptUnion] at hk
          rw [sptDomain_ins]
          rcases hk with hk | hk
          · left
            simp only [getLiveExp, bigUnion, List.map_cons, List.map_nil, List.foldr_cons,
              List.foldr_nil, sptDomain_sptUnion, sptDomain_ins] at hk
            rcases hk with (hk | hk) | hk | hk
            · exact hk
            all_goals exact absurd hk (sptDomain_ln k)
          · exact Or.inr hk
        · simp only [nliveStore]
          rintro ⟨e, he⟩
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
          rcases he with rfl | rfl <;> simp [nliveStore]
      refine ⟨sptInsert dst w t, tstore, ?_, slrSetVar live dst w _ _ (fun k v ⟨hk, hv⟩ =>
          hl k v ⟨(sptDomain_ins _ _ _ _).mpr (Or.inr hk), hv⟩),
        liveStoreRelLess _ _ _ _ ⟨hs, filterSub _ _⟩⟩
      rw [evaluate, htw]; rfl

/-- HOL `evaluate_remove_dead`, `Set` case (Resume 4123); `flat_exp_conventions`
restricts the expression to a register. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateRemoveDead_Set {width : Nat} [NeZero width] {C F : Type} (v : WordStoreHOL)
    (exp : WordLangExpHOL (BitVec width)) :
    removeDeadGoal C F (.set v exp : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  cases exp with
  | var r =>
    rw [evaluate] at hev
    by_cases hv : v = .handler ∨ v = .bitmapBase
    · simp only [hv, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [hv, if_false] at hev
      cases hw : wordExp st (.var r) with
      | none => rw [hw] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      | some w =>
        rw [hw] at hev
        simp only [Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl⟩ := hev
        by_cases hm : v ∈ nlive
        · simp only [removeDead, hm, if_true, Prod.mk.injEq] at hrd
          obtain ⟨rfl, rfl, rfl⟩ := hrd
          refine ⟨t, tstore, by rw [evaluate]; rfl, hl, ?_⟩
          intro n hn
          have hne : n ≠ v := fun h => hn (h ▸ hm)
          simp [setStore, FUPDATE_HOL, hne, hs n hn]
        · simp only [removeDead, hm, if_false, Prod.mk.injEq] at hrd
          obtain ⟨rfl, rfl, rfl⟩ := hrd
          have htw : wordExp { st with locals := t, store := tstore } (.var r) = some w := by
            simp only [wordExp, getVar] at hw ⊢
            exact hl r w ⟨(sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hw⟩
          refine ⟨t, tstore.updateEq (v, w), ?_,
            fun k x ⟨hk, hx⟩ => hl k x ⟨(sptDomain_ins _ _ _ _).mpr (Or.inr hk), hx⟩, ?_⟩
          · rw [evaluate]
            have hv' : ¬ (v = .handler ∨ v = .bitmapBase) := hv
            simp only [hv', if_false, htw]; rfl
          · intro n hn
            by_cases hnv : n = v
            · subst hnv; simp [setStore, FUPDATE_HOL]
            · have := hs n (by simp [hnv, hn])
              simp [setStore, FUPDATE_HOL, hnv, this]
  | _ => simp [flatExpConventions] at hflat

end Flapjack.WordAlloc
