import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

/-!
# `evaluate_remove_dead` leaf cases

The `Skip`, `Tick`, `Break`, `Continue`, `Raise`, `Return` and `LocValue` cases of
`word_allocProofScript.sml:3900-4472` `evaluate_remove_dead` (Resume blocks 4116,
4291-4334, 4347). Each theorem is the HOL statement restricted to one constructor;
none needs an induction hypothesis.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadLeavesWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadLeavesWitnesses

/-- HOL `evaluate_remove_dead`, `Skip` case (Resume 4334). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Skip {width : Nat} [NeZero width] {C F : Type} :
    removeDeadGoal C F (.skip : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, -⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rw [evaluate] at hev
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  exact ⟨t, tstore, by rw [evaluate], hl, hs⟩

/-- HOL `evaluate_remove_dead`, `Tick` case (Resume 4347). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Tick {width : Nat} [NeZero width] {C F : Type} :
    removeDeadGoal C F (.tick : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, -⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rw [evaluate] at hev
  rw [evaluate]
  by_cases hz : st.clock = 0
  · have hz' : ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F).clock = 0 := hz
    simp only [hz, if_true, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    rw [if_pos hz']
    exact ⟨(flushState true st).locals, (flushState true st).store, by simp [flushState], rfl, rfl⟩
  · have hz' : ¬ ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F).clock = 0 := hz
    simp only [hz, if_false, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    rw [if_neg hz']
    exact ⟨t, tstore, rfl, hl, hs⟩

/-- HOL `evaluate_remove_dead`, `Break` case (Resume 4291). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Break {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    removeDeadGoal C F (.break k : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, -⟩
  rw [removeDead] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  rw [evaluate] at hev
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  refine ⟨t, st.store, by rw [evaluate], rfl, ?_⟩
  simp only [getLive] at hl
  rw [sptOel_eq_getElem?]
  cases ho : lt[k]? with
  | none => trivial
  | some e => obtain ⟨names, exitNames⟩ := e; simpa [ho] using hl

/-- HOL `evaluate_remove_dead`, `Continue` case (Resume 4296). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Continue {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    removeDeadGoal C F (.continue k : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, -⟩
  rw [removeDead] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  rw [evaluate] at hev
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  refine ⟨t, st.store, by rw [evaluate], rfl, ?_⟩
  simp only [getLive] at hl
  rw [sptOel_eq_getElem?]
  cases ho : lt[k]? with
  | none => trivial
  | some e => obtain ⟨names, exitNames⟩ := e; simpa [ho] using hl

/-- HOL `evaluate_remove_dead`, `Raise` case (Resume 4320). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Raise {width : Nat} [NeZero width] {C F : Type} (n : Nat) :
    removeDeadGoal C F (.raise n : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [removeDead] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  simp only [getLive] at hl
  rw [evaluate] at hev
  rw [evaluate]
  cases hw : getVar n st with
  | none => rw [hw] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some w =>
    have htw : getVar n { st with locals := t, store := st.store } = some w :=
      hl n w ⟨(sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hw⟩
    rw [hw] at hev
    rw [htw]
    dsimp only at hev ⊢
    have hje : jumpExc { st with locals := t, store := st.store } = jumpExc st := rfl
    rw [hje]
    cases hj : jumpExc st with
    | none => rw [hj] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    | some p =>
      obtain ⟨s1, l1, l2⟩ := p
      rw [hj] at hev
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨s1.locals, s1.store, by simp, rfl, rfl⟩

/-- HOL `evaluate_remove_dead`, `Return` case (Resume 4326). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Return {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (ms : List Nat) :
    removeDeadGoal C F (.return n ms : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [removeDead] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  simp only [getLive] at hl
  rw [evaluate] at hev
  rw [evaluate]
  cases hw : getVar n st with
  | none => rw [hw] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some w =>
    cases hws : WordSemStateFiniteExact.getVars ms st with
    | none =>
      rw [hw, hws] at hev
      cases w <;> simp only [Prod.mk.injEq] at hev <;> exact absurd hev.1.symm herr
    | some ys =>
      have htw : getVar n { st with locals := t, store := st.store } = some w :=
        hl n w ⟨(sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hw⟩
      have htws : WordSemStateFiniteExact.getVars ms { st with locals := t, store := st.store } =
          some ys := by
        have := strongLocalsRelIGetVars' ms (sptDomain (numsetListInsert ms live))
          st t ys ⟨fun x hx => (sptDomain_numsetIns _ _ _).mpr (Or.inr hx),
            fun k v hk => hl k v ⟨(sptDomain_ins _ _ _ _).mpr (Or.inr hk.1), hk.2⟩, hws⟩
        exact this
      rw [hw, hws] at hev
      rw [htw, htws]
      cases w with
      | word _ => simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      | loc l1 l2 =>
        simp only [Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl⟩ := hev
        exact ⟨(flushState false st).locals, (flushState false st).store,
          by simp [flushState], rfl, rfl⟩

/-- HOL `evaluate_remove_dead`, `LocValue` case (Resume 4116): a dead destination is
removed (its write is outside the live set), a live one keeps the instruction. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_LocValue {width : Nat} [NeZero width] {C F : Type} (r l1 : Nat) :
    removeDeadGoal C F (.locValue r l1 : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [evaluate] at hev
  by_cases hm : sptMem l1 st.code
  · simp only [hm, if_true, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    by_cases hd : sptLookup r live = none
    · simp only [removeDead, hd, if_true, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      refine ⟨t, tstore, by rw [evaluate]; rfl, ?_, hs⟩
      refine strongLocalsRelInsertNotin id _ _ _ r _ ⟨hl, ?_⟩
      simp [sptDomain, hd]
    · simp only [removeDead, hd, if_false, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      refine ⟨sptInsert r (.loc l1 0) t, tstore, ?_, ?_, hs⟩
      · rw [evaluate]
        have hm' : sptMem l1 ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F).code := hm
        simp only [hm', if_true, setVar]
      · refine strongLocalsRelIInsertInsert _ r _ _ _ _ ⟨?_, rfl⟩
        intro k v ⟨hk, hv⟩
        exact hl k v ⟨(sptDomain_del _ _ _).mpr ⟨hk.2, hk.1⟩, hv⟩
  · simp only [hm, if_false, Prod.mk.injEq] at hev
    exact absurd hev.1.symm herr

end Flapjack.WordAlloc
