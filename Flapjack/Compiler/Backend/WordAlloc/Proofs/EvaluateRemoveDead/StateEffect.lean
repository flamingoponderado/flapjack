import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Store
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel

/-!
# `evaluate_remove_dead` state-effect cases

The `Alloc`, `StoreConsts`, `Install`, `CodeBufferWrite`, `DataBufferWrite`, `FFI`
and `ShareInst` cases of `word_allocProofScript.sml:3900-4472`
`evaluate_remove_dead` (Resume blocks 4301, 4338, 4352, 4376, 4393, 4410, 4438).
`remove_dead` leaves each of these programs unchanged; Alloc resets the dead-store
list to `[]`, the others keep it.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadStateEffectWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadStateEffectWitnesses

/-- `flush_state T` forgets the locals and the store (Flapjack infrastructure). -/
theorem flushStateWith {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    flushState true { s with locals := t, store := ts } = flushState true s := rfl

/-- `gc` leaves the locals alone (Flapjack infrastructure). -/
theorem gcWithLocals {width : Nat} [NeZero width] {C F : Type}
    (x : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    gc { x with locals := t } = (gc x).map (fun y => { y with locals := t }) := by
  unfold gc
  simp only
  split <;> (try split) <;> rfl

/-- `pop_env` overwrites the locals (Flapjack infrastructure). -/
theorem popEnvWithLocals {width : Nat} [NeZero width] {C F : Type}
    (g : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    popEnv { g with locals := t } = popEnv g := by
  unfold popEnv
  simp only

/-- `alloc` reads the locals only through its cut sets (Flapjack infrastructure;
HOL's Alloc case unfolds `alloc_def`, `push_env`, `gc` and `pop_env` inline). -/
theorem allocWithLocals {width : Nat} [NeZero width] {C F : Type} (w : BitVec width)
    (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (h : wordSemCutEnvs names t = wordSemCutEnvs names s.locals)
    (herr : (alloc w names s).1 ≠ some .error) :
    alloc w names { s with locals := t } = alloc w names s := by
  unfold alloc at herr ⊢
  have h' : wordSemCutEnvs names ({ s with locals := t } : WordSemStateFiniteExact width C F).locals =
      wordSemCutEnvs names s.locals := h
  rw [h']
  cases hc : wordSemCutEnvs names s.locals with
  | none => rw [hc] at herr; exact absurd rfl herr
  | some envs =>
    rw [hc] at herr
    simp only at herr ⊢
    have hp : pushEnv envs none (setStore .allocSize (.word w) { s with locals := t }) =
        { pushEnv envs none (setStore .allocSize (.word w) s) with locals := t } := rfl
    rw [hp]
    rw [gcWithLocals]
    cases hgc : gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => rw [hgc] at herr; exact absurd rfl herr
    | some g =>
      rw [hgc] at herr
      simp only [Option.map, popEnvWithLocals]
      cases hpe : popEnv g with
      | none => rfl
      | some g' => rfl

/-- HOL `evaluate_remove_dead`, `Alloc` case (Resume 4301). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (names : WordLangCutsetsHOL) :
    removeDeadGoal C F (.alloc n names : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [removeDead] at hrd
  simp only [getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  rw [evaluate] at hev
  rw [evaluate]
  have hdom : ∀ k, sptDomain (sptInsert n () (sptUnion names.1 names.2)) k ↔
      k = n ∨ sptDomain names.1 k ∨ sptDomain names.2 k := by
    intro k; rw [sptDomain_ins, sptDomain_sptUnion]
  cases hv : getVar n st with
  | none => rw [hv] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some x =>
    cases x with
    | loc _ _ => rw [hv] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    | word w =>
      rw [hv] at hev
      simp only at hev
      have hv' : getVar n ({ st with locals := t, store := st.store } :
          WordSemStateFiniteExact width C F) = some (.word w) :=
        strongLocalsRelIGetVar n _ st t st.store _
          ⟨hv, slrMono hl (fun k hk => (hdom k).mpr (hk.elim Or.inl (Or.inr ∘ Or.inl)))⟩
      rw [hv']
      have hcut : wordSemCutEnvs names t = wordSemCutEnvs names st.locals := by
        cases hc : wordSemCutEnvs names st.locals with
        | none =>
          have : (alloc w names st).1 = some .error := by unfold alloc; rw [hc]
          rw [hev] at this; exact absurd this herr
        | some x =>
          exact strongLocalsRelICutEnvs names st t x
            ⟨slrMono hl (fun k hk => (hdom k).mpr (Or.inr hk)), hc⟩
      have herr' : (alloc w names st).1 ≠ some .error := by rw [hev]; exact herr
      have hwl := allocWithLocals w names st t hcut herr'
      refine ⟨rst.locals, rst.store, ?_, ?_⟩
      · show alloc w names { st with locals := t } = _
        rw [hwl, hev]
      · cases res with
        | none => exact ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _⟩
        | some r =>
          cases r <;> first
            | exact ⟨rfl, rfl⟩
            | exact ⟨rfl, by split <;> first | trivial | exact strongLocalsRelIdRefl _ _⟩

/-- HOL `evaluate_remove_dead`, `StoreConsts` case (Resume 4338). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_StoreConsts {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 addr offset : Nat) (words : List (Bool × BitVec width)) :
    removeDeadGoal C F (.storeConsts t1 t2 addr offset words : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hdom : ∀ k, (k = addr ∨ k = offset ∨ (k ≠ t1 ∧ k ≠ t2 ∧ sptDomain live k)) →
      sptDomain (sptInsert addr () (sptInsert offset () (sptDelete t1 (sptDelete t2 live)))) k := by
    intro k hk
    rw [sptDomain_ins, sptDomain_ins, sptDomain_del, sptDomain_del]
    rcases hk with hk | hk | ⟨h1, h2, hk⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr ⟨h1, h2, hk⟩)
  rw [evaluate] at hev
  split at hev
  · rename_i a off ha ho
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · rename_i hc
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      have ha' := strongLocalsRelIGetVar addr _ st t tstore _
        ⟨ha, slrMono hl (fun k hk => hdom k (hk.elim Or.inl (Or.inr ∘ Or.inr)))⟩
      have ho' := strongLocalsRelIGetVar offset _ st t tstore _
        ⟨ho, slrMono hl (fun k hk => hdom k (hk.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)))⟩
      refine ⟨sptInsert addr (.word (a + wordSemBytesInWord * BitVec.ofNat width words.length))
          (sptInsert offset (.word off) (sptDelete t1 (sptDelete t2 t))), tstore, ?_, ?_, hs⟩
      · rw [evaluate]
        simp only [ha', ho']
        rw [if_neg hc]
        rfl
      · intro k v ⟨hk, hv⟩
        simp only [setVar, unsetVar] at hv
        simp only [id]
        by_cases hka : k = addr
        · subst hka; rw [sptLookup_sptInsert_same] at hv ⊢; exact hv
        · rw [sptLookup_sptInsert_ne _ _ _ _ hka] at hv ⊢
          by_cases hko : k = offset
          · subst hko; rw [sptLookup_sptInsert_same] at hv ⊢; exact hv
          · rw [sptLookup_sptInsert_ne _ _ _ _ hko] at hv ⊢
            rw [sptLookup_sptDelete, sptLookup_sptDelete] at hv ⊢
            by_cases h1 : k = t1
            · simp [h1] at hv
            · by_cases h2 : k = t2
              · simp [h2] at hv
              · simp only [h1, h2, if_false] at hv ⊢
                exact hl k v ⟨hdom k (Or.inr (Or.inr ⟨h1, h2, hk⟩)), hv⟩
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- HOL `evaluate_remove_dead`, `CodeBufferWrite` case (Resume 4376). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_CodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) :
    removeDeadGoal C F (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hdom : ∀ k, (k = r1 ∨ k = r2 ∨ sptDomain live k) →
      sptDomain (sptListInsert [r1, r2] live) k := by
    intro k hk
    rw [sptDomain_listIns]
    rcases hk with hk | hk | hk
    · exact Or.inl (by simp [hk])
    · exact Or.inl (by simp [hk])
    · exact Or.inr hk
  rw [evaluate] at hev
  split at hev
  · rename_i w1 w2 h1 h2
    have h1' := strongLocalsRelIGetVar r1 _ st t tstore _
      ⟨h1, slrMono hl (fun k hk => hdom k (hk.elim Or.inl (Or.inr ∘ Or.inr)))⟩
    have h2' := strongLocalsRelIGetVar r2 _ st t tstore _
      ⟨h2, slrMono hl (fun k hk => hdom k (hk.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)))⟩
    split at hev
    · rename_i cb hb
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      refine ⟨t, tstore, ?_, slrMono hl (fun k hk => hdom k (Or.inr (Or.inr hk))), hs⟩
      rw [evaluate]
      simp only [h1', h2']
      have hb' : wordSemBufferWrite ({ st with locals := t, store := tstore } :
          WordSemStateFiniteExact width C F).codeBuffer w1 (w2.setWidth 8) = some cb := hb
      rw [hb']
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- HOL `evaluate_remove_dead`, `DataBufferWrite` case (Resume 4393). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_DataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) :
    removeDeadGoal C F (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hdom : ∀ k, (k = r1 ∨ k = r2 ∨ sptDomain live k) →
      sptDomain (sptListInsert [r1, r2] live) k := by
    intro k hk
    rw [sptDomain_listIns]
    rcases hk with hk | hk | hk
    · exact Or.inl (by simp [hk])
    · exact Or.inl (by simp [hk])
    · exact Or.inr hk
  rw [evaluate] at hev
  split at hev
  · rename_i w1 w2 h1 h2
    have h1' := strongLocalsRelIGetVar r1 _ st t tstore _
      ⟨h1, slrMono hl (fun k hk => hdom k (hk.elim Or.inl (Or.inr ∘ Or.inr)))⟩
    have h2' := strongLocalsRelIGetVar r2 _ st t tstore _
      ⟨h2, slrMono hl (fun k hk => hdom k (hk.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)))⟩
    split at hev
    · rename_i db hb
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      refine ⟨t, tstore, ?_, slrMono hl (fun k hk => hdom k (Or.inr (Or.inr hk))), hs⟩
      rw [evaluate]
      simp only [h1', h2']
      have hb' : wordSemBufferWrite ({ st with locals := t, store := tstore } :
          WordSemStateFiniteExact width C F).dataBuffer w1 w2 = some db := hb
      rw [hb']
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- HOL `evaluate_remove_dead`, `Install` case (Resume 4352). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Install {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL) :
    removeDeadGoal C F (.install ptr len dptr dlen names : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hdom : ∀ k, (k ∈ [ptr, len, dptr, dlen] ∨ sptDomain names.1 k ∨ sptDomain names.2 k) →
      sptDomain (sptListInsert [ptr, len, dptr, dlen] (sptUnion names.1 names.2)) k := by
    intro k hk; rw [sptDomain_listIns, sptDomain_sptUnion]; exact hk
  have gv : ∀ x v, x ∈ [ptr, len, dptr, dlen] → getVar x st = some v →
      getVar x ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F) =
        some v :=
    fun x v hx h => hl x v ⟨hdom x (Or.inl hx), h⟩
  rw [evaluate] at hev
  split at hev
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · rename_i env hc
    have hc' : wordSemCutEnv names ({ st with locals := t, store := tstore } :
        WordSemStateFiniteExact width C F).locals = some env :=
      strongLocalsRelICutEnv names st t env ⟨slrMono hl (fun k hk => hdom k (Or.inr hk)), hc⟩
    split at hev
    · rename_i w1 w2 w3 w4 h1 h2 h3 h4
      have h1' := gv _ _ (by simp) h1
      have h2' := gv _ _ (by simp) h2
      have h3' := gv _ _ (by simp) h3
      have h4' := gv _ _ (by simp) h4
      rw [evaluate, hc']
      simp only [h1', h2', h3', h4']
      dsimp only at hev
      split at hev
      · rename_i bytes cb data db _ _
        split at hev
        · rename_i bytes' data' cfg' k _ _ _
          split at hev
          · rename_i hcond
            rw [if_pos hcond]
            simp only [Prod.mk.injEq] at hev
            obtain ⟨rfl, rfl⟩ := hev
            exact ⟨_, tstore, rfl, strongLocalsRelIdRefl _ _, hs⟩
          · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
        · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- HOL `evaluate_remove_dead`, `FFI` case (Resume 4410). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_FFI {width : Nat} [NeZero width] {C F : Type}
    (ffiIndex : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL) :
    removeDeadGoal C F (.ffi ffiIndex ptr1 len1 ptr2 len2 names :
      WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  simp only [removeDead, getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hdom : ∀ k, (k = ptr1 ∨ k = len1 ∨ k = ptr2 ∨ k = len2 ∨ sptDomain names.1 k ∨
      sptDomain names.2 k) →
      sptDomain (sptInsert ptr1 () (sptInsert len1 () (sptInsert ptr2 () (sptInsert len2 ()
        (sptUnion names.1 names.2))))) k := by
    intro k hk
    rw [sptDomain_ins, sptDomain_ins, sptDomain_ins, sptDomain_ins, sptDomain_sptUnion]
    exact hk
  have gv : ∀ x v, (x = ptr1 ∨ x = len1 ∨ x = ptr2 ∨ x = len2) → getVar x st = some v →
      getVar x ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F) =
        some v := by
    intro x v hx h
    refine hl x v ⟨hdom x ?_, h⟩
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  rw [evaluate] at hev
  split at hev
  · rename_i w1 w2 w3 w4 h1 h2 h3 h4
    have h1' := gv _ _ (Or.inr (Or.inl rfl)) h1
    have h2' := gv _ _ (Or.inl rfl) h2
    have h3' := gv _ _ (Or.inr (Or.inr (Or.inr rfl))) h3
    have h4' := gv _ _ (Or.inr (Or.inr (Or.inl rfl))) h4
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · rename_i env hc
      have hc' : wordSemCutEnv names ({ st with locals := t, store := tstore } :
          WordSemStateFiniteExact width C F).locals = some env :=
        strongLocalsRelICutEnv names st t env
          ⟨slrMono hl (fun k hk => hdom k (Or.inr (Or.inr (Or.inr (Or.inr hk))))), hc⟩
      rw [evaluate]
      simp only [h1', h2', h3', h4']
      rw [hc']
      split at hev
      · split at hev
        · simp only [Prod.mk.injEq] at hev
          obtain ⟨rfl, rfl⟩ := hev
          exact ⟨_, _, rfl, rfl, rfl⟩
        · simp only [Prod.mk.injEq] at hev
          obtain ⟨rfl, rfl⟩ := hev
          exact ⟨_, tstore, rfl, strongLocalsRelIdRefl _ _, hs⟩
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- A flat `ShareInst` address reads no store name (Flapjack infrastructure; HOL
unfolds `flat_exp_conventions_def` and `nlive_store_def` in its ShareInst case). -/
theorem flatShareInstNliveStore {width : Nat} [NeZero width] (nlive : List WordStoreHOL)
    (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (h : flatExpConventions (.shareInst op v exp : WordLangProgHOL (BitVec width)) = true) :
    nliveStore nlive exp := by
  cases exp with
  | var _ => simp [nliveStore]
  | op b ls =>
    unfold flatExpConventions at h
    split at h
    all_goals first
      | (simp at h; done)
      | (rename_i heq; simp only [WordLangProgHOL.shareInst.injEq, WordLangExpHOL.op.injEq] at heq
         obtain ⟨-, -, rfl, rfl⟩ := heq
         rw [nliveStore]
         rintro ⟨e, he⟩
         simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
         rcases he with rfl | rfl <;> simp [nliveStore])
      | (rename_i heq; simp at heq; done)
      | (exfalso; solve_by_elim)
  | _ => simp [flatExpConventions] at h

/-- The `sh_mem_set_var` step of a shared-memory load (Flapjack infrastructure for
HOL's ShareInst case, which unfolds `sh_mem_set_var_def`). -/
theorem shMemSetVarRemoveDead {width : Nat} [NeZero width] {C F : Type}
    (r : Option (HolFfiResult F)) (v : Nat) (live : NumSet) (nlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet)) (st : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
    (hl : strongLocalsRel id (sptDomain (sptDelete v live)) st.locals t)
    (hs : liveStoreRel nlive st.store tstore) (hev : shMemSetVar r v st = (res, rst))
    (herr : res ≠ some .error) :
    ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      shMemSetVar r v { st with locals := t, store := tstore } =
        (res, { rst with locals := t', store := tstore' }) ∧
      removeDeadPost live nlive lt res rst t' tstore' := by
  rcases r with _ | ⟨nf, nb⟩ | ⟨o⟩
  · simp only [shMemSetVar, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [shMemSetVar, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨sptInsert v _ t, tstore, rfl, slrSetVar live v _ _ _ hl, hs⟩
  · simp only [shMemSetVar, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨_, _, rfl, rfl, rfl⟩

/-- HOL `evaluate_remove_dead`, `ShareInst` case (Resume 4438). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_ShareInst {width : Nat} [NeZero width] {C F : Type} (op : WordMemOp)
    (v : Nat) (exp : WordLangExpHOL (BitVec width)) :
    removeDeadGoal C F (.shareInst op v exp : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  have hnl := flatShareInstNliveStore nlive op v exp hflat
  rw [evaluate] at hev
  split at hev
  · rename_i ad hw
    cases op
    all_goals simp only [removeDead, getLive, Prod.mk.injEq] at hrd
    all_goals obtain ⟨rfl, rfl, rfl⟩ := hrd
    all_goals simp only [reduceCtorEq, or_self, or_false, false_or, if_true, if_false] at hl
    all_goals have hw' := strongLocalsRelIWordExp t _ nlive tstore st exp _ ⟨hw, hl, hs, hnl⟩
    all_goals rw [evaluate, hw']
    all_goals simp only
    all_goals simp only [shareInst] at hev ⊢
    all_goals first
      | exact shMemSetVarRemoveDead _ v live nlive lt st t tstore res rst
          (slrMono hl (fun k hk => by rw [sptDomain_sptUnion]; exact Or.inr hk)) hs hev herr
      | split at hev
        · rename_i w hv
          have hv' : getVar v ({ st with locals := t, store := tstore } :
              WordSemStateFiniteExact width C F) = some (.word w) :=
            hl v _ ⟨by rw [sptDomain_sptUnion]; exact Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inl rfl)), hv⟩
          rw [hv']
          simp only [shMemStore, shMemStoreByte, shMemStore16, shMemStore32] at hev ⊢
          split at hev
          · rename_i hd
            rw [if_pos hd]
            split at hev
            all_goals simp only [Prod.mk.injEq] at hev
            all_goals obtain ⟨rfl, rfl⟩ := hev
            · exact ⟨_, _, rfl, rfl, rfl⟩
            · exact ⟨t, tstore, rfl, slrMono hl (fun k hk => by
                rw [sptDomain_sptUnion]; exact Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inr hk))), hs⟩
          · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
        · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

end Flapjack.WordAlloc
