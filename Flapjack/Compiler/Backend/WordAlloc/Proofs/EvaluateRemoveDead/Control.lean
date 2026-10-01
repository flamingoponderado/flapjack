import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Loop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Store

/-!
# `evaluate_remove_dead` control cases

The `Seq`, `MustTerminate`, `If` and `Loop` cases of `word_allocProofScript.sml:3900-4472`
`evaluate_remove_dead` (Resume blocks 4137, 4157, 4170, 4281). Each takes the
statement for its sub-programs as induction hypotheses; `Loop` is
`evaluate_remove_dead_Loop_helper` at the body statement.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadControlWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadControlWitnesses

/-- Only the `NONE` branch of the post-condition reads the live sets (Flapjack
infrastructure). -/
theorem removeDeadPost_some {width : Nat} [NeZero width] {C F : Type} (a a' : NumSet)
    (b b' : List WordStoreHOL) (lt : List (NumSet × NumSet)) (r : WordSemResult width)
    (rst : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    removeDeadPost a b lt (some r) rst t ts ↔ removeDeadPost a' b' lt (some r) rst t ts := by
  cases r <;> exact Iff.rfl

/-- The post-condition reads only the locals and store of the source result state
(Flapjack infrastructure). -/
theorem removeDeadPost_clock {width : Nat} [NeZero width] {C F : Type} (live : NumSet)
    (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) (res : Option (WordSemResult width))
    (s : WordSemStateFiniteExact width C F) (c d : Nat) (t : Spt (WordLocW width))
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    removeDeadPost live nlive lt res { s with clock := c, termdep := d } t ts ↔
      removeDeadPost live nlive lt res s t ts := by
  cases res with
  | none => exact Iff.rfl
  | some r => cases r <;> exact Iff.rfl

/-- HOL `evaluate_remove_dead`, `Seq` case (Resume 4137). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Seq {width : Nat} [NeZero width] {C F : Type}
    (s1 s2 : WordLangProgHOL (BitVec width)) (ih1 : removeDeadGoal C F s1)
    (ih2 : removeDeadGoal C F s2) :
    removeDeadGoal C F (.seq s1 s2) := by
  have hseq := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hflat
  rw [removeDead] at hrd
  rcases h2 : removeDead s2 live nlive lt with ⟨s2', l2, n2⟩
  rw [h2] at hrd
  dsimp only at hrd
  rcases h1 : removeDead s1 l2 n2 lt with ⟨s1', l1, n1⟩
  rw [h1] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨hp, rfl, rfl⟩ := hrd
  subst hp
  rw [hseq] at hev
  rcases he1 : evaluate s1 st with ⟨r1, st1⟩
  rw [he1] at hev
  dsimp only at hev
  have herr1 : r1 ≠ some .error := by
    rintro rfl; simp only [Prod.mk.injEq] at hev; exact herr hev.1.symm
  obtain ⟨t1, ts1, hT1, hp1⟩ := ih1 l2 n2 lt s1' l1 n1 st t tstore r1 st1
    ⟨hl, hs, he1, hflat.1, h1, herr1⟩
  cases r1 with
  | none =>
    obtain ⟨hl1, hs1⟩ := hp1
    obtain ⟨t2, ts2, hT2, hp2⟩ := ih2 live nlive lt s2' l2 n2 st1 t1 ts1 res rst
      ⟨hl1, hs1, hev, hflat.2, h2, herr⟩
    refine ⟨t2, ts2, ?_, hp2⟩
    split
    · rw [evaluate] at hT1
      simp only [Prod.mk.injEq] at hT1
      rw [hT1.2]; exact hT2
    · rename_i hn
      rw [evaluate] at hT2
      simp only [Prod.mk.injEq] at hT2
      obtain ⟨rfl, h⟩ := hT2
      rw [hT1, h]
    · rw [hseq, hT1]; exact hT2
  | some r =>
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    refine ⟨t1, ts1, ?_, (removeDeadPost_some l2 live n2 nlive lt r _ _ _).mp hp1⟩
    split
    · rw [evaluate] at hT1; simp only [Prod.mk.injEq] at hT1; cases hT1.1
    · exact hT1
    · rw [hseq, hT1]

/-- HOL `evaluate_remove_dead`, `MustTerminate` case (Resume 4157). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_MustTerminate {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (ih : removeDeadGoal C F p) :
    removeDeadGoal C F (.mustTerminate p) := by
  have hmt := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions] at hflat
  rw [removeDead] at hrd
  rcases hp : removeDead p live nlive lt with ⟨p', l1, n1⟩
  rw [hp] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rw [hmt] at hev
  by_cases hz : st.termdep = 0
  · simp only [hz, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [hz, if_false] at hev
    generalize hst' :
      ({ st with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 } :
        WordSemStateFiniteExact width C F) = st' at hev
    rcases hb : evaluate p st' with ⟨r, s1⟩
    rw [hb] at hev
    dsimp only at hev
    have herr' : r ≠ some .error := by
      rintro rfl; simp only [Prod.mk.injEq] at hev; exact herr hev.1.symm
    have hto : r ≠ some .timeOut := by
      rintro rfl; simp only [Prod.mk.injEq] at hev; exact herr hev.1.symm
    obtain ⟨t', ts', hT, hpost⟩ := ih live nlive lt p' l1 n1 st' t tstore r s1
      ⟨by rw [← hst']; exact hl, by rw [← hst']; exact hs, hb, hflat, hp, herr'⟩
    subst hst'
    have hev' : (r, { s1 with clock := st.clock, termdep := st.termdep }) = (res, rst) := by
      cases r with
      | none => exact hev
      | some x => cases x <;> first | exact hev | exact absurd rfl hto
    simp only [Prod.mk.injEq] at hev'
    obtain ⟨rfl, rfl⟩ := hev'
    refine ⟨t', ts', ?_, (removeDeadPost_clock _ _ _ _ _ _ _ _ _).mpr hpost⟩
    rw [hmt]
    have hz' : ¬ ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F).termdep = 0 := hz
    simp only [hz', if_false]
    have hT' : evaluate p'
        ({ ({ st with locals := t, store := tstore } : WordSemStateFiniteExact width C F) with
          clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 } :
          WordSemStateFiniteExact width C F) =
        (r, { s1 with locals := t', store := ts' }) := hT
    rw [hT']
    cases r with
    | none => rfl
    | some x => cases x <;> first | rfl | exact absurd rfl hto

/-- HOL `evaluate_remove_dead`, `If` case (Resume 4170). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_If {width : Nat} [NeZero width] {C F : Type} (cmp : Cmp) (r1 : Nat)
    (ri : WordRegImm (BitVec width)) (e2 e3 : WordLangProgHOL (BitVec width))
    (ih2 : removeDeadGoal C F e2) (ih3 : removeDeadGoal C F e3) :
    removeDeadGoal C F (.ite cmp r1 ri e2 e3) := by
  have hite := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hflat
  rw [removeDead] at hrd
  rcases h2 : removeDead e2 live nlive lt with ⟨e2', l2, n2⟩
  rcases h3 : removeDead e3 live nlive lt with ⟨e3', l3, n3⟩
  rw [h2, h3] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨hp, rfl, rfl⟩ := hrd
  subst hp
  -- the union of the branch live sets lies inside the If's live set
  have hsub : ∀ k, sptDomain l2 k ∨ sptDomain l3 k →
      sptDomain (match ri with
        | .reg r2 => sptInsert r2 () (sptInsert r1 () (sptUnion l2 l3))
        | _ => sptInsert r1 () (sptUnion l2 l3)) k := by
    intro k hk
    cases ri <;> simp only [sptDomain_ins, sptDomain_sptUnion] <;> simp [hk]
  have hr1 : sptDomain (match ri with
        | .reg r2 => sptInsert r2 () (sptInsert r1 () (sptUnion l2 l3))
        | _ => sptInsert r1 () (sptUnion l2 l3)) r1 := by
    cases ri <;> simp only [sptDomain_ins] <;> simp
  have hl2 : strongLocalsRel id (sptDomain l2) st.locals t :=
    fun k v ⟨hk, hv⟩ => hl k v ⟨hsub k (Or.inl hk), hv⟩
  have hl3 : strongLocalsRel id (sptDomain l3) st.locals t :=
    fun k v ⟨hk, hv⟩ => hl k v ⟨hsub k (Or.inr hk), hv⟩
  have hs2 : liveStoreRel n2 st.store tstore :=
    liveStoreRelLess _ _ _ _ ⟨hs, filterSub _ _⟩
  have hs3 : liveStoreRel n3 st.store tstore :=
    liveStoreRelLess _ _ _ _ ⟨hs, fun x hx => by simpa using (List.mem_filter.mp hx).2⟩
  rw [hite] at hev
  cases hx : getVar r1 st with
  | none => rw [hx] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some x =>
    cases hy : WordSemStateFiniteExact.getVarImm ri st with
    | none => rw [hx, hy] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    | some y =>
      rw [hx, hy] at hev
      dsimp only at hev
      have htx : getVar r1 { st with locals := t, store := tstore } = some x :=
        hl r1 x ⟨hr1, hx⟩
      have hty : WordSemStateFiniteExact.getVarImm ri { st with locals := t, store := tstore } =
          some y := by
        cases ri with
        | reg r2 =>
          simp only [WordSemStateFiniteExact.getVarImm] at hy ⊢
          exact hl r2 y ⟨by simp only [sptDomain_ins]; simp, hy⟩
        | imm w => simpa [WordSemStateFiniteExact.getVarImm] using hy
      cases hc : wordSemWordCmp cmp x y with
      | none => rw [hc] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      | some b =>
        rw [hc] at hev
        cases b with
        | true =>
          obtain ⟨t', ts', hT, hpost⟩ := ih2 live nlive lt e2' l2 n2 st t tstore res rst
            ⟨hl2, hs2, hev, hflat.1, h2, herr⟩
          refine ⟨t', ts', ?_, hpost⟩
          split
          · rw [evaluate] at hT
            rw [evaluate]; exact hT
          · rw [hite, htx, hty]; dsimp only; rw [hc]; exact hT
        | false =>
          obtain ⟨t', ts', hT, hpost⟩ := ih3 live nlive lt e3' l3 n3 st t tstore res rst
            ⟨hl3, hs3, hev, hflat.2, h3, herr⟩
          refine ⟨t', ts', ?_, hpost⟩
          split
          · rw [evaluate] at hT
            rw [evaluate]; exact hT
          · rw [hite, htx, hty]; dsimp only; rw [hc]; exact hT

/-- HOL `evaluate_remove_dead`, `Loop` case (Resume 4281): the Loop helper at the
body statement for the loop's own context. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Loop {width : Nat} [NeZero width] {C F : Type} (names : NumSet)
    (body : WordLangProgHOL (BitVec width)) (exitNames : NumSet) (ih : removeDeadGoal C F body) :
    removeDeadGoal C F (.loop names body exitNames) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions] at hflat
  have hnl : nlivein = [] := by
    rw [removeDead_loop] at hrd
    simp only [Prod.mk.injEq] at hrd
    exact hrd.2.2.symm
  exact evaluateRemoveDeadLoopHelper st t tstore names body exitNames live nlive lt prog' livein
    nlivein res rst ⟨hl, hs, hev, hflat, hrd, hnl, herr,
      fun st' t' ts' p'' l' n' r' rs' ⟨a, b, c, d, e⟩ =>
        ih names [] ((names, exitNames) :: lt) p'' l' n' st' t' ts' r' rs' ⟨a, b, c, hflat, d, e⟩⟩

end Flapjack.WordAlloc
