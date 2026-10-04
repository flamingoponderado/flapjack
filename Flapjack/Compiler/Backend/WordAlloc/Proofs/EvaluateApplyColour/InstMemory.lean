import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace InstMemoryWitnesses

/-- Imported canonical finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstMemoryWitnesses

/-- Local state-field projection infrastructure, not a separate HOL port. -/
private theorem memoryFields {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) :
    t.memory = s.memory ∧ t.mdomain = s.mdomain ∧ t.be = s.be := by
  simp only [wordStateEqRel] at h
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- HOL `evaluate_apply_colour[Inst]`, Load memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstLoad {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .load reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .load reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .load reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr haddr
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hm : memLoad addr cst = memLoad addr st := by
        obtain ⟨hm, hd, hb⟩ := memoryFields hs
        simp only [memLoad, hm, hd]
      rw [hm]
      split at hinst
      · cases hinst
      · rename_i value hload
        cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f reg _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
          (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Load8 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstLoad8 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .load8 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .load8 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .load8 reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr haddr
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hm : memLoadByteAuxExact cst.memory cst.mdomain cst.be addr = memLoadByteAuxExact st.memory st.mdomain st.be addr := by
        obtain ⟨hm, hd, hb⟩ := memoryFields hs
        rw [hm, hd, hb]
      rw [hm]
      split at hinst
      · cases hinst
      · rename_i value hload
        cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f reg _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
          (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Load32 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstLoad32 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .load32 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .load32 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .load32 reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr haddr
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hm : memLoad32Exact cst.memory cst.mdomain cst.be addr = memLoad32Exact st.memory st.mdomain st.be addr := by
        obtain ⟨hm, hd, hb⟩ := memoryFields hs
        rw [hm, hd, hb]
      rw [hm]
      split at hinst
      · cases hinst
      · rename_i value hload
        cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f reg _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
          (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Load16 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstLoad16 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .load16 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .load16 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .load16 reg (.addr base offset))) live lt st cst := by
  intro st cst f live lt _
  apply applyColourPost_self
  intro he
  rw [evaluate] at he
  simp only [inst] at he
  exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Store16 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstStore16 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .store16 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .store16 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .store16 reg (.addr base offset))) live lt st cst := by
  intro st cst f live lt _
  apply applyColourPost_self
  intro he
  rw [evaluate] at he
  simp only [inst] at he
  exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Store memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstStore {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .store reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .store reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .store reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr value haddr hvar
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hv := strongLocalsRelGetVar f _ st cst reg value
        ⟨hr, by simp [sptDomain_ins], hvar⟩
      rw [hv]
      dsimp only
      split at hinst
      · rename_i s1 hstore
        obtain ⟨t1, ht1, hst, hl1, hl2⟩ := wsrMemStore hs hstore
        rw [ht1]
        cases hinst
        dsimp only
        refine ⟨rfl, hst, ?_⟩
        simp only [applyColourLocals, hl1, hl2]
        exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
          (Or.inr ((sptDomain_ins _ _ _ k).mpr (Or.inr hk))))
      · cases hinst
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Store8 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstStore8 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .store8 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .store8 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .store8 reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr value haddr hvar
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hv := strongLocalsRelGetVar f _ st cst reg (.word value)
        ⟨hr, by simp [sptDomain_ins], hvar⟩
      rw [hv]
      dsimp only
      have hm : memStoreByteAuxExact cst.memory cst.mdomain cst.be addr (value.setWidth 8) =
          memStoreByteAuxExact st.memory st.mdomain st.be addr (value.setWidth 8) := by
        obtain ⟨hm, hd, hb⟩ := memoryFields hs
        rw [hm, hd, hb]
      rw [hm]
      split at hinst
      · rename_i memory hstore
        cases hinst
        dsimp only
        refine ⟨rfl, ?_, ?_⟩
        · simp_all [wordStateEqRel]
        · exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_ins _ _ _ k).mpr (Or.inr hk))))
      · cases hinst
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, Store32 memory subcase.
Literal source clauses and original three premises/full existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_InstStore32 {width : Nat} [NeZero width] {C F : Type}
    (reg base : Nat) (offset : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.mem .store32 reg (.addr base offset))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.mem .store32 reg (.addr base offset))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.mem .store32 reg (.addr base offset))) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i addr value haddr hvar
      have hc := applyColourExpLemma st (.op .add [.var base, .const offset]) cst f (.word addr)
        ⟨haddr, hs, slrMono hr (by
          intro k hk
          simp [getLiveExp, bigUnion, sptDomain_ins, sptDomain_uni, sptDomain_ln] at hk
          subst k
          simp [sptDomain_ins])⟩
      simp only [applyColourExp, applyColourExpCore, List.map_cons, List.map_nil] at hc
      rw [hc]
      dsimp only
      have hv := strongLocalsRelGetVar f _ st cst reg (.word value)
        ⟨hr, by simp [sptDomain_ins], hvar⟩
      rw [hv]
      dsimp only
      have hm : memStore32Exact cst.memory cst.mdomain cst.be addr (value.setWidth 32) =
          memStore32Exact st.memory st.mdomain st.be addr (value.setWidth 32) := by
        obtain ⟨hm, hd, hb⟩ := memoryFields hs
        rw [hm, hd, hb]
      rw [hm]
      split at hinst
      · rename_i memory hstore
        cases hinst
        dsimp only
        refine ⟨rfl, ?_, ?_⟩
        · simp_all [wordStateEqRel]
        · exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_ins _ _ _ k).mpr (Or.inr hk))))
      · cases hinst
    · cases hinst
  · exact absurd rfl he

end Flapjack.WordAlloc
