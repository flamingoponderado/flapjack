import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
import Flapjack.Misc.SptreeLookup

/-!
# `evaluate_apply_colour` leaf cases

HOL `Resume evaluate_apply_colour[...]` blocks for the statements without
sub-programs (`word_allocProofScript.sml:1165-2268`). Each theorem is the HOL
theorem restricted to one constructor; none needs an induction hypothesis.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourLeafWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourLeafWitnesses

open EvaluateApplyColourLeafWitnesses

/-- Structure eta for the exact WordSem state, stated with the explicit
constructor so that it can rewrite a `with permute := st.permute` update. -/
theorem wordSemStateEta {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.mk st.locals st.localsSize st.fpRegs st.store st.stack st.stackLimit
      st.stackMax st.stackSize st.memory st.mdomain st.shMdomain st.permute st.compile
      st.compileOracle st.codeBuffer st.dataBuffer st.gcFun st.handler st.clock st.termdep
      st.code st.be st.ffi = st := rfl

theorem sptDomain_ins {α : Type} (n : Nat) (v : α) (t : Spt α) (k : Nat) :
    sptDomain (sptInsert n v t) k ↔ k = n ∨ sptDomain t k :=
  sptMem_sptInsert k n v t

theorem sptDomain_del {α : Type} (n : Nat) (t : Spt α) (k : Nat) :
    sptDomain (sptDelete n t) k ↔ k ≠ n ∧ sptDomain t k := by
  unfold sptDomain
  rw [sptLookup_sptDelete]
  by_cases h : k = n <;> simp [h]

theorem sptDomain_uni {α : Type} (a b : Spt α) (k : Nat) :
    sptDomain (sptUnion a b) k ↔ sptDomain a k ∨ sptDomain b k :=
  sptMem_sptUnion a b k

theorem sptDomain_ln {α : Type} (k : Nat) : ¬ sptDomain (Spt.ln : Spt α) k := by
  simp [sptDomain, sptLookup]

theorem sptOel_eq_getElem? {α : Type} : ∀ (k : Nat) (l : List α), sptOel k l = l[k]?
  | _, [] => by simp [sptOel]
  | 0, _ :: _ => by simp [sptOel]
  | k + 1, _ :: l => by simp [sptOel, sptOel_eq_getElem? k l]

/-- Restricting a live-scoped relation to a sub-predicate. -/
theorem slrMono {α : Type} {f : Nat → Nat} {A B : Nat → Prop} {s t : Spt α}
    (h : strongLocalsRel f A s t) (hAB : ∀ k, B k → A k) : strongLocalsRel f B s t :=
  fun k v hk => h k v ⟨hAB k hk.1, hk.2⟩

theorem wsrClock {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) : t.clock = s.clock := by
  unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wsrFlush {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (b : Bool) (h : wordStateEqRel s t) :
    wordStateEqRel (flushState b s) (flushState b t) := by
  cases b <;> simp_all [wordStateEqRel, flushState]

theorem wsrDecClock {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) :
    wordStateEqRel (decClock s) (decClock t) := by
  simp_all [wordStateEqRel, decClock]

theorem wsrLocals {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (a b : Spt (WordLocW width))
    (h : wordStateEqRel s t) :
    wordStateEqRel { s with locals := a } { t with locals := b } := by
  simp_all [wordStateEqRel]

theorem wsrStore {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) : t.store = s.store := by
  unfold wordStateEqRel at h; exact h.2.1

theorem wsrCode {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) : t.code = s.code := by
  unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wsrSetStore {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (n : WordStoreHOL) (w : WordLocW width)
    (h : wordStateEqRel s t) : wordStateEqRel (setStore n w s) (setStore n w t) := by
  simp_all [wordStateEqRel, setStore]

theorem wsrJumpExc {width : Nat} [NeZero width] {C F : Type}
    {s t s1 : WordSemStateFiniteExact width C F} {l1 l2 : Nat} (h : wordStateEqRel s t)
    (hj : jumpExc s = some (s1, l1, l2)) :
    ∃ t1, jumpExc t = some (t1, l1, l2) ∧ wordStateEqRel s1 t1 ∧ t1.locals = s1.locals := by
  have hstack : t.stack = s.stack := by unfold wordStateEqRel at h; exact h.2.2.2.1
  have hh : t.handler = s.handler := by unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.2.2.2.1
  unfold jumpExc at hj ⊢
  rw [hstack, hh]
  split at hj
  · rename_i hlt
    rw [if_pos hlt]
    split at hj
    · rename_i m e0 e n l1' l2' xs heq
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      refine ⟨_, rfl, ?_, rfl⟩
      simp_all [wordStateEqRel]
    · cases hj
  · cases hj

theorem wsrMemStore {width : Nat} [NeZero width] {C F : Type}
    {s t s1 : WordSemStateFiniteExact width C F} {a : BitVec width} {w : WordLocW width}
    (h : wordStateEqRel s t) (hm : memStore a w s = some s1) :
    ∃ t1, memStore a w t = some t1 ∧ wordStateEqRel s1 t1 ∧ s1.locals = s.locals ∧
      t1.locals = t.locals := by
  have hmd : t.mdomain = s.mdomain := by unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.1
  have hmem : t.memory = s.memory := by unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.1
  unfold memStore at hm ⊢
  rw [hmd, hmem]
  split at hm
  · rename_i hd
    rw [if_pos hd]
    simp only [Option.some.injEq] at hm
    subst hm
    refine ⟨_, rfl, ?_, rfl, rfl⟩
    simp_all [wordStateEqRel]
  · cases hm

theorem sptDomain_listIns (keys : List Nat) (t : NumSet) (k : Nat) :
    sptDomain (sptListInsert keys t) k ↔ k ∈ keys ∨ sptDomain t k := by
  induction keys generalizing t with
  | nil => simp [sptListInsert]
  | cons x xs ih =>
      simp only [sptListInsert, ih, sptDomain_ins, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem sptDomain_numsetIns (keys : List Nat) (t : NumSet) (k : Nat) :
    sptDomain (numsetListInsert keys t) k ↔ sptDomain t k ∨ k ∈ keys := by
  rw [domainNumsetListInsert]

/-- HOL `evaluate_apply_colour`, `Skip` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Skip {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.skip : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.skip : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.skip : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro _
  simp only [applyColour]
  rw [evaluate, evaluate]
  exact ⟨rfl, hs, by simpa [getLive, applyColourLocals] using hr⟩

/-- HOL `evaluate_apply_colour`, `Tick` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Tick {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.tick : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.tick : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.tick : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro _
  simp only [applyColour]
  have hclk := wsrClock hs
  rw [evaluate, evaluate]
  by_cases hz : st.clock = 0
  · rw [if_pos hz, if_pos (hclk.trans hz)]
    exact ⟨rfl, wsrFlush true hs, rfl⟩
  · rw [if_neg hz, if_neg (fun h => hz (hclk ▸ h))]
    exact ⟨rfl, wsrDecClock hs, by simpa [getLive, applyColourLocals, decClock] using hr⟩

/-- HOL `evaluate_apply_colour`, `Break` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Break {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.break k : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.break k : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.break k : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro _
  simp only [applyColour]
  rw [evaluate, evaluate]
  refine ⟨rfl, hs, ?_⟩
  simp only [applyColourLocals, sptOel_eq_getElem?]
  simp only [getLive] at hr
  cases ho : lt[k]? with
  | none => trivial
  | some e => obtain ⟨names, exitNames⟩ := e; simpa [ho] using hr

/-- HOL `evaluate_apply_colour`, `Continue` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Continue {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.continue k : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.continue k : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.continue k : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro _
  simp only [applyColour]
  rw [evaluate, evaluate]
  refine ⟨rfl, hs, ?_⟩
  simp only [applyColourLocals, sptOel_eq_getElem?]
  simp only [getLive] at hr
  cases ho : lt[k]? with
  | none => trivial
  | some e => obtain ⟨names, exitNames⟩ := e; simpa [ho] using hr

/-- Colouring injectivity on `n INSERT live` from the catch-all `colouring_ok`
clause for a statement writing exactly `n`. -/
theorem injInsertOfIset {f : Nat → Nat} {n : Nat} {live : NumSet}
    (h : ∀ a b, sptDomain (sptUnion (sptInsert n () .ln) live) a →
      sptDomain (sptUnion (sptInsert n () .ln) live) b → f a = f b → a = b) :
    ∀ a b, (a = n ∨ sptDomain live a) → (b = n ∨ sptDomain live b) → f a = f b → a = b := by
  intro a b ha hb hab
  refine h a b ?_ ?_ hab
  · rw [sptDomain_uni, sptDomain_ins]; rcases ha with ha | ha
    · exact Or.inl (Or.inl ha)
    · exact Or.inr ha
  · rw [sptDomain_uni, sptDomain_ins]; rcases hb with hb | hb
    · exact Or.inl (Or.inl hb)
    · exact Or.inr hb

/-- HOL `evaluate_apply_colour`, `Assign` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Assign {width : Nat} [NeZero width] {C F : Type} (v : Nat)
    (exp : WordLangExpHOL (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.assign v exp : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.assign v exp : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.assign v exp : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getWrites, getLive] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  cases hw : wordExp st exp with
  | none => rw [hw] at he; exact absurd rfl he
  | some w =>
      have hcw := applyColourExpLemma st exp cst f w
        ⟨hw, hs, slrMono hr (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inl hk))⟩
      rw [hcw]
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      refine strongLocalsRelInsert f v _ _ _ w ⟨injInsertOfIset hok.2, ?_⟩
      exact slrMono hr (fun k hk => (sptDomain_uni _ _ k).mpr
        (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))

/-- HOL `evaluate_apply_colour`, `Get` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Get {width : Nat} [NeZero width] {C F : Type} (v : Nat)
    (name : WordStoreHOL) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.get v name : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.get v name : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.get v name : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getWrites, getLive] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hgs : getStore name cst = getStore name st := by simp only [getStore, wsrStore hs]
  rw [hgs]
  cases hw : getStore name st with
  | none => rw [hw] at he; exact absurd rfl he
  | some w =>
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      refine strongLocalsRelInsert f v _ _ _ w ⟨injInsertOfIset hok.2, ?_⟩
      exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)

/-- HOL `evaluate_apply_colour`, `Set` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Set {width : Nat} [NeZero width] {C F : Type} (v : WordStoreHOL)
    (exp : WordLangExpHOL (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.set v exp : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.set v exp : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.set v exp : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  by_cases hv : v = .handler ∨ v = .bitmapBase
  · rw [if_pos hv] at he; exact absurd rfl he
  rw [if_neg hv] at he ⊢
  rw [if_neg hv]
  cases hw : wordExp st exp with
  | none => rw [hw] at he; exact absurd rfl he
  | some w =>
      have hcw := applyColourExpLemma st exp cst f w
        ⟨hw, hs, slrMono hr (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inl hk))⟩
      rw [hcw]
      refine ⟨rfl, wsrSetStore v w hs, ?_⟩
      simp only [applyColourLocals, setStore]
      exact slrMono hr (fun k hk => (sptDomain_uni _ _ k).mpr (Or.inr hk))

/-- HOL `evaluate_apply_colour`, `LocValue` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_LocValue {width : Nat} [NeZero width] {C F : Type} (r l1 : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.locValue r l1 : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.locValue r l1 : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.locValue r l1 : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getWrites, getLive] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hc : sptMem l1 cst.code ↔ sptMem l1 st.code := by rw [wsrCode hs]
  by_cases hm : sptMem l1 st.code
  · rw [if_pos hm, if_pos (hc.mpr hm)]
    refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
    simp only [applyColourLocals, setVar]
    refine strongLocalsRelInsert f r _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
    exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)
  · rw [if_neg hm] at he; exact absurd rfl he

/-- HOL `evaluate_apply_colour`, `Raise` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Raise {width : Nat} [NeZero width] {C F : Type} (n : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.raise n : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.raise n : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.raise n : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  cases hw : getVar n st with
  | none => rw [hw] at he; exact absurd rfl he
  | some w =>
      have hcw := strongLocalsRelGetVar f _ st cst n w
        ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hw⟩
      rw [hcw]
      rw [hw] at he
      cases hje : jumpExc st with
      | none => rw [hje] at he; exact absurd rfl he
      | some p =>
          obtain ⟨s1, l1, l2⟩ := p
          obtain ⟨t1, ht1, hst, hloc⟩ := wsrJumpExc hs hje
          rw [ht1]
          exact ⟨rfl, hst, hloc.symm⟩

/-- HOL `evaluate_apply_colour`, `Store` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Store {width : Nat} [NeZero width] {C F : Type}
    (exp : WordLangExpHOL (BitVec width)) (v : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.store exp v : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.store exp v : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.store exp v : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  cases hw : wordExp st exp with
  | none => rw [hw] at he; exact absurd rfl he
  | some x =>
    cases x with
    | loc _ _ => rw [hw] at he; exact absurd rfl he
    | word a =>
      cases hv : getVar v st with
      | none => rw [hw, hv] at he; exact absurd rfl he
      | some w =>
        have hcw := applyColourExpLemma st exp cst f (.word a)
          ⟨hw, hs, slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_uni _ _ k).mpr (Or.inl hk))))⟩
        have hcv := strongLocalsRelGetVar f _ st cst v w
          ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hv⟩
        rw [hcw, hcv]
        rw [hw, hv] at he
        simp only at he
        cases hm : memStore a w st with
        | none => rw [hm] at he; exact absurd rfl he
        | some s1 =>
          obtain ⟨t1, ht1, hst, hl1, hl2⟩ := wsrMemStore hs hm
          dsimp only
          rw [ht1, hm]
          refine ⟨rfl, hst, ?_⟩
          simp only [applyColourLocals, hl1, hl2]
          exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_uni _ _ k).mpr (Or.inr hk))))

/-- HOL `evaluate_apply_colour`, `Return` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Return {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (ms : List Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.return n ms : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.return n ms : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.return n ms : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  cases hw : getVar n st with
  | none => rw [hw] at he; exact absurd rfl he
  | some x =>
    have hcw := strongLocalsRelGetVar f _ st cst n x
      ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hw⟩
    rw [hcw]
    cases x with
    | word _ => rw [hw] at he; exact absurd rfl he
    | loc l1 l2 =>
      cases hvs : WordSemStateFiniteExact.getVars ms st with
      | none => rw [hw, hvs] at he; exact absurd rfl he
      | some ys =>
        have hcvs := strongLocalsRelGetVars ms ys f _ st cst
          ⟨hr, fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_numsetIns _ _ k).mpr (Or.inr hk))), hvs⟩
        rw [hcvs]
        exact ⟨rfl, wsrFlush false hs, rfl⟩

/-- HOL `evaluate_apply_colour`, `CodeBufferWrite` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_CodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hcb : cst.codeBuffer = st.codeBuffer := by
    unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases h1 : getVar r1 st with
  | none => rw [h1] at he; exact absurd rfl he
  | some x1 =>
    cases h2 : getVar r2 st with
    | none => rw [h1, h2] at he; cases x1 <;> exact absurd rfl he
    | some x2 =>
      have hc1 := strongLocalsRelGetVar f _ st cst r1 x1
        ⟨hr, (sptDomain_listIns _ _ _).mpr (Or.inl (by simp)), h1⟩
      have hc2 := strongLocalsRelGetVar f _ st cst r2 x2
        ⟨hr, (sptDomain_listIns _ _ _).mpr (Or.inl (by simp)), h2⟩
      rw [hc1, hc2]
      rw [h1, h2] at he
      cases x1 with
      | loc _ _ => exact absurd rfl he
      | word w1 =>
        cases x2 with
        | loc _ _ => exact absurd rfl he
        | word w2 =>
          simp only at he ⊢
          rw [hcb]
          cases hb : wordSemBufferWrite st.codeBuffer w1 (w2.setWidth 8) with
          | none => rw [hb] at he; exact absurd rfl he
          | some nb =>
            refine ⟨rfl, ?_, ?_⟩
            · simp_all [wordStateEqRel]
            · exact slrMono hr (fun k hk => (sptDomain_listIns _ _ _).mpr (Or.inr hk))

/-- HOL `evaluate_apply_colour`, `DataBufferWrite` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_DataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [getLive] at hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hdb : cst.dataBuffer = st.dataBuffer := by
    unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  cases h1 : getVar r1 st with
  | none => rw [h1] at he; exact absurd rfl he
  | some x1 =>
    cases h2 : getVar r2 st with
    | none => rw [h1, h2] at he; cases x1 <;> exact absurd rfl he
    | some x2 =>
      have hc1 := strongLocalsRelGetVar f _ st cst r1 x1
        ⟨hr, (sptDomain_listIns _ _ _).mpr (Or.inl (by simp)), h1⟩
      have hc2 := strongLocalsRelGetVar f _ st cst r2 x2
        ⟨hr, (sptDomain_listIns _ _ _).mpr (Or.inl (by simp)), h2⟩
      rw [hc1, hc2]
      rw [h1, h2] at he
      cases x1 with
      | loc _ _ => exact absurd rfl he
      | word w1 =>
        cases x2 with
        | loc _ _ => exact absurd rfl he
        | word w2 =>
          simp only at he ⊢
          rw [hdb]
          cases hb : wordSemBufferWrite st.dataBuffer w1 w2 with
          | none => rw [hb] at he; exact absurd rfl he
          | some nb =>
            refine ⟨rfl, ?_, ?_⟩
            · simp_all [wordStateEqRel]
            · exact slrMono hr (fun k hk => (sptDomain_listIns _ _ _).mpr (Or.inr hk))

/-- HOL `evaluate_apply_colour`, `OpCurrHeap` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_OpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (b : BinOp) (dst src : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getWrites, getLive] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hexp : (WordLangExpHOL.op b [.var (f src), .lookup .currHeap] : WordLangExpHOL (BitVec width)) =
      applyColourExp f (.op b [.var src, .lookup .currHeap]) := by
    simp [applyColourExp, applyColourExpCore]
  rw [hexp]
  cases hw : wordExp st (.op b [.var src, .lookup .currHeap]) with
  | none => rw [hw] at he; exact absurd rfl he
  | some w =>
      have hlive : ∀ k, sptDomain (getLiveExp (.op b [.var src, .lookup .currHeap] :
          WordLangExpHOL (BitVec width))) k → k = src := by
        intro k hk
        simp only [getLiveExp, bigUnion, List.map, List.foldr, sptDomain_uni, sptDomain_ins] at hk
        rcases hk with (hk | hk) | hk | hk
        · exact hk
        · exact absurd hk (sptDomain_ln k)
        · exact absurd hk (sptDomain_ln k)
        · exact absurd hk (sptDomain_ln k)
      have hcw := applyColourExpLemma st _ cst f w
        ⟨hw, hs, slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr (Or.inl (hlive k hk)))⟩
      rw [hcw]
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      refine strongLocalsRelInsert f dst _ _ _ w ⟨injInsertOfIset hok.2, ?_⟩
      exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
        (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))

end Flapjack.WordAlloc
