module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateConst
public import Flapjack.Compiler.Backend.WordElim.Proofs.Stacks
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConstFull
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcConst
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.AllocConst
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.JumpExcConst

@[expose] public section

/-!
# `word_state_rel` lemmas of HOL `word_elimProof`

Counterpart of the WORD STATE REL section of
`cakeml/compiler/backend/proofs/word_elimProofScript.sml` (lines 532-930).
HOL's `domain A ⊆ domain B` is `sptDomainSet A ⊆ sptDomainSet B`, and
`BIGUNION (set (MAP f l))` is `⋃₀ {S | S ∈ l.map f}`.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack WordSemStateFiniteExact

namespace WordElimStateRelSupport
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordElimStateRelSupport


/-- Exact HOL `word_state_rel_get_var` (`word_elimProofScript.sml:534-539`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_get_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_get_var {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {v : Nat} : wordStateRel reachable s t → t.getVar v = s.getVar v := by
  intro h
  simp only [getVar, h.1]

/-- Exact HOL `word_state_rel_get_store` (`word_elimProofScript.sml:541-546`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_get_store"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_get_store {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {v : WordStoreHOL} : wordStateRel reachable s t →
      WordSemStateFiniteExact.getStore v t = WordSemStateFiniteExact.getStore v s := by
  intro h
  simp only [WordSemStateFiniteExact.getStore, h.2.2.1]

/-- Exact HOL `word_state_rel_get_vars` (`word_elimProofScript.sml:548-554`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_get_vars"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_get_vars {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {vs : List Nat} : wordStateRel reachable s t → t.getVars vs = s.getVars vs := by
  intro h
  exact getVars_congr s t h.1 vs

/-- Exact HOL `word_state_rel_set_var` (`word_elimProofScript.sml:556-569`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_set_var {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {v : WordLocW width} {n : Nat} :
    wordStateRel reachable s t ∧
        (match destWordLoc v with | none => (∅ : Set Nat) | some n => {n}) ⊆
          sptDomainSet reachable →
      wordStateRel reachable (s.setVar n v) (t.setVar n v) := by
  rintro ⟨h, hv⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, hcode, hdom⟩ := h
  refine ⟨by simp [setVar, h1], h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, hcode, ?_⟩
  intro m hm
  have hm' : m ∈ sptDomainSet (findLocState (s.setVar n v)) := hm
  rw [domain_find_loc_state] at hm'
  have hfull : m ∈ sptDomainSet (findLocState s) → sptMem m reachable := hdom m
  rw [show sptMem m reachable ↔ m ∈ sptDomainSet reachable from Iff.rfl]
  simp only [setVar, Set.mem_union] at hm'
  rcases hm' with ((hl | hs) | hk) | hmem
  · rcases getLocals_insert n v s.locals hl with hl' | hl'
    · exact hfull (by rw [domain_find_loc_state]; exact Or.inl (Or.inl (Or.inl hl')))
    · exact hv hl'
  · exact hfull (by rw [domain_find_loc_state]; exact Or.inl (Or.inl (Or.inr hs)))
  · exact hfull (by rw [domain_find_loc_state]; exact Or.inl (Or.inr hk))
  · exact hfull (by rw [domain_find_loc_state]; exact Or.inr hmem)

/-- Exact HOL `word_state_rel_set_var_word` (`word_elimProofScript.sml:572-579`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_set_var_word"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_set_var_word {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {n : Nat} {w : BitVec width} :
    wordStateRel reachable s t →
      wordStateRel reachable (s.setVar n (.word w)) (t.setVar n (.word w)) := by
  intro h
  exact word_state_rel_set_var ⟨h, by simp [destWordLoc]⟩

/-- Exact HOL `word_state_rel_set_fp_var` (`word_elimProofScript.sml:603-611`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_set_fp_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_set_fp_var {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {n : Nat} {v : BitVec 64} :
    wordStateRel reachable s t →
      wordStateRel reachable (s.setFpVar n v) (t.setFpVar n v) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, hcode, hdom⟩ := h
  exact ⟨h1, by simp [setFpVar, h2], h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, hcode, hdom⟩

/-- Exact HOL `word_state_rel_word_exp` (`word_elimProofScript.sml:613-625`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_word_exp {width : Nat} [NeZero width] {C F : Type}
    :
    ∀ (s1 : WordSemStateFiniteExact width C F) (exp : WordLangExpHOL (BitVec width))
      (s2 : WordSemStateFiniteExact width C F) (reachable : NumSet),
      wordStateRel reachable s1 s2 → s2.wordExp exp = s1.wordExp exp := by
  intro s1 exp s2 reachable h
  exact wordExp_congr s1 s2 h.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 exp

/-- Exact HOL `word_state_rel_mem_load` (`word_elimProofScript.sml:627-632`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_mem_load"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_mem_load {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {addr : BitVec width} : wordStateRel reachable s t → t.memLoad addr = s.memLoad addr := by
  intro h
  simp only [memLoad, h.2.2.2.2.1, h.2.2.2.2.2.1]

/-- Exact HOL `word_state_rel_mem_load_32` (`word_elimProofScript.sml:634-640`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_mem_load_32"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_mem_load_32 {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {c : BitVec width} : wordStateRel reachable s t →
      memLoad32Exact s.memory s.mdomain s.be c = memLoad32Exact t.memory t.mdomain t.be c := by
  intro h
  rw [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

/-- Exact HOL `word_state_rel_get_fp_var` (`word_elimProofScript.sml:642-647`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_get_fp_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_get_fp_var {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {v : Nat} : wordStateRel reachable s t → s.getFpVar v = t.getFpVar v := by
  intro h
  simp only [getFpVar, h.2.1]

/-- Exact HOL `word_state_rel_assign_NONE` (`word_elimProofScript.sml:649-656`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_assign_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_assign_NONE {width : Nat} [NeZero width] {C F : Type}
    :
    ∀ (reg : Nat) (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (reachable : NumSet) (t : WordSemStateFiniteExact width C F),
      wordStateRel reachable s t → (s.assign reg exp = none ↔ t.assign reg exp = none) := by
  intro reg exp s reachable t h
  have he := word_state_rel_word_exp s exp t reachable h
  simp only [assign, he]
  cases s.wordExp exp <;> simp


/-- Related states differ at most in their code. Flapjack infrastructure. -/
theorem wordStateRel_eq_withCode {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) : t = { s with code := t.code } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, _, _⟩ := h
  cases s; cases t
  simp_all

/-- Replacing the code is an `inst` frame. Flapjack infrastructure. -/
theorem withCode_instFrame {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) :
    InstFrame (fun x : WordSemStateFiniteExact width C F => { x with code := code }) where
  locals _ := rfl
  store _ := rfl
  memory _ := rfl
  mdomain _ := rfl
  be _ := rfl
  fpRegs _ := rfl
  setVar _ _ _ := rfl
  setFpVar _ _ _ := rfl
  setMemory _ _ := rfl
  memStore a w s := by
    simp only [memStore]
    split <;> rfl

/-- Exact HOL `word_state_rel_inst_NONE` (`word_elimProofScript.sml:658-683`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_inst_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_inst_NONE {width : Nat} [NeZero width] {C F : Type}
    :
    ∀ (reachable : NumSet) (s t : WordSemStateFiniteExact width C F)
      (i : WordLangInst (BitVec width)),
      wordStateRel reachable s t → (s.inst i = none ↔ t.inst i = none) := by
  intro reachable s t i h
  rw [wordStateRel_eq_withCode h, ← inst_frame (withCode_instFrame t.code) i s]
  cases s.inst i <;> simp

/-- Exact HOL `word_state_rel_set_vars` (`word_elimProofScript.sml:582-600`);
HOL free variables are
universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_set_vars"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_set_vars {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {l : List (WordLocW width)} {l0 : List Nat} :
    wordStateRel reachable s t ∧
        ⋃₀ {S | S ∈ l.map (fun x' => match destWordLoc x' with
          | none => (∅ : Set Nat) | some x => {x})} ⊆ sptDomainSet reachable ∧
        l0.length = l.length →
      wordStateRel reachable (s.setVars l0 l) (t.setVars l0 l) := by
  rintro ⟨h, hl, hlen⟩
  induction l0 generalizing l with
  | nil =>
    cases l with
    | nil => simpa [setVars, LoopSemStateFiniteExact.sptAlistInsert] using h
    | cons _ _ => simp at hlen
  | cons n ns ih =>
    cases l with
    | nil => simp at hlen
    | cons x xs =>
      have hxs : ⋃₀ {S | S ∈ xs.map (fun x' => match destWordLoc x' with
          | none => (∅ : Set Nat) | some x => {x})} ⊆ sptDomainSet reachable := by
        rintro m ⟨S, hS, hmS⟩
        exact hl ⟨S, List.mem_cons_of_mem _ hS, hmS⟩
      have hx : (match destWordLoc x with
          | none => (∅ : Set Nat) | some y => {y}) ⊆ sptDomainSet reachable := by
        intro m hm
        exact hl ⟨_, List.mem_cons_self, hm⟩
      have rest := ih hxs (by simpa using hlen)
      have := word_state_rel_set_var (n := n) (v := x) ⟨rest, hx⟩
      simpa [setVars, setVar, LoopSemStateFiniteExact.sptAlistInsert] using this

/-! ## Location bookkeeping (Flapjack infrastructure)

The HOL proofs below establish `domain (find_loc_state s1) ⊆ domain reachable`
by `fs`/`gvs` case splits.  The Lean proofs factor this through
`LocsWithin s1 s`: every location of `s1` is already a location of `s`. -/

section LocationBookkeeping
variable {width : Nat} [NeZero width] {C F : Type}

/-- Pointwise form of `find_loc_state`. Flapjack infrastructure. -/
theorem sptMem_findLocState (s : WordSemStateFiniteExact width C F) (n : Nat) :
    sptMem n (findLocState s) ↔
      sptMem n (getLocals s.locals) ∨ sptMem n (getStore s.store) ∨
        sptMem n (getStack s.stack) ∨ sptMem n (getMemory s.memory s.mdomain) := by
  simp only [findLocState, sptMem_sptUnion]
  tauto

/-- Every location of `s1` is a location of `s`. Flapjack infrastructure. -/
def LocsWithin (s1 s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ n, sptMem n (findLocState s1) → sptMem n (findLocState s)

theorem LocsWithin.refl (s : WordSemStateFiniteExact width C F) : LocsWithin s s :=
  fun _ h => h

theorem LocsWithin.trans {s2 s1 s : WordSemStateFiniteExact width C F}
    (h2 : LocsWithin s2 s1) (h1 : LocsWithin s1 s) : LocsWithin s2 s :=
  fun n h => h1 n (h2 n h)

/-- A value whose `Loc` block (if any) is a location of `s`. -/
def LocOf (s : WordSemStateFiniteExact width C F) (v : WordLocW width) : Prop :=
  ∀ n o, v = .loc n o → sptMem n (findLocState s)

theorem locOf_word (s : WordSemStateFiniteExact width C F) (w : BitVec width) :
    LocOf s (.word w) := by
  intro n o h; cases h

/-- Related states with the same code and fewer locations stay related after
    replacing the code by the removed state's. Flapjack infrastructure. -/
theorem wordStateRel_withCode {reachable : NumSet} {s t s1 : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) (hcode : s1.code = s.code)
    (hloc : ∀ n, sptMem n (findLocState s1) → sptMem n reachable) :
    wordStateRel reachable s1 { s1 with code := t.code } := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, by rw [hcode]; exact hc, hloc⟩

theorem wordStateRel_withCode_within {reachable : NumSet}
    {s t s1 : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) (hcode : s1.code = s.code) (hloc : LocsWithin s1 s) :
    wordStateRel reachable s1 { s1 with code := t.code } :=
  wordStateRel_withCode h hcode fun n hn => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 n
    (hloc n hn)

theorem wordExp_locOf (s : WordSemStateFiniteExact width C F) (e : WordLangExpHOL (BitVec width))
    {v : WordLocW width} (h : s.wordExp e = some v) : LocOf s v := by
  rintro n o rfl
  rw [sptMem_findLocState]
  cases e with
  | const w => simp [wordExp] at h
  | var x => exact Or.inl ((domainGetLocalsLookup n s.locals).mpr ⟨x, o, by simpa [wordExp, getVar] using h⟩)
  | lookup name => exact Or.inr (Or.inl ((domain_get_store n s.store).mpr ⟨name, o, by simpa [wordExp, WordSemStateFiniteExact.getStore] using h⟩))
  | load a =>
    refine Or.inr (Or.inr (Or.inr ?_))
    simp only [wordExp] at h
    split at h
    · simp only [memLoad] at h
      split at h
      · rename_i hd
        exact (domain_get_memory _ _ n).mpr ⟨_, o, hd, (Option.some.inj h)⟩
      · cases h
    · cases h
  | op operator args =>
    simp only [wordExp] at h
    split at h
    · simp at h
    · cases h
  | shift sh e1 e2 =>
    simp only [wordExp] at h
    split at h
    · simp at h
    · cases h

theorem locsWithin_setVar (s : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width)
    (hv : LocOf s v) : LocsWithin (s.setVar k v) s := by
  intro n hn
  rw [sptMem_findLocState] at hn
  rcases hn with hl | hrest
  · rcases getLocals_insert k v s.locals hl with hl' | hl'
    · exact (sptMem_findLocState s n).mpr (Or.inl hl')
    · cases v with
      | word w => simp at hl'
      | loc b o =>
        simp only [destWordLoc_loc, Set.mem_singleton_iff] at hl'
        subst hl'
        exact hv _ o rfl
  · exact (sptMem_findLocState s n).mpr (Or.inr hrest)

theorem locsWithin_setFpVar (s : WordSemStateFiniteExact width C F) (k : Nat) (v : BitVec 64) :
    LocsWithin (s.setFpVar k v) s := fun _ h => h

/-- Overwriting one memory cell with a word adds no location. -/
theorem locsWithin_memory_word (s : WordSemStateFiniteExact width C F) (k : BitVec width)
    (w : BitVec width) :
    LocsWithin { s with memory := fun a => if a = k then .word w else s.memory a } s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  rcases hn with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    obtain ⟨k', n1, hd, hk⟩ := (domain_get_memory _ _ n).mp h
    dsimp only at hk hd
    split at hk
    · cases hk
    · exact (domain_get_memory _ _ n).mpr ⟨k', n1, hd, hk⟩

theorem locsWithin_memStore (s s1 : WordSemStateFiniteExact width C F) (a : BitVec width)
    (v : WordLocW width) (hv : LocOf s v) (h : memStore a v s = some s1) : LocsWithin s1 s := by
  simp only [memStore] at h
  split at h
  · cases h
    intro n hn
    rw [sptMem_findLocState] at hn
    rcases hn with h | h | h | h
    · exact (sptMem_findLocState s n).mpr (Or.inl h)
    · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inl h))
    · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inl h)))
    · obtain ⟨k', n1, hd, hk⟩ := (domain_get_memory _ _ n).mp h
      dsimp only at hk hd
      split at hk
      · exact hv n n1 hk
      · exact (sptMem_findLocState s n).mpr
          (Or.inr (Or.inr (Or.inr ((domain_get_memory _ _ n).mpr ⟨k', n1, hd, hk⟩))))
  · cases h

theorem assign_locsWithin (s s1 : WordSemStateFiniteExact width C F) (reg : Nat)
    (exp : WordLangExpHOL (BitVec width)) (h : s.assign reg exp = some s1) : LocsWithin s1 s := by
  simp only [assign] at h
  split at h
  · cases h
  · rename_i w hw
    cases h
    exact locsWithin_setVar s reg w (wordExp_locOf s exp hw)

theorem memLoad_locOf (s : WordSemStateFiniteExact width C F) (a : BitVec width)
    {v : WordLocW width} (h : s.memLoad a = some v) : LocOf s v :=
  wordExp_locOf s (.load (.const a)) (by simpa [wordExp] using h)

theorem memStoreByteAux_locsWithin (s : WordSemStateFiniteExact width C F) (a : BitVec width)
    (b : BitVec 8) {m : BitVec width → WordLocW width}
    (h : memStoreByteAuxExact s.memory s.mdomain s.be a b = some m) :
    LocsWithin { s with memory := m } s := by
  simp only [memStoreByteAuxExact] at h
  split at h
  · split at h
    · cases h
      exact locsWithin_memory_word s _ _
    · cases h
  · cases h

theorem memStore32_locsWithin (s : WordSemStateFiniteExact width C F) (a : BitVec width)
    (b : BitVec 32) {m : BitVec width → WordLocW width}
    (h : memStore32Exact s.memory s.mdomain s.be a b = some m) :
    LocsWithin { s with memory := m } s := by
  simp only [memStore32Exact] at h
  split at h
  · split at h
    · split at h
      · cases h
        exact locsWithin_memory_word s _ _
      · cases h
    · cases h
  · cases h

/-- Chains `set_var` of words and `set_fp_var` updates. -/
macro "locs_chain" : tactic => `(tactic| (repeat' (first
   | exact LocsWithin.refl _
   | refine LocsWithin.trans (locsWithin_setVar _ _ _ (locOf_word _ _)) ?_
   | refine LocsWithin.trans (locsWithin_setFpVar _ _ _) ?_)))

theorem inst_locsWithin (s s1 : WordSemStateFiniteExact width C F)
    (i : WordLangInst (BitVec width)) (h : s.inst i = some s1) : LocsWithin s1 s := by
  cases i with
  | skip => simp only [inst] at h; cases h; exact LocsWithin.refl s
  | const r w => exact assign_locsWithin s s1 _ _ h
  | arith a =>
    cases a
    · exact assign_locsWithin s s1 _ _ h
    · exact assign_locsWithin s s1 _ _ h
    all_goals simp only [inst] at h
    all_goals (repeat' split at h)
    all_goals first
      | (cases h; done)
      | (cases h; locs_chain)
  | mem op r a =>
    cases a
    cases op <;> simp only [inst] at h
    all_goals (repeat' split at h)
    all_goals first
      | (cases h; done)
      | (cases h; locs_chain; done)
      | skip
    · rename_i hl h'
      cases h
      exact locsWithin_setVar s r _ (memLoad_locOf s _ h')
    · rename_i hv _ _ hm
      cases h
      exact locsWithin_memStore s s1 _ _ (wordExp_locOf s (.var r) (by simpa [wordExp] using hv)) hm
    · rename_i hm
      cases h
      exact memStoreByteAux_locsWithin s _ _ hm
    · rename_i hm
      cases h
      exact memStore32_locsWithin s _ _ hm
  | fp f =>
    cases f <;> simp only [inst] at h
    all_goals (repeat' split at h)
    all_goals first
      | (cases h; done)
      | (cases h; locs_chain)

/-! ### Replacing the code commutes with the stack operations -/

theorem popEnv_withCode (s : WordSemStateFiniteExact width C F)
    (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    popEnv { s with code := c } = (popEnv s).map fun x => { x with code := c } := by
  unfold popEnv
  dsimp only
  split <;> rfl

theorem jumpExc_withCode (s : WordSemStateFiniteExact width C F)
    (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    jumpExc { s with code := c } =
      (jumpExc s).map (Prod.map (fun x => { x with code := c }) id) := by
  unfold jumpExc
  dsimp only
  by_cases h : s.handler < s.stack.length
  · simp only [h, if_true]
    split <;> rfl
  · simp only [h, if_false, Option.map_none]

theorem gc_withCode (s : WordSemStateFiniteExact width C F)
    (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    gc { s with code := c } = (gc s).map fun x => { x with code := c } := by
  unfold gc
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem withCode_allocFrame (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    AllocFrame (fun x : WordSemStateFiniteExact width C F => { x with code := c }) where
  locals _ := rfl
  store _ := rfl
  pushStore envs w s := by
    simp only [pushEnv, setStore]
  gc s := gc_withCode s c
  popEnv s := popEnv_withCode s c
  flushState b s := by cases b <;> rfl

/-! ### Locations after the stack operations -/

theorem popEnv_locsWithin (s s1 : WordSemStateFiniteExact width C F)
    (h : popEnv s = some s1) : LocsWithin s1 s := by
  have hst : sptDomainSet (getStack s.stack) ⊆ fun n => sptMem n (findLocState s) :=
    fun n hn => (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inl hn)))
  unfold popEnv at h
  split at h
  all_goals first
    | cases h; done
    | skip
  all_goals
    rename_i hs
    cases h
    obtain ⟨hl, ht⟩ := getStack_hd_thm _ _ _ _ _ _ _ ⟨hst, hs⟩
    intro n hn
    rw [sptMem_findLocState] at hn
    rcases hn with h | h | h | h
    · exact hl h
    · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inl h))
    · exact ht h
    · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inr h)))

theorem jumpExc_locsWithin (s s1 : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (h : jumpExc s = some (s1, l1, l2)) : LocsWithin s1 s := by
  have hst : sptDomainSet (getStack (wordSemLastN (s.handler + 1) s.stack)) ⊆
      fun n => sptMem n (findLocState s) :=
    fun n hn => (sptMem_findLocState s n).mpr
      (Or.inr (Or.inr (Or.inl (getStack_LASTN s.stack _ hn))))
  unfold jumpExc at h
  split at h
  · split at h
    · rename_i hs
      cases h
      obtain ⟨hl, ht⟩ := getStack_hd_thm _ _ _ _ _ _ _ ⟨hst, hs⟩
      intro n hn
      rw [sptMem_findLocState] at hn
      rcases hn with h | h | h | h
      · exact hl h
      · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inl h))
      · exact ht h
      · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inr h)))
    · cases h
  · cases h

theorem gc_locsWithin (s s1 : WordSemStateFiniteExact width C F)
    (hg : gcNoNewLocs s.gcFun) (h : gc s = some s1) : LocsWithin s1 s := by
  unfold gc at h
  dsimp only at h
  split at h
  · cases h
  · rename_i wl m st hgc
    split at h
    · cases h
    · rename_i stack hdec
      cases h
      obtain ⟨h1, h2, h3⟩ := hg _ _ _ _ _ _ _ _ ⟨hgc, hdec⟩
      intro n hn
      rw [sptMem_findLocState] at hn ⊢
      rcases hn with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (h3 n h))
      · exact Or.inr (Or.inr (Or.inl (h1 n h)))
      · exact Or.inr (Or.inr (Or.inr (h2 n h)))

theorem locsWithin_setStore_word (s : WordSemStateFiniteExact width C F) (k : WordStoreHOL)
    (w : BitVec width) : LocsWithin (setStore k (.word w) s) s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  rcases hn with h | h | h | h
  · exact Or.inl h
  · rcases get_store_update s.store k (.word w) h with h' | h'
    · exact Or.inr (Or.inl h')
    · simp at h'
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem locsWithin_flushState (s : WordSemStateFiniteExact width C F) (b : Bool) :
    LocsWithin (flushState b s) s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  cases b <;> simp only [flushState] at hn
  · rcases hn with h | h | h | h
    · simp [getLocals] at h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases hn with h | h | h | h
    · simp [getLocals] at h
    · obtain ⟨k, n1, hk⟩ := (domain_get_store n HolFiniteMapExact.empty).mp h
      simp [HolFiniteMapExact.empty] at hk
    · simp [getStack] at h
    · exact Or.inr (Or.inr (Or.inr h))

theorem pushEnv_locsWithin (s : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hd : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    LocsWithin (pushEnv envs hd s) s := by
  unfold wordSemCutEnvs wordSemCutNames at hcut
  split at hcut
  · rename_i e1 e2 h1 h2
    cases hcut
    split at h1 <;> cases h1
    split at h2 <;> cases h2
    have hloc : sptDomainSet (getLocals s.locals) ⊆ fun n => sptMem n (findLocState s) :=
      fun n hn => (sptMem_findLocState s n).mpr (Or.inl hn)
    have hst : sptDomainSet (getStack s.stack) ⊆ fun n => sptMem n (findLocState s) :=
      fun n hn => (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inl hn)))
    intro n hn
    rw [sptMem_findLocState] at hn
    rcases hd with _ | ⟨_, _, l1, l2⟩
    all_goals
      simp only [pushEnv, wordSemEnvToList] at hn
      rcases hn with h | h | h | h
      · exact (sptMem_findLocState s n).mpr (Or.inl h)
      · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inl h))
      · exact stack_list_rearrange_lemma (n := names.1) s _ names.2 _ _ ⟨hloc, hst⟩ h
      · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inr h)))
  · cases hcut

/-- The locations of a successful or out-of-space `alloc` result. -/
theorem alloc_locsWithin (s s1 : WordSemStateFiniteExact width C F) (w : BitVec width)
    (names : WordLangCutsetsHOL) (res : Option (WordSemResult width))
    (hres : res ≠ some .error) (hg : gcNoNewLocs s.gcFun) (h : alloc w names s = (res, s1)) :
    LocsWithin s1 s ∧ (res = none ∨ res = some .notEnoughSpace) := by
  unfold alloc at h
  split at h
  · cases h; exact absurd rfl hres
  · rename_i envs hcut
    have h0 := locsWithin_setStore_word s .allocSize w
    have h1 := pushEnv_locsWithin (setStore .allocSize (.word w) s) names envs hcut none
    split at h
    · cases h; exact absurd rfl hres
    · rename_i s2 hgc
      have h2 := gc_locsWithin (pushEnv envs none (setStore .allocSize (.word w) s)) s2
        (by unfold pushEnv; exact hg) hgc
      split at h
      · cases h; exact absurd rfl hres
      · rename_i s3 hpop
        have h3 := popEnv_locsWithin s2 s3 hpop
        have hall : LocsWithin s3 s := h3.trans (h2.trans (h1.trans h0))
        split at h
        · cases h; exact absurd rfl hres
        · split at h
          · cases h; exact absurd rfl hres
          · cases h; exact ⟨hall, Or.inl rfl⟩
          · cases h; exact ⟨(locsWithin_flushState s3 true).trans hall, Or.inr rfl⟩

end LocationBookkeeping

end Flapjack.Compiler.Backend.WordElim

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack WordSemStateFiniteExact

/-- Related states are the original state with the removed code. Flapjack
infrastructure. -/
theorem wordStateRel_exists_withCode {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    (h : wordStateRel reachable s t) : ∃ c, t = { s with code := c } :=
  ⟨_, wordStateRel_eq_withCode h⟩

theorem popEnv_code {width : Nat} [NeZero width] {C F : Type}
    {s s1 : WordSemStateFiniteExact width C F} (h : popEnv s = some s1) : s1.code = s.code := by
  unfold popEnv at h
  split at h <;> cases h <;> rfl

/-- Exact HOL `word_state_rel_assign_SOME` (`word_elimProofScript.sml:685-735`);
HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_assign_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_assign_SOME {width : Nat} [NeZero width] {C F : Type}
    {reachable : NumSet} {s t : WordSemStateFiniteExact width C F}
    {reg : Nat} {exp : WordLangExpHOL (BitVec width)} {s1 t1 : WordSemStateFiniteExact width C F} :
    wordStateRel reachable s t →
      (s.assign reg exp = some s1 ∧ t.assign reg exp = some t1 →
        wordStateRel reachable s1 t1) := by
  intro h ⟨hs, ht⟩
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  rw [← assign_frame (withCode_instFrame c), hs] at ht
  cases ht
  have hcode : s1.code = s.code := by
    simp only [assign] at hs
    split at hs <;> cases hs
    rfl
  exact wordStateRel_withCode_within h hcode (assign_locsWithin s s1 reg exp hs)

/-- Exact HOL `word_state_rel_inst_SOME` (`word_elimProofScript.sml:737-800`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_inst_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_inst_SOME {width : Nat} [NeZero width] {C F : Type} :
    ∀ (reachable : NumSet) (s t : WordSemStateFiniteExact width C F)
      (i : WordLangInst (BitVec width)) (s1 t1 : WordSemStateFiniteExact width C F),
      wordStateRel reachable s t →
        (s.inst i = some s1 ∧ t.inst i = some t1 → wordStateRel reachable s1 t1) := by
  intro reachable s t i s1 t1 h ⟨hs, ht⟩
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  rw [← inst_frame (withCode_instFrame c), hs] at ht
  cases ht
  exact wordStateRel_withCode_within h (instConstFull i s s1 hs).1 (inst_locsWithin s s1 i hs)

/-- Exact HOL `word_state_rel_pop_env_NONE` (`word_elimProofScript.sml:802-808`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_pop_env_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_pop_env_NONE {width : Nat} [NeZero width] {C F : Type} :
    ∀ (reachable : NumSet) (s t : WordSemStateFiniteExact width C F),
      wordStateRel reachable s t → (popEnv s = none ↔ popEnv t = none) := by
  intro reachable s t h
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  have := popEnv_withCode s c
  cases hp : popEnv s <;> simp_all

/-- Exact HOL `word_state_rel_pop_env` (`word_elimProofScript.sml:810-819`).
HOL's universally quantified `l1 : δ` and `l2 : ε` do not occur in the body;
they are retained with independent types, as in the typed capture. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_pop_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_pop_env {width : Nat} [NeZero width] {C F : Type} {δ ε : Type} :
    ∀ (reachable : NumSet) (s t s1 : WordSemStateFiniteExact width C F) (_l1 : δ) (_l2 : ε),
      wordStateRel reachable s t →
        popEnv s = some s1 → ∃ t1, popEnv t = some t1 ∧ wordStateRel reachable s1 t1 := by
  intro reachable s t s1 _ _ h hp
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  refine ⟨{ s1 with code := c }, by rw [popEnv_withCode, hp]; rfl, ?_⟩
  exact wordStateRel_withCode_within h (popEnv_code hp) (popEnv_locsWithin s s1 hp)

/-- Exact HOL `word_state_rel_jump_exc` (`word_elimProofScript.sml:821-835`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_jump_exc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_jump_exc {width : Nat} [NeZero width] {C F : Type} :
    ∀ (reachable : NumSet) (s t s1 : WordSemStateFiniteExact width C F) (l1 l2 : Nat),
      wordStateRel reachable s t →
        jumpExc s = some (s1, l1, l2) →
          ∃ t1, jumpExc t = some (t1, l1, l2) ∧ wordStateRel reachable s1 t1 := by
  intro reachable s t s1 l1 l2 h hj
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  refine ⟨{ s1 with code := c }, by rw [jumpExc_withCode, hj]; rfl, ?_⟩
  exact wordStateRel_withCode_within h (jumpExcConst s s1 (l1, l2) hj).2.2.2.2.1
    (jumpExc_locsWithin s s1 l1 l2 hj)

/-- Exact HOL `word_state_rel_gc` (`word_elimProofScript.sml:837-851`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_gc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_gc {width : Nat} [NeZero width] {C F : Type} :
    ∀ (reachable : NumSet) (s t s1 : WordSemStateFiniteExact width C F),
      wordStateRel reachable s t ∧ gcNoNewLocs s.gcFun →
        gc s = some s1 → ∃ t1, gc t = some t1 ∧ wordStateRel reachable s1 t1 := by
  intro reachable s t s1 ⟨h, hg⟩ hgc
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode h
  refine ⟨{ s1 with code := c }, by rw [gc_withCode, hgc]; rfl, ?_⟩
  exact wordStateRel_withCode_within h (gcConst s s1 hgc).2.2.1 (gc_locsWithin s s1 hg hgc)

/-- Exact HOL `word_state_rel_alloc` (`word_elimProofScript.sml:853-900`);
HOL's `dest_result_loc res ⊆ domain reachable` is the `Set Nat` inclusion of
the set `{n | destResultLoc res n}`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_state_rel_alloc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_state_rel_alloc {width : Nat} [NeZero width] {C F : Type} :
    ∀ (reachable : NumSet) (s t : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (c : BitVec width) (n : WordLangCutsetsHOL)
      (s1 : WordSemStateFiniteExact width C F),
      wordStateRel reachable s t ∧ res ≠ some .error ∧ gcNoNewLocs s.gcFun →
        alloc c n s = (res, s1) →
          ∃ t1, alloc c n t = (res, t1) ∧ wordStateRel reachable s1 t1 ∧
            {n | destResultLoc res n} ⊆ sptDomainSet reachable := by
  intro reachable s t res c n s1 ⟨h, hres, hg⟩ ha
  obtain ⟨code, rfl⟩ := wordStateRel_exists_withCode h
  obtain ⟨hloc, hr⟩ := alloc_locsWithin s s1 c n res hres hg ha
  refine ⟨{ s1 with code := code }, ?_, ?_, ?_⟩
  · rw [← alloc_frame (withCode_allocFrame code), ha]; rfl
  · exact wordStateRel_withCode_within h (allocConst c n s s1 res ha).2.2.1 hloc
  · rcases hr with rfl | rfl <;> intro x hx <;> exact hx.elim

end Flapjack.Compiler.Backend.WordElim
