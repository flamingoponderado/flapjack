module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateConst

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
end Flapjack.Compiler.Backend.WordElim
