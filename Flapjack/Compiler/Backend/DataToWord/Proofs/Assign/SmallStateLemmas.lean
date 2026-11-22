module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Compiler.Backend.DataToWord.Total
public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutNamesOdd
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.WordDepth
public import Flapjack.Misc.MiscThe
public import Flapjack.Misc.SptreeLookup
public import Flapjack.Misc.Sptree.MkWf
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ToListA
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Misc.Sptree.ToAList
public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvProperties
public import Flapjack.FiniteMap.AlistExact.Lookup

@[expose] public section

/-!
# Small state, option and sparse-tree lemmas of `data_to_word_assignProofScript.sml`

HOL `OPTION_MAP2` is `Option.map₂` (as in `BackendProps`), `the` is `miscThe`, `domain t` is
`sptDomain t`, and `x ∈ domain t` is `sptDomain t x`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth

namespace SmallStateLemmasWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end SmallStateLemmasWitness

/-- Lists of length five, in both orientations of the length equation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LENGTH_EQ_5"]
theorem lengthEq5 {α : Type} (xs : List α) :
    (xs.length = 5 ↔ ∃ a1 a2 a3 a4 a5, xs = [a1, a2, a3, a4, a5]) ∧
      (5 = xs.length ↔ ∃ a1 a2 a3 a4 a5, xs = [a1, a2, a3, a4, a5]) := by
  have key : xs.length = 5 ↔ ∃ a1 a2 a3 a4 a5, xs = [a1, a2, a3, a4, a5] := by
    constructor
    · intro h
      match xs, h with
      | [a1, a2, a3, a4, a5], _ => exact ⟨a1, a2, a3, a4, a5, rfl⟩
    · rintro ⟨a1, a2, a3, a4, a5, rfl⟩; rfl
  exact ⟨key, by rw [eq_comm]; exact key⟩

/-- A non-negative integer is a natural number. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "not_less_zero_int_eq"]
theorem not_less_zero_int_eq (i : Int) : ¬ i < 0 ↔ ∃ n : Nat, i = (n : Int) := by
  constructor
  · intro h; exact ⟨i.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  · rintro ⟨n, rfl⟩; omega

/-- A lookup succeeds exactly on the domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IS_SOME_lookup"]
theorem isSome_lookup {α : Type} (n : Nat) (l : Spt α) :
    (sptLookup n l).isSome = true ↔ sptDomain l n := by
  unfold sptDomain
  exact Iff.rfl

/-- `OPTION_MAP2` is `NONE` when either argument is `NONE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "OPTION_MAP2_NONE_THM"]
theorem optionMap2_none_thm {α β : Type} (f : β → β → α) (x : Option β) :
    Option.map₂ f none x = none ∧ Option.map₂ f x none = none := by
  cases x <;> simp

/-- `OPTION_MAP2` is `NONE` when either argument is `NONE` (the later
simp-set restatement). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "OPTION_MAP2_NONE"]
theorem optionMap2_none {α β : Type} (f : β → β → α) (n : Option β) :
    Option.map₂ f none n = none ∧ Option.map₂ f n none = none := by
  cases n <;> simp

/-- `option_le` is total. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_flip_neg"]
theorem optionLe_flip_neg (a b : Option Nat) (h : ¬ optionLe a b) : optionLe b a := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp_all [optionLe]
  omega

/-- The stack-limit test `the F (OPTION_MAP ($> n) m)` is the negated bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "the_F_not_option_le"]
theorem the_F_not_optionLe (n : Nat) (m : Option Nat) :
    miscThe false (m.map (fun x => decide (n > x))) = true ↔ ¬ optionLe (some n) m := by
  rcases m with _ | m <;> simp [miscThe, optionLe]

/-- The negated stack-limit test is the bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "not_the_F_option_le"]
theorem not_the_F_optionLe (n : Nat) (m : Option Nat) :
    ¬ miscThe false (m.map (fun x => decide (n > x))) = true ↔ optionLe (some n) m := by
  rcases m with _ | m <;> simp [miscThe, optionLe]

/-- Small power-of-two bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "TWO_POW_LEMMA"]
theorem twoPowLemma (n : Nat) :
    (2 ^ n ≤ 3 → n < 2) ∧ (2 ^ n ≤ 2 → n < 2) ∧ (2 ^ n ≤ 1 → n < 1) := by
  rcases n with _ | _ | n
  · simp
  · simp
  · have h4 : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [show (2 : Nat) ^ 2 = 4 from rfl] at h4
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> omega

/-- A bounded division keeps the last full multiple below the square. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "WordFromInt_DIV_LEMMA"]
theorem wordFromInt_div_lemma (kk B : Nat) (h : kk < B * B ∧ 0 < B) :
    B * (kk / B) ≤ B * B - B := by
  obtain ⟨hk, hB⟩ := h
  have hd : kk / B < B := Nat.div_lt_of_lt_mul hk
  have : B * (kk / B) ≤ B * (B - 1) := Nat.mul_le_mul_left B (by omega)
  rw [Nat.mul_sub_one] at this
  exact this

/-- A universally quantified bound below 32 is the 32 instances. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "explode_less_32"]
theorem explode_less_32 (P : Nat → Prop) :
    (∀ n : Nat, n < 32 → P n) ↔
      P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧
      P 10 ∧ P 11 ∧ P 12 ∧ P 13 ∧ P 14 ∧ P 15 ∧ P 16 ∧ P 17 ∧ P 18 ∧ P 19 ∧
      P 20 ∧ P 21 ∧ P 22 ∧ P 23 ∧ P 24 ∧ P 25 ∧ P 26 ∧ P 27 ∧ P 28 ∧ P 29 ∧
      P 30 ∧ P 31 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
      h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega),
      h 10 (by omega), h 11 (by omega), h 12 (by omega), h 13 (by omega), h 14 (by omega),
      h 15 (by omega), h 16 (by omega), h 17 (by omega), h 18 (by omega), h 19 (by omega),
      h 20 (by omega), h 21 (by omega), h 22 (by omega), h 23 (by omega), h 24 (by omega),
      h 25 (by omega), h 26 (by omega), h 27 (by omega), h 28 (by omega), h 29 (by omega),
      h 30 (by omega), h 31 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ n hn
    interval_cases n <;> assumption

/-- Compiling a part keeps its name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MAP_FST_MAP_compile_part"
  (words_as_type_indexed_bitvec)]
theorem map_fst_map_compilePart {width : Nat} [NeZero width] (c : Config)
    (full_list : List (Nat × Nat × DataLang.Prog)) :
    ((full_list.map (compilePart c) : List (Nat × Nat × WordLangProgHOL (BitVec width))).map
      Prod.fst) = full_list.map Prod.fst := by
  induction full_list with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, b, p⟩ := e
    simp only [List.map_cons, ih]
    rfl

/-- The name of a compiled part is its source name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "compile_part_loc_IMP"
  (words_as_type_indexed_bitvec)]
theorem compilePart_loc_imp {width : Nat} [NeZero width] (c : Config) (a1 : Nat)
    (a2 : Nat × DataLang.Prog) (n : Nat) (x : Nat × WordLangProgHOL (BitVec width))
    (h : compilePart c (a1, a2) = (n, x)) : n = a1 := by
  obtain ⟨b, p⟩ := a2
  simp only [compilePart, Prod.mk.injEq] at h
  exact h.1.symm

/-- The adjusted cut of an intersection is the meet of the two adjusted
domains. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IN_domain_adjust_set_inter"]
theorem in_domain_adjustSet_inter {α β : Type} (x : Nat) (s1 : Spt α) (s2 : Spt β) :
    sptDomain (adjustSet (sptInter s1 s2)) x ↔
      sptDomain (adjustSet s1) x ∧ sptDomain (adjustSet s2) x := by
  simp only [Proofs.Gc.adjustSet_domain, sptDomain_sptInter]
  constructor
  · rintro ⟨n, rfl, h1, h2⟩
    exact ⟨⟨n, rfl, h1⟩, ⟨n, rfl, h2⟩⟩
  · rintro ⟨⟨n, rfl, h1⟩, ⟨m, hm, h2⟩⟩
    have : m = n := by simp only [adjustVar] at hm; omega
    subst this
    exact ⟨m, rfl, h1, h2⟩

/-- Inserting key one does not change the adjusted cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_names_adjust_set_insert_1"]
theorem cutNames_adjustSet_insert_1 {α β : Type} (x : Spt β) (w : α) (l : Spt α) :
    wordSemCutNames (adjustSet x) (sptInsert 1 w l) = wordSemCutNames (adjustSet x) l :=
  Proofs.Gc.cutNames_adjustSet_insert_one x l w

/-- Inserting key three does not change the adjusted cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_names_adjust_set_insert_3"]
theorem cutNames_adjustSet_insert_3 {α β : Type} (x : Spt β) (w : α) (l : Spt α) :
    wordSemCutNames (adjustSet x) (sptInsert 3 w l) = wordSemCutNames (adjustSet x) l :=
  Proofs.Gc.cutNames_adjustSet_insert_three x l w

/-- Inserting key five does not change the adjusted cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_names_adjust_set_insert_5"]
theorem cutNames_adjustSet_insert_5 {α β : Type} (x : Spt β) (w : α) (l : Spt α) :
    wordSemCutNames (adjustSet x) (sptInsert 5 w l) = wordSemCutNames (adjustSet x) l :=
  Proofs.Gc.cutNames_adjustSet_insertOdd x l 5 w rfl

/-- Pushing a data environment keeps the timestamp counter. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "push_env_tstamps"]
theorem pushEnv_tstamps {C F : Type} (x : Spt DataSem.Value) (t : Bool) (s : DataSem.State C F) :
    (DataSem.pushEnv x t s).tstamps = s.tstamps := by
  cases t <;> rfl

/-- Decrementing the data clock keeps the timestamp counter. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "dec_clock_tstamps"]
theorem decClock_tstamps {C F : Type} (s : DataSem.State C F) :
    (DataSem.decClock s).tstamps = s.tstamps := rfl

/-- Cutting the data state keeps its references. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_refs_same"]
theorem cutState_refs_same {C F : Type} (n : NumSet) (s x : DataSem.State C F)
    (h : DataSem.cutState n s = some x) : s.refs = x.refs := by
  unfold DataSem.cutState at h
  cases hc : DataSem.cutEnv n s.locals <;> simp [hc] at h
  subst h; rfl

/-- Consuming data space keeps the maximal stack size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "consume_space_stack_max"]
theorem consumeSpace_stackMax {C F : Type} (a : Nat) (x s : DataSem.State C F)
    (h : DataSem.consumeSpace a x = some s) : x.stackMax = s.stackMax := by
  unfold DataSem.consumeSpace at h
  split at h <;> simp at h
  subst h; rfl

/-- Setting a word variable keeps the memory, domain, endianness and code. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "set_var_consts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVar_consts {width : Nat} [NeZero width] {C F : Type} (r : Nat) (v : WordLocW width)
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.setVar r v s).memory = s.memory ∧
      (WordSemStateFiniteExact.setVar r v s).mdomain = s.mdomain ∧
      (WordSemStateFiniteExact.setVar r v s).be = s.be ∧
      (WordSemStateFiniteExact.setVar r v s).code = s.code :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Reading a word variable ignores the memory. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_var_consts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_consts {width : Nat} [NeZero width] {C F : Type} (r : Nat)
    (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getVar r { s with memory := m } =
      WordSemStateFiniteExact.getVar r s := rfl

/-- A set word variable reads back. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "lookup_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_setVar {width : Nat} [NeZero width] {C F : Type} (x : Nat) (y : WordLocW width)
    (z : WordSemStateFiniteExact width C F) :
    sptLookup x (WordSemStateFiniteExact.setVar x y z).locals = some y := by
  simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert]

/-- Pushing a word environment keeps the store, memory, domain, code and
endianness. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "push_env_store"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_store {width : Nat} [NeZero width] {C F : Type}
    (x : Spt (WordLocW width) × Spt (WordLocW width))
    (y : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.pushEnv x y s).store = s.store ∧
      (WordSemStateFiniteExact.pushEnv x y s).memory = s.memory ∧
      (WordSemStateFiniteExact.pushEnv x y s).mdomain = s.mdomain ∧
      (WordSemStateFiniteExact.pushEnv x y s).code = s.code ∧
      (WordSemStateFiniteExact.pushEnv x y s).be = s.be := by
  rcases y with _ | ⟨_, _, _, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Deleting a list of keys keeps a tree well formed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "wf_FOLDR_delete"]
theorem wf_foldr_delete {α : Type} (ks : List Nat) (L : Spt α) (h : sptWf L = true) :
    sptWf (ks.foldr sptDelete L) = true := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact sptWfDelete _ k ih

/-- Lookup after deleting a list of keys. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "lookup_FOLDR_delete"]
theorem lookup_foldr_delete {α : Type} (ks : List Nat) (L : Spt α) (h : Nat) :
    sptLookup h (ks.foldr sptDelete L) = if h ∈ ks then none else sptLookup h L := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldr_cons, sptLookup_sptDelete]
    by_cases hk : h = k
    · simp [hk]
    · simp [hk, ih]

/-- A successful adjusted pair of cuts is the reserved-name cut and the
intersection with the adjusted names, the latter contained in the
environment. Flapjack factoring of the two cut successes. -/
theorem cutEnvs_adjustSets_second {α β : Type} (names : Spt α) (env first second : Spt β)
    (run : wordSemCutEnvs (adjustSets names) env = some (first, second)) :
    second = sptInter env (adjustSet names) ∧
      LoopSemStateFiniteExact.sptSubsetLive (adjustSet names) env := by
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).2 env <;>
    simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at run
  exact ⟨run.2.symm, h2⟩

/-- The listed second cut has no reserved location, and a location found
in the union is in the first cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "lookup_loc_lemma"
  (words_as_type_indexed_bitvec)]
theorem lookup_loc_lemma {width : Nat} [NeZero width] {β : Type}
    (y2 : Spt (WordLocW width)) (permute : Nat → Nat → Nat)
    (l' : List (Nat × WordLocW width)) (permute' : Nat → Nat → Nat) (keep_names : Spt β)
    (locals y1 : Spt (WordLocW width)) (l1 l2 : Nat)
    (h : wordSemEnvToList y2 permute = (l', permute') ∧
      wordSemCutEnvs (adjustSets keep_names) locals = some (y1, y2) ∧
      sptLookup 0 (sptUnion y2 y1) = some (.loc l1 l2)) :
    holALookup l' 0 = none ∧ sptLookup 0 y1 = some (.loc l1 l2) := by
  obtain ⟨hl, hc, hu⟩ := h
  have zero := Proofs.Gc.cutEnvs_adjust_second_zero keep_names locals (y1, y2) hc
  have equiv := (wordSemEnvToListLookupEquiv y2 permute l' permute' hl).1 0
  constructor
  · have alist : ∀ entries : List (Nat × WordLocW width),
        holALookup entries 0 = sptAListLookup 0 entries := by
      intro entries
      induction entries with
      | nil => rfl
      | cons e rest ih =>
        obtain ⟨k, v⟩ := e
        by_cases hk : (0 : Nat) = k
        · subst hk; simp [holALookup, sptAListLookup]
        · simp [holALookup, sptAListLookup, hk, ih]
    rw [alist, equiv]
    exact zero
  · rw [sptLookup_sptUnion] at hu
    simpa [zero] using hu

/-- A data cut and the adjusted word cuts agree on every adjusted live name:
the value is in the target locals and in the second cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_envs_lookup_lookup"]
theorem cutEnv_envs_lookup_lookup {α β : Type} (kept_names : NumSet) (s_locals x : Spt α)
    (t_locals y1 y2 : Spt β) (k : Nat)
    (h : DataSem.cutEnv kept_names s_locals = some x ∧
      wordSemCutEnvs (adjustSets kept_names) t_locals = some (y1, y2) ∧
      sptDomain (adjustSet x) k) :
    ∃ v, sptLookup k t_locals = some v ∧ sptLookup k y2 = some v := by
  obtain ⟨hx, hc, hk⟩ := h
  obtain ⟨hy2, live⟩ := cutEnvs_adjustSets_second kept_names t_locals y1 y2 hc
  obtain ⟨n, rfl, hn⟩ := (Proofs.Gc.adjustSet_domain x k).mp hk
  have hn' : sptDomain kept_names n := by
    have := (Proofs.Gc.cutEnv_imp_mem kept_names s_locals x n hx)
    simpa [sptDomain] using this.mp hn
  have inAdj : sptMem (adjustVar n) (adjustSet kept_names) :=
    (Proofs.Gc.adjustVar_mem_adjustSet n kept_names).mpr hn'
  obtain ⟨v, hv⟩ := (sptMem_iff_lookup _ _).mp (live _ inAdj)
  obtain ⟨u, hu⟩ := (sptMem_iff_lookup _ _).mp inAdj
  refine ⟨v, hv, ?_⟩
  rw [hy2, sptLookup_sptInterCases, hv, hu]

/-- A data-live name is, adjusted, in the second word cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_envs_domain_IN"]
theorem cutEnvs_domain_in {α β : Type} (kept_names : NumSet) (t_locals y1 y2 : Spt α)
    (s_locals x : Spt β) (n : Nat)
    (h : wordSemCutEnvs (adjustSets kept_names) t_locals = some (y1, y2) ∧
      DataSem.cutEnv kept_names s_locals = some x ∧ sptDomain x n) :
    sptDomain y2 (adjustVar n) := by
  obtain ⟨hc, hx, hn⟩ := h
  have hk : sptDomain (adjustSet x) (adjustVar n) := (Proofs.Gc.adjustSet_domain x _).mpr ⟨n, rfl, hn⟩
  obtain ⟨v, -, hv⟩ := cutEnv_envs_lookup_lookup kept_names s_locals x t_locals y1 y2 _ ⟨hx, hc, hk⟩
  exact (sptMem_iff_lookup _ _).mpr ⟨v, hv⟩

/-- Keys below the next insertion index are untouched by the remaining
`fromList2` fold. Flapjack sparse-tree infrastructure. -/
theorem fromList2_fold_lookup_below {α : Type} (ts : List α) (start : Nat) (t : Spt α)
    (k : Nat) (hk : k < start) :
    sptLookup k (ts.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 2, sptInsert acc.1 value acc.2))
      (start, t)).2 = sptLookup k t := by
  induction ts generalizing start t with
  | nil => rfl
  | cons a ts ih =>
    rw [List.foldl_cons, ih (start + 2) _ (by omega)]
    exact sptLookup_sptInsert_ne start k a t (by omega)

/-- Reading the first three word arguments of a call environment. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "lookup_2_call_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_2_callEnv {width : Nat} [NeZero width] {C F : Type}
    (x y z : WordLocW width) (ts : List (WordLocW width)) (a1 : Option Nat)
    (a2 : WordSemStateFiniteExact width C F) :
    sptLookup 0 (WordSemStateFiniteExact.callEnv (x :: ts) a1 a2).locals = some x ∧
      sptLookup 2 (WordSemStateFiniteExact.callEnv (x :: y :: ts) a1 a2).locals = some y ∧
      sptLookup 4 (WordSemStateFiniteExact.callEnv (x :: y :: z :: ts) a1 a2).locals = some z := by
  simp only [WordSemStateFiniteExact.callEnv, sptFromList2, List.foldl_cons]
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [fromList2_fold_lookup_below _ _ _ _ (by omega), sptLookup_sptInsert_same]

/-- A small number at the head of the list adds nothing to the heap size.
HOL's statement also universally quantifies an unused, independently typed
variable `b : α`, which occurs nowhere in the statement and is omitted. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_Number_head"]
theorem sizeOf_number_head (vs : List DataSem.Value) (lims : DataSem.Limits)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) (n : Int)
    (h : DataSem.smallNum lims.arch64Bit n) :
    DataSem.sizeOfValues lims (.number n :: vs) refs seen = DataSem.sizeOfValues lims vs refs seen := by
  cases vs with
  | nil => simp [DataSem.sizeOfValues, h]
  | cons y ys =>
    rw [DataSem.sizeOfValues, DataSem.checkRes_sizeOfValues]
    simp [DataSem.sizeOfValues, h]

/-- Evaluating a guarded logical right shift. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_SmallLsr"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExp_smallLsr {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : WordSemStateFiniteExact width C F) (e : WordLangExpHOL (BitVec width))
    (hn : n < width) :
    WordSemStateFiniteExact.wordExp s (smallLsr e n) =
      match WordSemStateFiniteExact.wordExp s e with
      | some (.word w) => some (.word (w >>> n))
      | res => if n = 0 then res else none := by
  by_cases h0 : n = 0
  · subst h0
    simp only [smallLsr, if_true]
    split <;> simp_all
  · have hlt : n < 2 ^ width := Nat.lt_trans hn (Nat.lt_two_pow_self)
    have hval : (BitVec.ofNat width n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hsh : ∀ w : BitVec width, wordShiftHOL .lsr w n = some (w >>> n) := by
      intro w; simp [wordShiftHOL]; omega
    simp only [smallLsr, h0, if_false, shiftN, WordSemStateFiniteExact.wordExp]
    rcases WordSemStateFiniteExact.wordExp s e with _ | (w | ⟨b, o⟩) <;>
      simp [hval, hsh]

/-- The accumulator of the value traversal is appended. Flapjack sparse-tree
infrastructure (the same fact as `Gc.sptToListA_append`, restated here to
avoid importing the garbage-collector frame-root proofs). -/
theorem toListA_eq_toList_append {α : Type} (tree : Spt α) (acc : List α) :
    sptToListA acc tree = sptToList tree ++ acc := by
  change sptToListA acc tree = sptToListA [] tree ++ acc
  induction tree generalizing acc with
  | ln => rfl
  | ls value => rfl
  | bn left right ihl ihr =>
    simp only [sptToListA]
    rw [ihl (sptToListA acc right), ihl (sptToListA [] right), ihr acc]
    simp [List.append_assoc]
  | bs left value right ihl ihr =>
    simp only [sptToListA]
    rw [ihl (value :: sptToListA acc right), ihl (value :: sptToListA [] right), ihr acc]
    simp [List.append_assoc]

/-- Deleting a present key removes exactly its value from the traversal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "toList_delete_split"]
theorem toList_delete_split {α : Type} (k : Nat) (spt : Spt α) (vv : α)
    (h : sptLookup k spt = some vv) :
    ∃ pre post, sptToList spt = pre ++ [vv] ++ post ∧
      sptToList (sptDelete k spt) = pre ++ post := by
  have bn : ∀ l r : Spt α, sptToList (.bn l r) = sptToList l ++ sptToList r := by
    intro l r
    change sptToListA (sptToListA [] r) l = _
    rw [toListA_eq_toList_append]; rfl
  have bs : ∀ (l r : Spt α) (v : α),
      sptToList (.bs l v r) = sptToList l ++ [v] ++ sptToList r := by
    intro l r v
    change sptToListA (v :: sptToListA [] r) l = _
    rw [toListA_eq_toList_append]; simp; rfl
  have mkBN : ∀ l r : Spt α, sptToList (sptMkBN l r) = sptToList (.bn l r) :=
    fun l r => (Proofs.Gc.toListA_mk [] l r vv).1
  have mkBS : ∀ (l r : Spt α) (v : α), sptToList (sptMkBS l v r) = sptToList (.bs l v r) :=
    fun l r v => (Proofs.Gc.toListA_mk [] l r v).2
  induction spt generalizing k with
  | ln => simp [sptLookup] at h
  | ls v =>
    by_cases hk : k = 0
    · subst hk
      simp only [sptLookup, if_true, Option.some.injEq] at h
      subst h
      exact ⟨[], [], by simp [sptToList, sptToListA], by simp [sptDelete, sptToList, sptToListA]⟩
    · simp [sptLookup, hk] at h
  | bn l r ihl ihr =>
    by_cases hk : k = 0
    · simp [sptLookup, hk] at h
    by_cases he : k % 2 = 0
    · simp only [sptLookup, hk, he, if_false, if_true] at h
      obtain ⟨pre, post, h1, h2⟩ := ihl _ h
      refine ⟨pre, post ++ sptToList r, ?_, ?_⟩
      · rw [bn, h1]; simp
      · simp only [sptDelete, hk, he, if_false, if_true]
        rw [mkBN, bn, h2]; simp
    · simp only [sptLookup, hk, he, if_false] at h
      obtain ⟨pre, post, h1, h2⟩ := ihr _ h
      refine ⟨sptToList l ++ pre, post, ?_, ?_⟩
      · rw [bn, h1]; simp
      · simp only [sptDelete, hk, he, if_false]
        rw [mkBN, bn, h2]; simp
  | bs l v r ihl ihr =>
    by_cases hk : k = 0
    · subst hk
      simp only [sptLookup, if_true, Option.some.injEq] at h
      subst h
      refine ⟨sptToList l, sptToList r, bs l r v, ?_⟩
      simp only [sptDelete, if_true]
      exact bn l r
    by_cases he : k % 2 = 0
    · simp only [sptLookup, hk, he, if_false, if_true] at h
      obtain ⟨pre, post, h1, h2⟩ := ihl _ h
      refine ⟨pre, post ++ [v] ++ sptToList r, ?_, ?_⟩
      · rw [bs, h1]; simp
      · simp only [sptDelete, hk, he, if_false, if_true]
        rw [mkBS, bs, h2]; simp
    · simp only [sptLookup, hk, he, if_false] at h
      obtain ⟨pre, post, h1, h2⟩ := ihr _ h
      refine ⟨sptToList l ++ [v] ++ pre, post, ?_, ?_⟩
      · rw [bs, h1]; simp
      · simp only [sptDelete, hk, he, if_false]
        rw [mkBS, bs, h2]; simp

/-- Lifting the clock and depth update over a call of a pushed word state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "call_env_push_env_dec_clock_lift"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem callEnv_pushEnv_decClock_lift {width : Nat} [NeZero width] {C F : Type}
    (args : List (WordLocW width)) (b : Option Nat) (y1 y2 : Spt (WordLocW width))
    (t : WordSemStateFiniteExact width C F) (ck' tp : Nat) :
    WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none
        (WordSemStateFiniteExact.decClock { t with clock := ck', termdep := tp })) =
      { WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none t) with
        clock := ck' - 1, termdep := tp } := rfl

/-- As `call_env_push_env_dec_clock_lift`, with a discarded local update. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "call_env_push_env_dec_clock_lift_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem callEnv_pushEnv_decClock_lift_locals {width : Nat} [NeZero width] {C F : Type}
    (args : List (WordLocW width)) (b : Option Nat) (y1 y2 : Spt (WordLocW width))
    (t : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width) (ck' tp : Nat) :
    WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none
        (WordSemStateFiniteExact.decClock
          { t with locals := sptInsert k v t.locals, clock := ck', termdep := tp })) =
      { WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none t) with
        clock := ck' - 1, termdep := tp } := rfl

/-- The maximal stack size after pushing a data frame and calling. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "call_env_push_env_dec_clock_stack_max"]
theorem callEnv_pushEnv_decClock_stackMax {C F : Type} (args : List DataSem.Value)
    (ls : Option Nat) (env : Spt DataSem.Value) (s : DataSem.State C F) :
    (DataSem.callEnv args ls (DataSem.pushEnv env false (DataSem.decClock s))).stackMax =
      Option.map₂ max
        (Option.map₂ max s.stackMax
          (Option.map₂ (· + ·) s.localsSize (DataSem.sizeOfStack s.stack)))
        (Option.map₂ (· + ·)
          (Option.map₂ (· + ·) s.localsSize (DataSem.sizeOfStack s.stack)) ls) := rfl

/-- Reading `Var r + Const c` for the four small constants. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_var_to_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_to_wordExp {width : Nat} [NeZero width] {C F : Type} (r : Nat)
    (s : WordSemStateFiniteExact width C F) (w : BitVec width)
    (h : WordSemStateFiniteExact.getVar r s = some (.word w)) :
    WordSemStateFiniteExact.wordExp s (.op .add [.var r, .const 0]) = some (.word (w + 0)) ∧
      WordSemStateFiniteExact.wordExp s (.op .add [.var r, .const 1]) = some (.word (w + 1)) ∧
      WordSemStateFiniteExact.wordExp s (.op .add [.var r, .const 2]) = some (.word (w + 2)) ∧
      WordSemStateFiniteExact.wordExp s (.op .add [.var r, .const 3]) = some (.word (w + 3)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [WordSemStateFiniteExact.wordExp, h, theWords, wordOpHOL, wordOp]

/-- Evaluating `Var n + Const c` and `Var n - Const c`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_set"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExp_set {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (n : Nat) (c : BitVec width) :
    WordSemStateFiniteExact.wordExp s (.op .add [.var n, .const c]) =
        (match WordSemStateFiniteExact.getVar n s with
         | some (.word w) => some (.word (w + c))
         | _ => none) ∧
      WordSemStateFiniteExact.wordExp s (.op .sub [.var n, .const c]) =
        (match WordSemStateFiniteExact.getVar n s with
         | some (.word w) => some (.word (w - c))
         | _ => none) := by
  rcases h : WordSemStateFiniteExact.getVar n s with _ | (w | ⟨b, o⟩) <;>
    simp [WordSemStateFiniteExact.wordExp, theWords, wordOpHOL, wordOp, h]

/-- The pushed frame of a related call records the return location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_push_env_loc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_pushEnv_loc {width : Nat} [NeZero width] {C F : Type} (c : Config) (n l : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (args : List (WordLocW width)) (b : Option Nat)
    (y1 y2 : Spt (WordLocW width)) (t : WordSemStateFiniteExact width C F)
    (ys : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (h : Proofs.Gc.stateRel c n l s
      (WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none t))
      ys ((l1, l2) :: locs)) :
    sptLookup 0 y1 = some (.loc l1 l2) := by
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv] at hc
  have hf := (List.forall₂_cons.mp hc).1
  simp only [Proofs.Gc.containsLoc] at hf
  exact (sptMemToAList y1 0 _).mp (sptAListLookup_mem 0 _ _ hf)

/-- The maximal stack size bound after a list-building call. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_stackmax_bridge"]
theorem optionLe_stackmax_bridge (m l_size s_size ls_R ls_Re : Option Nat) :
    optionLe
      (Option.map₂ max
        (Option.map₂ max
          (Option.map₂ max m (Option.map₂ (· + ·) l_size s_size))
          (Option.map₂ (· + ·) (Option.map₂ (· + ·) l_size s_size) ls_R))
        (Option.map₂ (· + ·) (Option.map₂ max ls_R ls_Re) (Option.map₂ (· + ·) s_size l_size)))
      (Option.map₂ max m
        (Option.map₂ (· + ·) (Option.map₂ max ls_R ls_Re) (Option.map₂ (· + ·) s_size l_size))) := by
  rcases m with _ | m <;> rcases l_size with _ | a <;> rcases s_size with _ | b <;>
    rcases ls_R with _ | r <;> rcases ls_Re with _ | e <;> simp [optionLe]
  all_goals omega

/-- Heap sizing of a nonempty list: the tail first, then the head with the
remaining references. Flapjack factoring of `size_of_def` and
`check_res_size_of` (HOL's `size_of_cons`). -/
theorem sizeOfValues_cons_split (lims : DataSem.Limits) (h : DataSem.Value)
    (tail : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues lims (h :: tail) refs seen =
      ((DataSem.sizeOfValues lims tail refs seen).1 +
          (DataSem.sizeOfValues lims [h] (DataSem.sizeOfValues lims tail refs seen).2.1
            (DataSem.sizeOfValues lims tail refs seen).2.2).1,
        (DataSem.sizeOfValues lims [h] (DataSem.sizeOfValues lims tail refs seen).2.1
            (DataSem.sizeOfValues lims tail refs seen).2.2).2.1,
        (DataSem.sizeOfValues lims [h] (DataSem.sizeOfValues lims tail refs seen).2.1
            (DataSem.sizeOfValues lims tail refs seen).2.2).2.2) := by
  cases tail with
  | nil => simp [DataSem.sizeOfValues.eq_1]
  | cons y ys =>
    rw [DataSem.sizeOfValues, DataSem.checkRes_sizeOfValues]

open Classical in
/-- A number anywhere in the list adds its own bignum size. The test on
`small_num` uses classical decidability, as in the data semantics' `size_of`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_app_Number"]
theorem sizeOf_app_number (xs ys : List DataSem.Value) (lims : DataSem.Limits) (i : Int)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues lims (xs ++ .number i :: ys) refs seen =
      let (n, refs', seen') := DataSem.sizeOfValues lims (xs ++ ys) refs seen
      let k := if DataSem.smallNum lims.arch64Bit i then 0
        else DataSem.bignumSize lims.arch64Bit i
      (n + k, refs', seen') := by
  induction xs with
  | nil =>
    rw [List.nil_append, List.nil_append, sizeOfValues_cons_split]
    simp [DataSem.sizeOfValues]
  | cons h xs ih =>
    rw [List.cons_append, List.cons_append,
      sizeOfValues_cons_split lims h (xs ++ .number i :: ys),
      sizeOfValues_cons_split lims h (xs ++ ys), ih]
    rcases DataSem.sizeOfValues lims (xs ++ ys) refs seen with ⟨n, r', s'⟩
    simp only [Prod.mk.injEq, and_true]
    omega

/-- Deleting a number-valued local cannot increase the heap size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_heap_delete_Number_LE"]
theorem sizeOfHeap_delete_number_le {C F : Type} (k : Nat) (s : DataSem.State C F) (i : Int)
    (h : sptLookup k s.locals = some (.number i)) :
    DataSem.sizeOfHeap { s with locals := sptDelete k s.locals } ≤ DataSem.sizeOfHeap s := by
  obtain ⟨pre, post, h1, h2⟩ := toList_delete_split k s.locals _ h
  simp only [DataSem.sizeOfHeap, DataSem.stackToValues, h1, h2]
  have e : pre ++ [DataSem.Value.number i] ++ post ++ s.stack.flatMap DataSem.extractStack ++
      DataSem.globalToValues s.global =
      pre ++ .number i :: (post ++ s.stack.flatMap DataSem.extractStack ++
        DataSem.globalToValues s.global) := by simp
  have e2 : pre ++ post ++ s.stack.flatMap DataSem.extractStack ++
      DataSem.globalToValues s.global =
      pre ++ (post ++ s.stack.flatMap DataSem.extractStack ++
        DataSem.globalToValues s.global) := by simp
  rw [e, e2, sizeOf_app_number]
  simp only
  omega

/-- Deleting absent or number-valued locals cannot increase the heap size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "size_of_heap_FOLDR_delete_Number_LE"]
theorem sizeOfHeap_foldr_delete_number_le {C F : Type} (ks : List Nat)
    (L : Spt DataSem.Value) (state : DataSem.State C F)
    (h : sptWf L = true ∧
      ∀ k, k ∈ ks → sptLookup k L = none ∨ ∃ i, sptLookup k L = some (.number i)) :
    DataSem.sizeOfHeap { state with locals := ks.foldr sptDelete L } ≤
      DataSem.sizeOfHeap { state with locals := L } := by
  obtain ⟨hwf, hks⟩ := h
  induction ks with
  | nil => exact le_rfl
  | cons k ks ih =>
    have ih' := ih (fun k' hk' => hks k' (List.mem_cons_of_mem k hk'))
    have wfRest := wf_foldr_delete ks L hwf
    refine le_trans ?_ ih'
    rw [List.foldr_cons]
    cases hl : sptLookup k (ks.foldr sptDelete L) with
    | none =>
      have same : sptDelete k (ks.foldr sptDelete L) = ks.foldr sptDelete L := by
        apply (sptEqThm _ _ ⟨sptWfDelete _ k wfRest, wfRest⟩).2
        intro n
        rw [sptLookup_sptDelete]
        split
        · subst n; exact hl.symm
        · rfl
      rw [same]
    | some v =>
      have hv : ∃ i, v = .number i := by
        rw [lookup_foldr_delete] at hl
        split at hl
        · simp at hl
        · rcases hks k (List.mem_cons_self) with hn | ⟨i, hi⟩
          · rw [hn] at hl; simp at hl
          · rw [hi] at hl; exact ⟨i, (Option.some.inj hl).symm⟩
      obtain ⟨i, rfl⟩ := hv
      exact sizeOfHeap_delete_number_le k { state with locals := ks.foldr sptDelete L } i hl

/-- HOL's identity marker `STOP`, used to block rewriting in the append-loop
proofs. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "STOP_def"]
def stop {α : Type} (x : α) : α := x

/-- Cutting to fewer names, dropping at most two number-valued locals, cannot
increase the heap size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "configGC_size_of_heap_LE"]
theorem configGC_sizeOfHeap_le {C F C' F' : Type} (ns : NumSet) (s x : DataSem.State C F)
    (k1 k2 : Nat) (i1 i2 : Int) (state : DataSem.State C' F')
    (h : DataSem.cutStateOpt (some (sptInsert k2 () (sptInsert k1 () ns))) s = some x ∧
      sptLookup k1 x.locals = some (.number i1) ∧ sptLookup k2 x.locals = some (.number i2) ∧
      state.refs = s.refs ∧ state.limits = s.limits ∧ state.stack = s.stack ∧
      state.global = s.global) :
    DataSem.sizeOfHeap { state with locals := sptMkWf (sptInter s.locals ns) } ≤
      DataSem.sizeOfHeap { state with locals := x.locals } := by
  obtain ⟨hcut, h1, h2, -⟩ := h
  simp only [DataSem.cutStateOpt, DataSem.cutState, DataSem.cutEnv] at hcut
  split at hcut
  · simp only [Option.map_some, Option.some.injEq] at hcut
    subst hcut
    let extras := [k1, k2].filter (fun a => sptLookup a ns = none)
    have eq : extras.foldr sptDelete
        (sptMkWf (sptInter s.locals (sptInsert k2 () (sptInsert k1 () ns)))) =
        sptMkWf (sptInter s.locals ns) := by
      apply (sptEqThm _ _ ⟨wf_foldr_delete _ _ (sptWf_mkWf _), sptWf_mkWf _⟩).2
      intro n
      rw [lookup_foldr_delete, sptLookup_mkWf, sptLookup_mkWf, sptLookup_sptInterCases,
        sptLookup_sptInterCases]
      by_cases hn1 : n = k1 <;> by_cases hn2 : n = k2 <;>
        simp_all [extras, sptLookup_sptInsert] <;>
        (cases hns : sptLookup n ns <;> simp_all)
    rw [← eq]
    apply sizeOfHeap_foldr_delete_number_le
    refine ⟨sptWf_mkWf _, ?_⟩
    intro k hk
    simp only [extras, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at hk
    rcases hk with ⟨rfl | rfl, -⟩
    · exact Or.inr ⟨i1, h1⟩
    · exact Or.inr ⟨i2, h2⟩
  · simp at hcut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
