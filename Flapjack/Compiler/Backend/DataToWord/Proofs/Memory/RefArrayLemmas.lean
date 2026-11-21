module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.WordArith
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Preliminaries
public import Flapjack.Misc.Option
public import Flapjack.FiniteMap.AlistExact.Lookup

@[expose] public section

/-!
# Replicated references, byte words and list lemmas of `data_to_word_memoryProof`

Counterparts of `memory_rel_REPLICATE`, `memory_rel_RefArray`,
`word_of_byte_def`, `word_of_byte_0`, `LUPDATE_REPLICATE`, `IMP_EXP_LESS`,
`MOD_MULT_MOD_LEMMA`, `word_1_and_eq_0`, `or_seven_eq`, `or_1`, `FORALL_WORD`,
`IMP_THE_EQ`, `EVERY2_MAP_MAP`, `MEM_FIRST_EL`, `ALOOKUP_ZIP_EL`,
`ZIP_MAP_MAP`, `MIN_SUC_SUC` and `block_drop_def` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`REPLICATE` is `List.replicate`, `LUPDATE x a l` is `l.set a x`, `THE` is
`holThe`, `ALOOKUP` is `holALookup`, `EL` is `holEl`, `word_bit n w` is
written out as `n ≤ width - 1 ∧ w.getLsbD n = true` and `(h -- l) w` is the
reviewed `StackAlloc.gcWordBits`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- HOL `memory_rel_REPLICATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_REPLICATE"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_replicate {width : Nat} [NeZero width] (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (v : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : Nat) :
    memoryRel c be ts refs sp st m dm ((v, w) :: vars) →
      memoryRel c be ts refs sp st m dm (List.replicate n (v, w) ++ vars) := by
  apply memoryRel_rearrange
  intro pair member
  rcases List.mem_append.mp member with h | h
  · rw [List.eq_of_mem_replicate h]; simp
  · simp [h]

/-- HOL `memory_rel_RefArray`, the instance of `memory_rel_Ref` for a
replicated array, with HOL's `let` bindings kept. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefArray"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refArray {width : Nat} {tagWidth : Nat} [NeZero width] [NeZero tagWidth]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (v : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : Nat) (hd : BitVec width)
    (new : Nat) :
    memoryRel c be ts refs sp st m dm ((v, w) :: vars) ∧ DataToWord.encodeHeader c 2 n = some hd ∧
        ¬ sptDomain refs new ∧ n < sp ∧ goodDimindex width →
      ∃ eoh curr trig m1, st.lookup .endOfHeap = some (.word eoh) ∧
        st.lookup .triggerGC = some (.word trig) ∧ st.lookup .currHeap = some (.word curr) ∧
        (let w' := eoh - wordSemBytesInWord * BitVec.ofNat width (n + 1)
         let w1 := trig - wordSemBytesInWord * BitVec.ofNat width (n + 1)
         storeList w' (.word hd :: List.replicate n w) m dm = some m1 ∧
           memoryRel c be ts (sptInsert new (.valueArray (List.replicate n v)) refs) (sp - (n + 1))
             ((st.update (.endOfHeap, .word w')).update (.triggerGC, .word w1)) m1 dm
             ((.refPtr true new, Build.makePtr c (w' - curr) (0 : BitVec tagWidth) n) :: vars)) := by
  rintro ⟨rel, encoded, fresh, enough, good⟩
  have rel' : memoryRel c be ts refs sp st m dm
      ((List.replicate n v).zip (List.replicate n w) ++ vars) := by
    rw [zip_replicate]
    exact memoryRel_replicate c be ts refs sp st m dm v w vars n rel
  obtain ⟨eoh, curr, trig, m1, h1, h2, h3, h4, h5⟩ :=
    memoryRel_ref (tagWidth := tagWidth) c be ts refs sp st m dm (List.replicate n v) (List.replicate n w)
      vars hd new rel' (by simp) (by simpa using encoded) fresh (by simpa using enough) good
  refine ⟨eoh, curr, trig, m1, h1, h2, h3, ?_⟩
  simp only [List.length_replicate] at h4 h5
  exact ⟨h4, h5⟩

/-- HOL `word_of_byte_def`: a byte replicated across the word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_of_byte_def"
  (words_as_type_indexed_bitvec)]
def wordOfByte {width : Nat} [NeZero width] (w : BitVec width) : BitVec width :=
  let w := w <<< 8 ||| w
  let w := w <<< 16 ||| w
  if width = 32 then w else w <<< 32 ||| w

/-- HOL `word_of_byte_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_of_byte_0"
  (words_as_type_indexed_bitvec)]
theorem wordOfByte_zero {width : Nat} [NeZero width] : wordOfByte (0 : BitVec width) = 0 := by
  unfold wordOfByte
  split <;> simp

/-- HOL `LUPDATE_REPLICATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LUPDATE_REPLICATE"]
theorem set_replicate {α : Type} (x : α) :
    ∀ n a : Nat, (List.replicate n x).set a x = List.replicate n x := by
  intro n a
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_replicate]
  split <;> rfl

/-- HOL `IMP_EXP_LESS`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_EXP_LESS"]
theorem imp_exp_less (m l : Nat) : m ≤ l → 2 ^ m ≤ 2 ^ l :=
  fun h => Nat.pow_le_pow_right (by decide) h

/-- HOL `MOD_MULT_MOD_LEMMA`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MOD_MULT_MOD_LEMMA"]
theorem mod_mult_mod_lemma (k n x t : Nat) :
    k % n = 0 ∧ x % n = t ∧ 0 < k ∧ 0 < n ∧ n ≤ k → x % k % n = t := by
  rintro ⟨dvd, rfl, -, -, -⟩
  exact Nat.mod_mod_of_dvd x (Nat.dvd_of_mod_eq_zero dvd)

/-- HOL `word_1_and_eq_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_1_and_eq_0"
  (words_as_type_indexed_bitvec)]
theorem one_and_eq_zero {width : Nat} [NeZero width] (w : BitVec width) :
    (1 &&& w = 0) ↔ ¬ (0 ≤ width - 1 ∧ w.getLsbD 0 = true) := by
  have pos : 0 < width := NeZero.pos width
  have one0 : (1 : BitVec width).getLsbD 0 = true := by
    show (BitVec.ofNat width 1).getLsbD 0 = true
    rw [BitVec.getLsbD_ofNat]
    simp [pos]
  constructor
  · intro h ⟨_, bit⟩
    have := congrArg (fun v : BitVec width => v.getLsbD 0) h
    have z0 : (0 : BitVec width).getLsbD 0 = false := by simp
    simp only [BitVec.getLsbD_and, one0, bit, Bool.and_self, z0] at this
    exact Bool.noConfusion this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have z0 : (0 : BitVec width).getLsbD i = false := by simp
    rw [BitVec.getLsbD_and, z0]
    by_cases z : i = 0
    · subst z
      have : w.getLsbD 0 = false := by
        cases hb : w.getLsbD 0
        · rfl
        · exact absurd ⟨Nat.zero_le _, hb⟩ h
      rw [this, Bool.and_false]
    · have : (1 : BitVec width).getLsbD i = false := by
        show (BitVec.ofNat width 1).getLsbD i = false
        rw [BitVec.getLsbD_ofNat]
        have tb : Nat.testBit 1 i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [tb]
      rw [this, Bool.false_and]

/-- HOL `or_seven_eq`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "or_seven_eq"
  (words_as_type_indexed_bitvec)]
theorem or_seven_eq {width : Nat} [NeZero width] (w v : BitVec width) (k : Nat) :
    w <<< k ≠ v <<< k ∧ 2 < k → (w <<< k ||| 7) ≠ (v <<< k ||| 7) := by
  rintro ⟨ne, lt⟩ eq
  apply ne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bit := congrArg (fun x : BitVec width => x.getLsbD i) eq
  simp only [BitVec.getLsbD_or] at bit
  by_cases small : i < k
  · rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
    simp [small]
  · have seven : (7 : BitVec width).getLsbD i = false := by
      show (BitVec.ofNat width 7).getLsbD i = false
      rw [BitVec.getLsbD_ofNat]
      have : Nat.testBit 7 i = false := by
        apply Nat.testBit_lt_two_pow
        calc 7 < 2 ^ 3 := by decide
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      simp [this]
    simpa only [seven, Bool.or_false] using bit

/-- HOL `or_1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "or_1"
  (words_as_type_indexed_bitvec)]
theorem or_one {width : Nat} [NeZero width] :
    ∀ w : BitVec width, (StackAlloc.gcWordBits 0 0 w ||| 1) = 1 := by
  intro w
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, StackAlloc.getLsbD_gcWordBits]
  by_cases z : i = 0
  · simp [z]
    intro h _
    exact h
  · simp [z]

/-- HOL `FORALL_WORD`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "FORALL_WORD"
  (words_as_type_indexed_bitvec)]
theorem forall_word {width : Nat} [NeZero width] (P : BitVec width → Prop) :
    (∀ v, P v) ↔ ∀ n, n < 2 ^ width → P (BitVec.ofNat width n) := by
  constructor
  · intro h n _; exact h _
  · intro h v
    have := h v.toNat v.isLt
    simpa using this

/-- HOL `IMP_THE_EQ`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_THE_EQ"
  (total_function_inhabitants := [α])]
theorem imp_the_eq {α : Type} [Nonempty α] (x : Option α) (w : α) : x = some w → holThe x = w := by
  rintro rfl
  rfl

/-- HOL `EVERY2_MAP_MAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_MAP_MAP"]
theorem every2_map_map {α β γ : Type} (P : β → γ → Prop) (f : α → β) (g : α → γ) :
    ∀ xs : List α, List.Forall₂ P (xs.map f) (xs.map g) ↔ ∀ x ∈ xs, P (f x) (g x) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.forall₂_cons, ih]

/-- HOL `MEM_FIRST_EL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_FIRST_EL"
  (total_function_inhabitants := [α])]
theorem mem_first_el {α : Type} [Nonempty α] :
    ∀ (xs : List α) (x : α), x ∈ xs ↔
      ∃ n, n < xs.length ∧ holEl n xs = x ∧ ∀ m, m < n → holEl m xs ≠ holEl n xs := by
  intro xs
  induction xs with
  | nil => intro x; simp
  | cons y ys ih =>
    intro x
    classical
    constructor
    · intro member
      by_cases eq : y = x
      · exact ⟨0, by simp, eq, fun m h => absurd h (Nat.not_lt_zero _)⟩
      · have inYs : x ∈ ys := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h.symm eq
          · exact h
        obtain ⟨n, lt, el, first⟩ := (ih x).mp inYs
        refine ⟨n + 1, by simpa using lt, by simpa [holEl_cons_succ] using el, ?_⟩
        intro m hm
        cases m with
        | zero =>
          intro h
          apply eq
          rw [holEl_cons_succ, el] at h
          simpa [holEl, holHd] using h
        | succ m =>
          simp only [holEl_cons_succ]
          exact first m (by omega)
    · rintro ⟨n, lt, rfl, -⟩
      rw [holEl_eq_getElem n _ lt]
      exact List.getElem_mem lt

/-- HOL `ALOOKUP_ZIP_EL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ALOOKUP_ZIP_EL"
  (total_function_inhabitants := [α, β])]
theorem alookup_zip_el {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (xs : List α) (hs : List β) (n : Nat),
      n < xs.length ∧ hs.length = xs.length ∧ (∀ m, m < n → holEl m xs ≠ holEl n xs) →
      holALookup (xs.zip hs) (holEl n xs) = some (holEl n hs) := by
  intro xs
  induction xs with
  | nil => rintro hs n ⟨h, -⟩; simp at h
  | cons x xs ih =>
    rintro hs n ⟨lt, len, first⟩
    cases hs with
    | nil => simp at len
    | cons h hs =>
      cases n with
      | zero => simp [holALookup, holEl, holHd]
      | succ n =>
        have ne : holEl (n + 1) (x :: xs) ≠ x := by
          intro e
          exact first 0 (by omega) (by simpa [holEl, holHd] using e.symm)
        simp only [List.zip_cons_cons, holALookup, holEl_cons_succ] at ne ⊢
        rw [if_neg ne]
        exact ih hs n ⟨by simpa using lt, by simpa using len,
          fun m hm => by simpa [holEl_cons_succ] using first (m + 1) (by omega)⟩

/-- HOL `ZIP_MAP_MAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ZIP_MAP_MAP"]
theorem zip_map_map {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ xs : List α, List.zip (xs.map f) (xs.map g) = xs.map (fun k => (f k, g k)) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- HOL `MIN_SUC_SUC`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MIN_SUC_SUC"]
theorem min_succ_succ (m n : Nat) : min (m + 1) (n + 1) = min m n + 1 := by omega

/-- HOL `block_drop_def`: follow `n` cons-cell tails of a list value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "block_drop_def"]
def blockDrop : Nat → Flapjack.Compiler.Backend.DataSem.Value → Option Flapjack.Compiler.Backend.DataSem.Value
  | 0, v => some v
  | n + 1, .block _ _ [_, vl] => blockDrop n vl
  | _ + 1, _ => none

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
