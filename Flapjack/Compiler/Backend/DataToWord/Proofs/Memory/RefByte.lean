module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefArrayLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WriteBytes
public import Flapjack.Byte.GetSetByte

@[expose] public section

/-!
# Fresh byte arrays filled with one byte

Counterparts of the `memory_rel_RefByte_alt` group of
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`:
`word_of_byte` facts, `write_bytes` of replicated bytes, `last_bytes`, and the
memory relation for a byte array filled with a single byte. HOL `w2w` from
`word8` to `'a word` is `BitVec.setWidth width` (zero extension) and the
converse `w2w` is `BitVec.setWidth 8` (truncation).
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

/-- Every bit of a replicated byte is the corresponding byte bit. Flapjack
infrastructure for `set_byte_word_of_byte`. -/
theorem wordOfByte_getLsbD {width : Nat} [NeZero width] (good : goodDimindex width)
    (w : BitVec 8) (j : Nat) (hj : j < width) :
    (wordOfByte (w.setWidth width)).getLsbD j = w.getLsbD (j % 8) := by
  rcases good with h | h <;> subst h <;> unfold wordOfByte <;>
    interval_cases j <;> simp

/-- Byte lanes start at multiples of eight. Flapjack infrastructure. -/
theorem byteIndex_mod_eight {width : Nat} [NeZero width] (a : BitVec width) (be : Bool) :
    byteIndex a be % 8 = 0 := by
  simp only [byteIndex]
  split <;> omega

/-- Exact HOL `set_byte_word_of_byte` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "set_byte_word_of_byte"
  (words_as_type_indexed_bitvec)]
theorem setByte_wordOfByte {width : Nat} [NeZero width] (a : BitVec width) (w : BitVec 8) (be : Bool) :
    goodDimindex width → setByte a w (wordOfByte (w.setWidth width)) be = wordOfByte (w.setWidth width) := by
  intro good
  have h8 : 8 ≤ width := by rcases good with h | h <;> omega
  have hle := byteIndex_add_le h8 a be
  have hm := byteIndex_mod_eight a be
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_setByte a w _ be j hj, wordOfByte_getLsbD good w j hj]
  by_cases h1 : byteIndex a be + 8 ≤ j
  · simp [h1, show byteIndex a be ≤ j by omega, show ¬ j < byteIndex a be by omega,
      BitVec.getLsbD_of_ge w (j - byteIndex a be) (by omega)]
  · by_cases h2 : byteIndex a be ≤ j
    · simp only [h1, h2, decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or,
        show ¬ j < byteIndex a be by omega, Bool.or_false]
      congr 1
      omega
    · simp [h1, h2, show j < byteIndex a be by omega]

/-- Exact HOL `w2w_word_of_byte_w2w`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "w2w_word_of_byte_w2w"
  (words_as_type_indexed_bitvec)]
theorem setWidth_wordOfByte_setWidth {width : Nat} [NeZero width] (w : BitVec 8) :
    goodDimindex width → (wordOfByte (w.setWidth width)).setWidth 8 = w := by
  intro good
  have h8 : 8 ≤ width := by rcases good with h | h <;> omega
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_setWidth, wordOfByte_getLsbD good w j (by omega), Nat.mod_eq_of_lt hj]
  simp [hj]

/-- Writing replicated bytes into a replicated word changes nothing. Flapjack
infrastructure for `write_bytes_REPLICATE`. -/
theorem bytesToWord_replicate_wordOfByte {width : Nat} [NeZero width] (good : goodDimindex width)
    (w : BitVec 8) (be : Bool) :
    ∀ (c : Nat) (a : BitVec width) (m : Nat),
      bytesToWord c a (List.replicate m w) (wordOfByte (w.setWidth width)) be = wordOfByte (w.setWidth width) := by
  intro c
  induction c with
  | zero => intro a m; simp [bytesToWord]
  | succ c ih =>
    intro a m
    cases m with
    | zero => simp [bytesToWord]
    | succ m =>
      rw [List.replicate_succ, bytesToWord, ih, setByte_wordOfByte a w be good]

/-- Exact HOL `write_bytes_REPLICATE` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytes_REPLICATE"
  (words_as_type_indexed_bitvec)]
theorem writeBytes_replicate {width : Nat} [NeZero width] (w : BitVec 8) (be : Bool) :
    ∀ (n m : Nat), goodDimindex width →
      writeBytes (List.replicate m w) (List.replicate n (wordOfByte (w.setWidth width))) be =
        List.replicate n (wordOfByte (w.setWidth width)) := by
  intro n
  induction n with
  | zero => intro m _; simp [writeBytes]
  | succ n ih =>
    intro m good
    rw [List.replicate_succ, writeBytes, bytesToWord_replicate_wordOfByte good, List.drop_replicate, ih _ good]

/-- Exact HOL `last_bytes_def`: write `k` copies of byte `b` from address `a`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "last_bytes_def"
  (words_as_type_indexed_bitvec)]
def lastBytes {width : Nat} [NeZero width] (k : Nat) (b : BitVec 8) (a w : BitVec width) (be : Bool) :
    BitVec width :=
  if k = 0 then w else setByte a b (lastBytes (k - 1) b (a + 1#width) w be) be
termination_by k
decreasing_by omega

/-- Exact HOL `last_bytes_bytes_to_word_REPLICATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "last_bytes_bytes_to_word_REPLICATE"
  (words_as_type_indexed_bitvec)]
theorem lastBytes_bytesToWord_replicate {width : Nat} [NeZero width] (b1 b2 : BitVec 8) (be : Bool) :
    ∀ (n1 n k : Nat) (a w : BitVec width),
      n ≤ k ∧ b1 = b2 ∧ n1 = n → bytesToWord k a (List.replicate n b2) w be = lastBytes n1 b1 a w be := by
  intro n1 n
  induction n generalizing n1 with
  | zero =>
    rintro k a w ⟨-, -, rfl⟩
    rw [lastBytes]
    cases k <;> simp [bytesToWord]
  | succ n ih =>
    rintro k a w ⟨hk, rfl, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [lastBytes, if_neg (by omega), List.replicate_succ, bytesToWord,
      ih n k (a + 1) w ⟨by omega, rfl, rfl⟩]
    rfl


/-- Bits outside the lanes written by `bytes_to_word` keep their agreement.
Flapjack infrastructure for `write_bytes_change_extra`. -/
theorem bytesToWord_agree {width : Nat} [NeZero width] (be : Bool) :
    ∀ (c : Nat) (a : BitVec width) (bs : List (BitVec 8)) (x x' : BitVec width) (S : Nat → Prop),
      c ≤ bs.length →
      (∀ j < width, ¬ S j →
        (∀ i < c, ¬ (byteIndex (a + BitVec.ofNat width i) be ≤ j ∧ j < byteIndex (a + BitVec.ofNat width i) be + 8)) →
        x.getLsbD j = x'.getLsbD j) →
      ∀ j < width, ¬ S j → (bytesToWord c a bs x be).getLsbD j = (bytesToWord c a bs x' be).getLsbD j := by
  intro c
  induction c with
  | zero =>
    intro a bs x x' S _ agree j hj hS
    simp only [bytesToWord]
    exact agree j hj hS (fun i hi => absurd hi (Nat.not_lt_zero i))
  | succ c ih =>
    intro a bs x x' S hlen agree j hj hS
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [bytesToWord]
      rw [getLsbD_setByte _ _ _ _ _ hj, getLsbD_setByte _ _ _ _ _ hj]
      by_cases lane : byteIndex a be ≤ j ∧ j < byteIndex a be + 8
      · simp [show ¬ byteIndex a be + 8 ≤ j by omega, lane.1, show ¬ j < byteIndex a be by omega]
      · have inner := ih (a + 1) bs x x' (fun j => S j ∨ (byteIndex a be ≤ j ∧ j < byteIndex a be + 8))
          (by simp at hlen; omega)
          (by
            intro j hj hS' none
            apply agree j hj (fun h => hS' (Or.inl h))
            intro i hi
            cases i with
            | zero => simpa using fun h => hS' (Or.inr h)
            | succ i =>
              have e : a + BitVec.ofNat width (i + 1) = a + 1 + BitVec.ofNat width i := by
                rw [BitVec.add_assoc]
                congr 1
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_add, Nat.add_comm]
              rw [e]
              exact none i (by omega))
          j hj (by simp [hS, lane])
        rw [inner]

/-- `bytes_to_word` over all lanes of a word ignores the initial word.
Flapjack infrastructure for `write_bytes_change_extra`. -/
theorem bytesToWord_full {width : Nat} [NeZero width] (good : goodDimindex width) (be : Bool)
    (bs : List (BitVec 8)) (x x' : BitVec width) (hlen : width / 8 ≤ bs.length) :
    bytesToWord (width / 8) 0 bs x be = bytesToWord (width / 8) 0 bs x' be := by
  have hw8 : width % 8 = 0 := by rcases good with h | h <;> subst h <;> rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  refine bytesToWord_agree be (width / 8) 0 bs x x' (fun _ => False) hlen ?_ j hj (by simp)
  intro j hj _ none
  exfalso
  have small : width / 8 < 2 ^ width := by
    rcases good with h | h <;> subst h <;> decide
  cases be with
  | false =>
    apply none (j / 8) (by omega)
    have t : (0 + BitVec.ofNat width (j / 8)).toNat = j / 8 := by
      simp [Nat.mod_eq_of_lt (show j / 8 < 2 ^ width by omega)]
    simp only [byteIndex, t, Bool.false_eq_true, if_false]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  | true =>
    apply none (width / 8 - 1 - j / 8) (by omega)
    have t : (0 + BitVec.ofNat width (width / 8 - 1 - j / 8)).toNat = width / 8 - 1 - j / 8 := by
      simp [Nat.mod_eq_of_lt (show width / 8 - 1 - j / 8 < 2 ^ width by omega)]
    simp only [byteIndex, t, if_true]
    rw [Nat.mod_eq_of_lt (by omega)]
    rcases good with h | h <;> subst h <;> omega

/-- Exact HOL `write_bytes_change_extra`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytes_change_extra"
  (words_as_type_indexed_bitvec)]
theorem writeBytes_changeExtra {width : Nat} [NeZero width] :
    ∀ (ws : List (BitVec width)) (bs : List (BitVec 8)) (be : Bool) (ws' : List (BitVec width)),
      goodDimindex width ∧ ws.length = ws'.length ∧ ws.length < Build.byteLen width bs.length →
      writeBytes bs ws be = writeBytes bs ws' be := by
  intro ws
  induction ws with
  | nil =>
    rintro bs be ws' ⟨-, hl, -⟩
    cases ws' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x ws ih =>
    rintro bs be ws' ⟨good, hl, hb⟩
    cases ws' with
    | nil => simp at hl
    | cons x' ws' =>
      simp only [List.length_cons] at hl hb
      simp only [writeBytes]
      congr 1
      · apply bytesToWord_full good
        rcases good with h | h <;> subst h <;> simp only [Build.byteLen] at hb <;> norm_num at hb ⊢ <;> omega
      · apply ih
        refine ⟨good, by omega, ?_⟩
        rcases good with h | h <;> subst h <;> simp only [Build.byteLen, List.length_drop] at hb ⊢ <;>
          norm_num at hb ⊢ <;> omega


/-- The packed words of `n` copies of one byte: whole replicated words and a
final partial word. Flapjack infrastructure for `memory_rel_RefByte_alt`. -/
theorem writeBytes_replicate_last {width : Nat} [NeZero width] (good : goodDimindex width)
    (w : BitVec 8) (be : Bool) (n : Nat) :
    (writeBytes (List.replicate n w) (List.replicate (Build.byteLen width n) (0 : BitVec width)) be).map WordLocW.word =
      (List.replicate (Build.byteLen width n) (WordLocW.word (wordOfByte (w.setWidth width)))).set
        (Build.byteLen width n - 1) (.word (lastBytes (n % (width / 8)) w 0 0 be)) := by
  have hL : Build.byteLen width n = n / (width / 8) + 1 := by
    rcases good with h | h <;> subst h <;> simp [Build.byteLen]
  have hk : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  rw [hL, Nat.add_sub_cancel, List.replicate_succ', writeBytes_append, List.length_replicate,
    writeBytes_changeExtra _ _ be (List.replicate (n / (width / 8)) (wordOfByte (w.setWidth width)))
      ⟨good, by simp, by simp only [List.length_replicate, hL]; omega⟩,
    writeBytes_replicate w be _ _ good, List.drop_replicate,
    show n - width / 8 * (n / (width / 8)) = n % (width / 8) by rw [Nat.mod_eq_sub_mul_div]]
  simp only [writeBytes, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
  rw [lastBytes_bytesToWord_replicate w w be (n % (width / 8)) (n % (width / 8)) (width / 8) 0 0
    ⟨(Nat.mod_lt _ hk).le, rfl, rfl⟩]
  rw [List.replicate_succ', List.set_append_right _ _ (by simp)]
  simp

/-- Exact HOL `memory_rel_RefByte_alt`. HOL's `make_ptr` tag `0w` has an
independent word type, rendered at the separately quantified positive width
`tagWidth`, as in the reviewed `memory_rel_Ref`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefByte_alt"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refByteAlt {width tagWidth : Nat} [NeZero width] [NeZero tagWidth]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (new n : Nat) (w : BitVec 8) (fl : Bool) :
    memoryRel c be ts refs sp st m dm vars ∧ ¬ sptDomain refs new ∧ Build.byteLen width n < sp ∧
      Build.byteLen width n < 2 ^ (width - 4) ∧ Build.byteLen width n < 2 ^ c.lenSize ∧ goodDimindex width →
    ∃ free curr m1, st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      (let w' := wordSemBytesInWord * BitVec.ofNat width (Build.byteLen width n + 1)
       let ws := List.replicate (Build.byteLen width n) (WordLocW.word (wordOfByte (w.setWidth width)))
       let nb := n % (width / 8)
       let ws := ws.set (Build.byteLen width n - 1) (.word (lastBytes nb w 0 0 be))
       storeList free (.word (makeByteHeader c fl n) :: ws) m dm = some m1 ∧
       memoryRel c be ts (sptInsert new (.byteArray fl (List.replicate n w)) refs)
         (sp - (Build.byteLen width n + 1)) (st.update (.nextFree, .word (free + w'))) m1 dm
         ((.refPtr true new, Build.makePtr c (free - curr) (0 : BitVec tagWidth) (Build.byteLen width n)) :: vars)) := by
  rintro ⟨rel, fresh, enough, countBound, lenBound, good⟩
  obtain ⟨free, curr, m1, h1, h2, h3, h4⟩ :=
    memoryRel_freshByte c be ts refs sp st m dm vars new n fl (List.replicate n w) rel fresh enough
      countBound lenBound (by simp) good
  refine ⟨free, curr, m1, h1, h2, ?_, h4⟩
  rw [← writeBytes_replicate_last good w be n]
  exact h3
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
