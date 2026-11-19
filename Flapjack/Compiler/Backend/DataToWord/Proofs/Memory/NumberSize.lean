module

public import Flapjack.Compiler.Backend.DataSpace.Requirements
public import Flapjack.Misc.Multiword.Length
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.DataToWord.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
@[expose] public section

/-! Constant-part size bounds for data-to-word memory correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- A bounded magnitude occupies at most the source number-space estimate. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LESS_EQ_num_size"
  (words_as_type_indexed_bitvec)]
theorem length_n2mw_le_numSize {width : Nat} [NeZero width] (good : goodDimindex width)
    (m n : Nat) (bound : n ≤ m) :
    (Misc.Multiword.n2mw n : List (BitVec width)).length + 1 ≤ DataSpace.numSize m := by
  have baseLe : 4294967296 ≤ 2 ^ width := by
    rcases good with h | h <;> rw [h] <;> decide
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    by_cases small : m < 4294967296
    · have nSmall : n < 2 ^ width := by omega
      have nDiv : n / 2 ^ width = 0 := Nat.div_eq_of_lt nSmall
      by_cases zero : n = 0
      · simp [Misc.Multiword.n2mw, DataSpace.numSize, small, zero]
      · simp [Misc.Multiword.n2mw, DataSpace.numSize, small, zero, nDiv]
    · have mPos : 0 < m := by omega
      have smaller : m / 4294967296 < m := Nat.div_lt_self mPos (by decide)
      by_cases zero : n = 0
      · subst n
        rw [DataSpace.numSize, if_neg small]
        simp only [Misc.Multiword.n2mw, ↓reduceIte, List.length_nil]
        omega
      · have divBound : n / 2 ^ width ≤ m / 4294967296 :=
          Nat.le_trans (Nat.div_le_div_right bound) (Nat.div_le_div_left baseLe (by decide))
        have next := ih (m / 4294967296) smaller (n / 2 ^ width) divBound
        rw [DataSpace.numSize, if_neg small]
        rw [Misc.Multiword.n2mw, if_neg zero]
        simp only [List.length_cons]
        omega

/-- Small magnitudes fit the immediate integer range at either supported width. -/
private theorem small_of_abs {width : Nat} [NeZero width] (i : Int) (good : goodDimindex width)
    (bound : i.natAbs < 536870912) : smallInt width i := by
  unfold smallInt
  rcases good with h | h <;> rw [h] <;> cases i <;> simp_all [Int.natAbs] <;> omega

/-- Lowering one constant part uses at most its source space requirement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "part_to_words_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem partWords_length {width : Nat} [NeZero width] (conf : Config) (memory : Spt (Build.Value width))
    (part : ClosLang.ConstPart) (off : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (run : Build.partWords conf memory part off = some (w,ws)) (good : goodDimindex width) :
    ws.length ≤ DataSpace.partSpaceReq part := by
  classical
  cases part with
  | con tag refs =>
    cases refs with
    | nil => simp [Build.partWords] at run; simp [DataSpace.partSpaceReq, ← run.2]
    | cons x xs =>
      simp only [Build.partWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases h : encodeHeader (width := width) conf (4 * tag) (xs.length + 1) with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨_, rfl⟩ := run
        simp [DataSpace.partSpaceReq]
  | w64 w64 =>
    by_cases narrow : width < 64
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 2 <;> simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 1 <;> simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp
  | int i =>
    by_cases small : smallInt width i
    · simp [Build.partWords, small] at run
      obtain ⟨_, rfl⟩ := run
      simp
    · have absBig : ¬ i.natAbs < 536870912 := fun h => small (small_of_abs i good h)
      have bound := length_n2mw_le_numSize good i.natAbs i.natAbs (Nat.le_refl _)
      simp only [Build.partWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run
      cases h : encodeHeader (width := width) conf (if decide (i < 0) then 7 else 3)
          (Misc.Multiword.n2mw (width := width) i.natAbs).length <;>
        simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp only [List.length_cons, List.length_map]
      split <;> omega
  | str text =>
    simp only [Build.partWords] at run
    split at run
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      simp only [List.length_map, List.length_cons, writeBytes_wordCount, List.length_replicate]
      simp only [DataSpace.partSpaceReq]
      rw [Flapjack.Basis.Pure.MlString.MlString.length_explode]
      rcases good with hw | hw
      · simp [Build.byteLen, hw]
      · simp only [Build.byteLen, hw]
        norm_num
        have bound : text.strlen / 8 ≤ text.strlen / 4 := Nat.div_le_div_left (by decide) (by decide)
        omega

/-- The list induction for the constant-lowering space bound. -/
private theorem partsWords_length {width : Nat} [NeZero width] (parts : List ClosLang.ConstPart)
    (conf : Config) (memory : Spt (Build.Value width)) (index : Nat) (off : BitVec width)
    (w : Build.Value width) (ws : List (Build.Value width))
    (run : Build.partsToWords conf memory index parts off = some (w,ws)) (good : goodDimindex width) :
    ws.length ≤ (parts.map DataSpace.partSpaceReq).sum := by
  induction parts generalizing memory index off w ws with
  | nil => simp [Build.partsToWords] at run; simp [← run.2]
  | cons part rest ih =>
    simp only [Build.partsToWords] at run
    cases hp : Build.partWords conf memory part off with
    | none => simp [hp] at run
    | some first =>
      obtain ⟨v, words⟩ := first
      simp [hp] at run
      cases ht : Build.partsToWords conf (sptInsert index v memory) (index + 1) rest
        (off + wordSemBytesInWord * BitVec.ofNat width words.length) with
      | none => simp [ht] at run
      | some tail =>
        obtain ⟨v2, words2⟩ := tail
        simp [ht] at run
        obtain ⟨_, rfl⟩ := run
        have h1 := partWords_length conf memory part off v words hp good
        have h2 := ih _ _ _ _ _ ht
        simp only [List.length_append, List.map_cons, List.sum_cons]
        omega

/-- A complete constant layout fits the sum of its part requirements. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "const_parts_to_words_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem constPartsWords_length {width : Nat} [NeZero width] (conf : Config)
    (parts : List ClosLang.ConstPart) (w : Bool × WordLocW width) (ws : List (Bool × WordLocW width))
    (run : Build.partsWords conf parts = some (w,ws)) (good : goodDimindex width) :
    ws.length ≤ (parts.map DataSpace.partSpaceReq).sum := by
  apply partsWords_length parts conf .ln 0 0 w ws
  · exact run
  · exact good

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
