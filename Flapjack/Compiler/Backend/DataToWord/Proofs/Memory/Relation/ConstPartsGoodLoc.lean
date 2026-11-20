module

public import Flapjack.Compiler.Backend.DataToWord.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.GoodLoc

@[expose] public section

/-! Location validity of lowered constant layouts. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A part preserves validity when prior constant-memory lookups are valid. -/
private theorem partWords_good {width : Nat} [NeZero width] (conf : Config)
    (memory : Spt (Build.Value width)) (code : Nat → Prop) (part : ClosLang.ConstPart)
    (off : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (memoryGood : ∀ k, goodLoc code (Build.lookupMem memory k).2)
    (run : Build.partWords conf memory part off = some (w, ws)) :
    goodLoc code w.2 ∧ ∀ v ∈ ws, goodLoc code v.2 := by
  classical
  cases part with
  | con tag refs =>
    cases refs with
    | nil =>
      simp [Build.partWords] at run
      obtain ⟨_, rfl, rfl⟩ := run
      simp [goodLoc]
    | cons x xs =>
      simp only [Build.partWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases h : encodeHeader (width := width) conf (4 * tag) (xs.length + 1) with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp only [goodLoc, true_and, List.mem_cons, List.mem_map, forall_eq_or_imp]
        constructor
        · exact memoryGood x
        · intro val mem
          obtain ⟨k, _, rfl⟩ := mem
          exact memoryGood k
  | int i =>
    by_cases small : smallInt width i
    · simp [Build.partWords, small] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [goodLoc]
    · simp only [Build.partWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run
      cases h : encodeHeader (width := width) conf (if decide (i < 0) then 7 else 3)
          (Misc.Multiword.n2mw (width := width) i.natAbs).length with
      | none =>
        simp only [decide_eq_true_eq] at h
        simp [h] at run
      | some header =>
        simp only [decide_eq_true_eq] at h
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [goodLoc, Build.makePtr]
  | w64 word =>
    by_cases narrow : width < 64
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 2 <;> simp [h] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [goodLoc, Build.makePtr]
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 1 <;> simp [h] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [goodLoc, Build.makePtr]
  | str text =>
    simp only [Build.partWords] at run
    split at run
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [goodLoc, Build.makePtr]

/-- The list induction threads valid constant-memory lookups. -/
private theorem partsWords_good {width : Nat} [NeZero width] (parts : List ClosLang.ConstPart)
    (conf : Config) (memory : Spt (Build.Value width)) (code : Nat → Prop)
    (index : Nat) (off : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (memoryGood : ∀ k, goodLoc code (Build.lookupMem memory k).2)
    (run : Build.partsToWords conf memory index parts off = some (w,ws)) :
    goodLoc code w.2 ∧ ∀ v ∈ ws, goodLoc code v.2 := by
  induction parts generalizing memory index off w ws with
  | nil =>
    simp [Build.partsToWords] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [memoryGood]
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
        obtain ⟨rfl, rfl⟩ := run
        have ⟨valueGood, wordsGood⟩ := partWords_good conf memory code part off v words memoryGood hp
        have nextGood : ∀ k, goodLoc code (Build.lookupMem (sptInsert index v memory) k).2 := by
          intro k
          by_cases h : k = index
          · subst k
            simpa [Build.lookupMem, sptLookup_sptInsert_same] using valueGood
          · simpa [Build.lookupMem, sptLookup_sptInsert_ne, h] using memoryGood k
        have ⟨resultGood, tailGood⟩ := ih _ _ _ _ _ nextGood ht
        refine ⟨resultGood, ?_⟩
        intro value member
        rcases List.mem_append.mp member with h | h
        · exact wordsGood value h
        · exact tailGood value h

/-- Every location in a successfully lowered constant layout is valid. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "const_parts_to_words_good_loc"
  (words_as_type_indexed_bitvec)]
theorem constPartsWords_good {width : Nat} [NeZero width] (conf : Config)
    (parts : List ClosLang.ConstPart) (code : Nat → Prop) (b : Bool) (value : WordLocW width)
    (ws : List (Bool × WordLocW width))
    (run : Build.partsWords conf parts = some ((b, value), ws)) :
    goodLoc code value ∧ ∀ v ∈ ws, goodLoc code v.2 := by
  apply partsWords_good parts conf .ln code 0 0 (b, value) ws
  · intro k
    simp [Build.lookupMem, goodLoc]
  · exact run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
