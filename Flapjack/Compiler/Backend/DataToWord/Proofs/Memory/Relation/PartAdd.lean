module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BuildCorrespondence
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCondAdd
@[expose] public section

/-! Relocation of constant parts under a change of allocation base. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Relocating the memory and base relocates a successfully built constant part. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "part_to_words_add"
  (words_as_type_indexed_bitvec)]
theorem partWords_add {width : Nat} [NeZero width] (conf : Config)
    (part : ClosLang.ConstPart) (memory : Spt (Build.Value width))
    (off a : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (memory1 : Spt (Build.Value width))
    (offAligned : holByteAligned off = true) (aAligned : holByteAligned a = true)
    (good : goodDimindex width) (shiftBound : wordShiftAmount width ≤ shiftLength conf)
    (run : Build.partWords conf memory part off = some (w, ws))
    (memoryRel : ∀ i, (Build.lookupMem memory1 i).2 = wordCondAdd conf a (Build.lookupMem memory i)) :
    ∃ v vs, Build.partWords conf memory1 part (off + a) = some (v, vs) ∧
      vs.map Prod.snd = ws.map (wordCondAdd conf a) ∧ v.2 = wordCondAdd conf a w := by
  have sumAligned : holByteAligned (off + a) = true := by
    unfold holByteAligned at offAligned aAligned ⊢
    rw [(alignedAddSub _ _ _ aAligned).1]
    exact offAligned
  cases part with
  | con tag refs =>
    cases refs with
    | nil =>
      simp [Build.partWords] at run ⊢
      obtain ⟨bound, rfl, rfl⟩ := run
      simp [bound, wordCondAdd]
    | cons x xs =>
      simp only [Build.partWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run ⊢
      cases h : encodeHeader (width := width) conf (4 * tag) (xs.length + 1) with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [wordCondAdd, List.map_map, memoryRel, BitVec.shiftLeft_add_distrib, BitVec.add_assoc,
          BitVec.add_comm]
  | int i =>
    by_cases small : smallInt width i
    · simp [Build.partWords, small] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      simp [wordCondAdd]
    · simp only [Build.partWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run ⊢
      cases h : encodeHeader (width := width) conf (if i < 0 then 7 else 3)
          (Misc.Multiword.n2mw (width := width) i.natAbs).length with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [h, makePtr_add conf off _ _ offAligned good shiftBound,
          makePtr_add conf (off + a) _ _ sumAligned good shiftBound,
          wordCondAdd, List.map_map, BitVec.shiftLeft_add_distrib, BitVec.add_assoc,
          BitVec.add_comm]
  | w64 word =>
    by_cases narrow : width < 64
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run ⊢
      cases h : encodeHeader (width := width) conf 3 2 with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [makePtr_add conf off _ _ offAligned good shiftBound,
          makePtr_add conf (off + a) _ _ sumAligned good shiftBound, wordCondAdd,
          BitVec.shiftLeft_add_distrib, BitVec.add_assoc, BitVec.add_comm]
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run ⊢
      cases h : encodeHeader (width := width) conf 3 1 with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [makePtr_add conf off _ _ offAligned good shiftBound,
          makePtr_add conf (off + a) _ _ sumAligned good shiftBound, wordCondAdd,
          BitVec.shiftLeft_add_distrib, BitVec.add_assoc, BitVec.add_comm]
  | str s =>
    simp only [Build.partWords] at run ⊢
    split at run
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp_all [makePtr_add conf off _ _ offAligned good shiftBound,
        makePtr_add conf (off + a) _ _ sumAligned good shiftBound, wordCondAdd,
        List.map_map, BitVec.shiftLeft_add_distrib, BitVec.add_assoc, BitVec.add_comm]

/-- Relocating the memory and base relocates a successfully built list of parts. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "parts_to_words_add"
  (words_as_type_indexed_bitvec)]
theorem partsWords_add {width : Nat} [NeZero width] (conf : Config)
    (parts : List ClosLang.ConstPart) (memory : Spt (Build.Value width))
    (index : Nat) (off a : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (memory1 : Spt (Build.Value width))
    (run : Build.partsToWords conf memory index parts off = some (w, ws))
    (offAligned : holByteAligned off = true) (aAligned : holByteAligned a = true)
    (good : goodDimindex width) (shiftBound : wordShiftAmount width ≤ shiftLength conf)
    (memoryRel : ∀ i, (Build.lookupMem memory1 i).2 = wordCondAdd conf a (Build.lookupMem memory i)) :
    ∃ v vs, Build.partsToWords conf memory1 index parts (off + a) = some (v, vs) ∧
      vs.map Prod.snd = ws.map (wordCondAdd conf a) ∧ v.2 = wordCondAdd conf a w := by
  induction parts generalizing memory memory1 index off w ws with
  | nil =>
    simp [Build.partsToWords] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨Build.lookupMem memory1 (index - 1), [], by simp [Build.partsToWords, memoryRel]⟩
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
        obtain ⟨result, restWords⟩ := tail
        simp [ht] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨v1, words1, hp1, wordsRel, valueRel⟩ :=
          partWords_add conf part memory off a v words memory1 offAligned aAligned good shiftBound hp memoryRel
        have lengths : words1.length = words.length := by
          have := congrArg List.length wordsRel
          simpa using this
        have nextAligned : holByteAligned (off + wordSemBytesInWord * BitVec.ofNat width words.length) = true := by
          have stride := (byteAlignMultBytesInWord (BitVec.ofNat width words.length) good).2
          unfold holByteAligned at offAligned stride ⊢
          rw [(alignedAddSub _ _ _ stride).1]
          exact offAligned
        have nextRel : ∀ i, (Build.lookupMem (sptInsert index v1 memory1) i).2 =
            wordCondAdd conf a (Build.lookupMem (sptInsert index v memory) i) := by
          intro i
          by_cases h : i = index
          · subst i; simpa [Build.lookupMem, sptLookup_sptInsert_same] using valueRel
          · simpa [Build.lookupMem, sptLookup_sptInsert_ne, h] using memoryRel i
        obtain ⟨v2, words2, ht1, restRel, resultRel⟩ :=
          ih _ _ _ _ _ _ ht nextAligned nextRel
        refine ⟨v2, words1 ++ words2, ?_, ?_, resultRel⟩
        · simp only [Build.partsToWords, hp1, bind, Option.bind]
          rw [lengths]
          have ht2 : Build.partsToWords conf (sptInsert index v1 memory1) (index + 1) rest
              (off + a + wordSemBytesInWord * BitVec.ofNat width words.length) = some (v2, words2) := by
            simpa [BitVec.add_assoc, BitVec.add_comm, add_left_comm] using ht1
          simp [ht2]
        · simp [wordsRel, restRel]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
