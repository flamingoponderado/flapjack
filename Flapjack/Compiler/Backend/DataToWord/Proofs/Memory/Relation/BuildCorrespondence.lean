module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.BuildWords
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerAdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerBits
@[expose] public section

/-! Correspondence of executable and proof-side constant builders. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A successfully lowered part agrees with the proof-side builder. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "part_to_words_IMP_build_words"
  (words_as_type_indexed_bitvec)]
theorem partWords_imp_build {width : Nat} [NeZero width] (conf : Config)
    (memory : Spt (Build.Value width)) (part : ClosLang.ConstPart) (off : BitVec width)
    (w : Build.Value width) (ws : List (Build.Value width))
    (run : Build.partWords conf memory part off = some (w,ws))
    (good : goodDimindex width) (aligned : holByteAligned off = true)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    buildPartWords conf (fun i => (Build.lookupMem memory i).2) part off = some (w.2, ws.map Prod.snd) := by
  classical
  cases part with
  | con tag refs =>
    cases refs with
    | nil =>
      simp [Build.partWords] at run
      obtain ⟨bound, rfl, rfl⟩ := run
      simp [buildPartWords, bound]
    | cons x xs =>
      simp only [Build.partWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases h : encodeHeader (width := width) conf (4 * tag) (xs.length + 1) with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [buildPartWords, h, makeConsPtr_add conf off tag (xs.length + 1) aligned good shiftBound,
          getLowerBits_ptrBits, List.map_map]
  | int i =>
    by_cases small : smallInt width i
    · simp [Build.partWords, small] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [buildPartWords, small]
    · have tagEq : (((if decide (i < 0) then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat =
          (if decide (i < 0) then 7 else 3) := by
        rcases good with hw | hw <;> subst width <;> by_cases sign : i < 0 <;> simp [sign]
      simp only [Build.partWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run
      cases h : encodeHeader (width := width) conf (if decide (i < 0) then 7 else 3)
          (Misc.Multiword.n2mw (width := width) i.natAbs).length <;> simp_all
      obtain ⟨rfl, rfl⟩ := run
      simp [buildPartWords, small, Misc.Multiword.i2mw, tagEq, h, List.map_map]
  | w64 word =>
    by_cases narrow : width < 64
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 2 <;> simp_all
      obtain ⟨rfl, rfl⟩ := run
      simp [buildPartWords, narrow, h]
    · simp only [Build.partWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 1 <;> simp_all
      obtain ⟨rfl, rfl⟩ := run
      simp [buildPartWords, Nat.not_lt.mpr narrow, h]
  | str text =>
    simp only [Build.partWords] at run
    split at run
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp_all [buildPartWords, List.map_map]

/-- Successfully lowered parts agree with the complete proof-side builder. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "parts_to_words_IMP_build_words"
  (words_as_type_indexed_bitvec)]
theorem partsWords_imp_build {width : Nat} [NeZero width] (conf : Config)
    (memory : Spt (Build.Value width)) (index : Nat) (parts : List ClosLang.ConstPart)
    (off : BitVec width) (w : Build.Value width) (ws : List (Build.Value width))
    (run : Build.partsToWords conf memory index parts off = some (w,ws))
    (good : goodDimindex width) (aligned : holByteAligned off = true)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    buildWords conf (fun i => (Build.lookupMem memory i).2) index parts off = some (w.2, ws.map Prod.snd) := by
  induction parts generalizing memory index off w ws with
  | nil =>
    simp [Build.partsToWords] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [buildWords]
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
        have pbuild := partWords_imp_build conf memory part off v words hp good aligned shiftBound
        have strideAligned : holByteAligned (wordSemBytesInWord * BitVec.ofNat width words.length) = true :=
          (byteAlignMultBytesInWord (BitVec.ofNat width words.length) good).2
        have nextAligned : holByteAligned (off + wordSemBytesInWord * BitVec.ofNat width words.length) = true := by
          unfold holByteAligned at aligned strideAligned ⊢
          rw [(alignedAddSub _ _ _ strideAligned).1]
          exact aligned
        have memEq : (fun i => (Build.lookupMem (sptInsert index v memory) i).2) =
            (fun i => if i = index then v.2 else (Build.lookupMem memory i).2) := by
          funext i
          by_cases h : i = index
          · subst i; simp [Build.lookupMem, sptLookup_sptInsert_same]
          · simp [Build.lookupMem, sptLookup_sptInsert_ne, h]
        have tailBuild := ih _ _ _ _ _ ht nextAligned
        simp [buildWords, pbuild]
        rw [← memEq, tailBuild]
        simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
