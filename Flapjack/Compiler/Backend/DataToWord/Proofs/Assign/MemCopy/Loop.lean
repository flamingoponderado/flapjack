module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemCopy.Element
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemCopy
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.UnusedWrite
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Separation
@[expose] public section

/-! The complete data-to-word block-copy loop invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

open Classical in
/-- Extend a separated destination word list by one in-domain update. This
private helper factors the separation step of the HOL loop proof. -/
private theorem extendListWrite {width : Nat} [NeZero width]
    (base : BitVec width) (xs : List (WordLocW width)) (remaining : Nat)
    (value : WordLocW width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (other : ((BitVec width × WordLocW width) → Prop) → Prop)
    (sep : SetSep.star (SetSep.star (Misc.wordList base xs)
      (Misc.wordListExists (base + StackRemove.bytesInWord width * BitVec.ofNat width xs.length) (remaining + 1))) other
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    let dest := base + StackRemove.bytesInWord width * BitVec.ofNat width xs.length
    domain dest = true ∧
    SetSep.star (SetSep.star (Misc.wordList base (xs ++ [value]))
      (Misc.wordListExists (base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1)) remaining)) other
      (SetSep.fun2Set ((fun key => if key = dest then value else memory key), fun a => domain a = true)) := by
  dsimp only
  let dest := base + StackRemove.bytesInWord width * BitVec.ofNat width xs.length
  have old := sep
  change SetSep.star (SetSep.star (Misc.wordList base xs) (Misc.wordListExists dest (remaining + 1))) other _ at old
  rw [(StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) dest remaining).2] at old
  simp only [SetSep.star, SetSep.sepExists] at old
  obtain ⟨left, right, part, ⟨prefixHeap, tail, part2, prefixH, ⟨oldValue, head, rest, part3, headH, restH⟩⟩, otherH⟩ := old
  have grouped : SetSep.star (SetSep.one (dest, oldValue))
      (SetSep.star (Misc.wordList base xs) (SetSep.star (Misc.wordListExists (dest + StackRemove.bytesInWord width) remaining) other))
      (SetSep.fun2Set (memory, fun a => domain a = true)) := by
    have initial : SetSep.star (SetSep.star (Misc.wordList base xs)
        (SetSep.star (SetSep.one (dest, oldValue)) (Misc.wordListExists (dest + StackRemove.bytesInWord width) remaining))) other
        (SetSep.fun2Set (memory, fun a => domain a = true)) :=
      ⟨left, right, part, ⟨prefixHeap, tail, part2, prefixH, ⟨head, rest, part3, headH, restH⟩⟩, otherH⟩
    repeat rw [← SetSep.starAssoc] at initial
    rw [star_swap_first] at initial
    exact initial
  have inside : domain dest = true := by
    obtain ⟨head, rest, partition, single, _⟩ := grouped
    have h : head (dest, oldValue) := by rw [single]
    have graph : SetSep.fun2Set (memory, fun a => domain a = true) (dest, oldValue) := by
      rw [← partition.1]; exact Or.inl h
    exact ((SetSep.fun2SetThm memory (fun a => domain a = true) dest oldValue).mp graph).2
  have updated := SetSep.writeFun2Set value dest oldValue _ memory (fun a => domain a = true) grouped
  refine ⟨inside, ?_⟩
  rw [SetSep.starComm, star_swap_first] at updated
  repeat rw [SetSep.starAssoc] at updated
  rw [wordListAppend]
  simp only [Misc.wordList]
  rw [SetSep.starComm (SetSep.one _) SetSep.emp, StackRemove.StackHeap.starEmptyLeft]
  have destEq : base + BitVec.ofNat width xs.length * StackRemove.bytesInWord width = dest := by
    dsimp [dest]; rw [BitVec.mul_comm]
  have nextEq : base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1) =
      dest + StackRemove.bytesInWord width := by
    dsimp [dest]; simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one, BitVec.add_assoc]
  rw [destEq, nextEq]
  convert updated using 2
  congr 1
  funext key
  by_cases h : key = dest <;> simp [dest] at h ⊢


namespace MemCopyLoopWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MemCopyLoopWitness

/-- The generated copy loop preserves the full paired-root memory invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_memcopy"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem impMemcopy {width : Nat} [NeZero width] {C F C2 F2 : Type}
    (c : Config) (s1 : WordSemStateFiniteExact width C F) (x : DataSem.State C2 F2)
    (ts sp a1 stamp tag : Nat) (values : List DataSem.Value)
    (wptr wx nfree header : BitVec width) (vars : List (DataSem.Value × WordLocW width))
    (other : ((BitVec width × WordLocW width) → Prop) → Prop)
    (len start k : Nat) (ys : List DataSem.Value) (ws : List (WordLocW width))
    (memory : BitVec width → WordLocW width)
    (rel : memoryRel c s1.be ts x.refs sp s1.store memory s1.mdomain
      ((.block stamp tag values, .word wptr) :: (ys.zip ws ++ vars)))
    (sep : SetSep.star (SetSep.star (Misc.wordList nfree (.word header :: ws))
      (Misc.wordListExists (nfree + StackRemove.bytesInWord width * BitVec.ofNat width (ws.length + 1)) k)) other
      (SetSep.fun2Set (memory, fun a => s1.mdomain a = true)))
    (lenBound : len ≤ k) (good : goodDimindex width)
    (read : sptLookup (adjustVar a1) s1.locals = some (.word wptr))
    (eval : s1.wordExp (realAddr c (adjustVar a1)) = some (.word wx))
    (free : s1.store.lookup .nextFree = some (.word nfree))
    (sourceBound : start + len ≤ values.length) (spaceBound : ws.length + len < sp)
    (sameLength : ys.length = ws.length) :
    ∃ m2 ws2, memcopy len (wx + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width start)
        (nfree + StackRemove.bytesInWord width * BitVec.ofNat width (ws.length + 1)) memory s1.mdomain = some m2 ∧
      SetSep.star (Misc.wordList nfree (.word header :: (ws ++ ws2))) SetSep.sepT
        (SetSep.fun2Set (m2, fun a => s1.mdomain a = true)) ∧ ws2.length = len ∧
      memoryRel c s1.be ts x.refs sp s1.store m2 s1.mdomain
        ((ys ++ (values.drop start).take len).zip (ws ++ ws2) ++ vars) := by
  induction len generalizing start k ys ws memory with
  | zero =>
    refine ⟨memory, [], ?_, ?_, rfl, ?_⟩
    · rfl
    · rw [← SetSep.starAssoc] at sep
      simpa using starFun2SetImpSepT _ _ memory (fun a => s1.mdomain a = true) sep
    · simp only [List.take_zero, List.append_nil]
      exact memoryRel_tl c s1.be ts x.refs sp s1.store memory s1.mdomain _ _ rel
  | succ len ih =>
    cases k with
    | zero => omega
    | succ k =>
      have indexBound : start < values.length := by omega
      let src := wx + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width start
      let dst := nfree + StackRemove.bytesInWord width * BitVec.ofNat width (ws.length + 1)
      let value := memory src
      let nextMemory := fun key => if key = dst then value else memory key
      obtain ⟨extended, srcDomain⟩ := impMemcopyLemma c s1 x ts sp a1 stamp tag start values ys ws vars wptr wx memory
        rel indexBound sameLength good read eval
      change s1.mdomain src = true at srcDomain
      have writeResult := memoryRel_write c s1.be ts x.refs sp s1.store memory s1.mdomain
        ((.block stamp tag values, .word wptr) :: ((ys ++ [values[start]]).zip (ws ++ [value]) ++ vars)) value extended
      obtain ⟨free2, free2Eq, canWrite⟩ := writeResult
      have freeSame : free2 = nfree := by rw [free] at free2Eq; exact (WordLocW.word.inj (Option.some.inj free2Eq)).symm
      subst free2
      have writeAt := canWrite (ws.length + 1) (by omega)
      change s1.mdomain dst = true ∧ memoryRel c s1.be ts x.refs sp s1.store nextMemory s1.mdomain _ at writeAt
      have sepNext := extendListWrite nfree (.word header :: ws) k value memory s1.mdomain other (by simpa using sep)
      have nextSep : SetSep.star (SetSep.star (Misc.wordList nfree (.word header :: (ws ++ [value])))
          (Misc.wordListExists (nfree + StackRemove.bytesInWord width * BitVec.ofNat width ((ws ++ [value]).length + 1)) k)) other
          (SetSep.fun2Set (nextMemory, fun a => s1.mdomain a = true)) := by
        simpa [dst, nextMemory, List.length_append, Nat.add_assoc] using sepNext.2
      obtain ⟨m2, ws2, run2, sep2, length2, rel2⟩ :=
        ih (start + 1) k (ys ++ [values[start]]) (ws ++ [value]) nextMemory writeAt.2 nextSep
          (by omega) (by omega) (by simp; omega) (by simp [sameLength])
      refine ⟨m2, value :: ws2, ?_, ?_, ?_, ?_⟩
      · change memcopy (len + 1) src dst memory s1.mdomain = some m2
        simp only [memcopy, srcDomain, writeAt.1, Bool.and_self, ↓reduceIte]
        have srcNext : src + wordSemBytesInWord = wx + StackRemove.bytesInWord width +
            StackRemove.bytesInWord width * BitVec.ofNat width (start + 1) := by
          simp only [src, wordSemBytesInWord, BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one, BitVec.add_assoc, StackRemove.bytesInWord]
        have dstNext : dst + wordSemBytesInWord = nfree + StackRemove.bytesInWord width *
            BitVec.ofNat width ((ws ++ [value]).length + 1) := by
          simp only [dst, wordSemBytesInWord, List.length_append, List.length_singleton,
            BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one, BitVec.add_assoc, StackRemove.bytesInWord]
        simpa only [src, dst, nextMemory, srcNext, dstNext] using run2
      · simpa [List.append_assoc] using sep2
      · simp [length2]
      · have selected : (values.drop start).take (len + 1) =
            values[start] :: (values.drop (start + 1)).take len := by
          rw [List.drop_eq_getElem_cons indexBound]
          rfl
        rw [selected]
        simpa [List.append_assoc] using rel2

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
