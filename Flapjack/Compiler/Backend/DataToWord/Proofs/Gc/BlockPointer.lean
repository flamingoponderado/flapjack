import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Block
import Flapjack.Compiler.Backend.DataToWord.Proofs.Mask
import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers

/-! Pointer annotations of related nonempty constructors. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A related nonempty constructor local has the same encoded pointer
annotation as the corresponding abstract block. This Lean-side helper is
used to reason about the compiler's packed-field tests. -/
theorem stateRel64_getBlockPointer {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values))
    (nonempty : values ≠ []) :
    ∃ (word : BitVec 64) (ptr : Nat),
      WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      word = Memory.getAddr conf ptr (.word (ptrBits conf tag values.length)) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.block stamp tag values) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.block stamp tag values) word sourceRun wordRun
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.block stamp tag values, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, space⟩ := focused
  obtain ⟨addresses, inv, projected⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, valuesRel, _⟩ := stackInv
  cases addresses with
  | nil => cases valuesRel
  | cons root rest =>
    cases valuesRel with
    | cons head tail =>
      cases projected with
      | cons addressHead addressTail =>
        obtain ⟨ptr, children, pair, lookup, rootEq, cell⟩ :=
          (Memory.valueInv_nonemptyBlock conf stamp tag values source.refs root f tf heap nonempty).mp head
        have lengthEq : children.length = values.length := pair.length_eq.symm
        refine ⟨Memory.getAddr conf ptr (.word (ptrBits conf tag values.length)), ptr, ?_, rfl⟩
        have eq : word = .word (Memory.getAddr conf ptr (.word (ptrBits conf tag values.length))) := by
          simpa [rootEq, Memory.wordAddr, lengthEq] using addressHead.symm
        simpa [eq] using wordRun

/-- The fast length mask discards the pointer index and tag field, leaving
the saturated length field and pointer marker. -/
theorem getAddr_lengthField64 (conf : Config) (ptr tag len : Nat) :
    (Memory.getAddr conf ptr (.word (ptrBits conf tag len)) &&&
      BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1)) =
      (pointerBits conf 0 len ||| (1 : BitVec 64)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getAddr, getLowerBits_word_eq_mask, ptrBits_eq_inlined, pointerBits, smallShiftLength,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  have zeroTag : (if 0 < 2 ^ conf.tagBits - 1 then 0 else 2 ^ conf.tagBits - 1) = 0 := by
    split <;> omega
  rw [zeroTag]
  simp only [Nat.zero_testBit, Bool.and_false, Bool.false_or]
  by_cases low : i < conf.lenBits + 1
  · have belowShift : i < shiftLength conf := by simp [shiftLength] at *; omega
    have notTag : ¬ 1 + conf.lenBits ≤ i := by omega
    have within : i < conf.lenBits + conf.tagBits + 1 := by omega
    simp [low, belowShift, notTag, within]
  · have afterTag : 1 + conf.lenBits ≤ i := by omega
    have positive : 1 ≤ i := by omega
    have cappedBound : (if len < 2 ^ conf.lenBits - 1 then len else 2 ^ conf.lenBits - 1) < 2 ^ conf.lenBits := by
      have power := Nat.two_pow_pos conf.lenBits
      split <;> omega
    have highPower : 2 ^ conf.lenBits ≤ 2 ^ (i - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have highBit : (if len < 2 ^ conf.lenBits - 1 then len else 2 ^ conf.lenBits - 1).testBit (i - 1) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le cappedBound highPower)
    have nonzero : i ≠ 0 := by omega
    simp [low, afterTag, positive, highBit, BitVec.getLsbD_one, nonzero]

/-- Under the source pointer-layout bound, equality of fast length fields
with a nonsaturated query is exactly equality of the original lengths. -/
theorem pointerLengthField_eq64 (conf : Config) (actual wanted : Nat)
    (shiftBound : shiftLength conf < 64) (queryBound : wanted < 2 ^ conf.lenBits - 1) :
    (pointerBits conf 0 actual ||| (1 : BitVec 64)) = (pointerBits conf 0 wanted ||| 1) ↔ actual = wanted := by
  have zeroTag : (if 0 < 2 ^ conf.tagBits - 1 then 0 else 2 ^ conf.tagBits - 1) = 0 := by
    split <;> omega
  have field (n : Nat) : (pointerBits conf 0 n ||| (1 : BitVec 64)) =
      BitVec.ofNat 64 (2 * (if n < 2 ^ conf.lenBits - 1 then n else 2 ^ conf.lenBits - 1) + 1) := by
    unfold pointerBits
    dsimp only
    rw [zeroTag]
    simp only [Nat.zero_mul, Nat.reducePow]
    change ((0 : BitVec 64) ||| BitVec.ofNat 64 ((if n < 2 ^ conf.lenBits - 1 then n else 2 ^ conf.lenBits - 1) * 2) ||| 1) = _
    have mulEq : (if n < 2 ^ conf.lenBits - 1 then n else 2 ^ conf.lenBits - 1) * 2 =
        2 * (if n < 2 ^ conf.lenBits - 1 then n else 2 ^ conf.lenBits - 1) := by omega
    rw [mulEq, BitVec.ofNat_add, BitVec.ofNat_mul]
    have identity (x : BitVec 64) : (0 ||| (2 * x) ||| 1) = 2 * x + 1 := by bv_decide
    exact identity _
  rw [field actual, field wanted]
  have lenBitsBound : conf.lenBits ≤ 61 := by simp [shiftLength] at shiftBound; omega
  have powerBound : 2 ^ conf.lenBits ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) lenBitsBound
  have satBound : (if actual < 2 ^ conf.lenBits - 1 then actual else 2 ^ conf.lenBits - 1) < 2 ^ conf.lenBits := by
    have positive := Nat.two_pow_pos conf.lenBits
    split <;> omega
  have querySmall : wanted < 2 ^ conf.lenBits := by have positive := Nat.two_pow_pos conf.lenBits; omega
  have leftBound : 2 * (if actual < 2 ^ conf.lenBits - 1 then actual else 2 ^ conf.lenBits - 1) + 1 < 2 ^ 64 := by
    by_cases h : actual < 2 ^ conf.lenBits - 1 <;>
      simp only [h, ↓reduceIte] at satBound ⊢ <;> norm_num at powerBound ⊢ <;> omega
  have rightBound : 2 * wanted + 1 < 2 ^ 64 := by
    norm_num at powerBound ⊢
    omega
  simp only [queryBound, ↓reduceIte]
  constructor
  · intro eq
    have numeric := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at numeric
    split at numeric <;> omega
  · rintro rfl
    simp [queryBound]

/-- The compiler's packed-pointer length test agrees with a source block's
field count whenever the query is positive and does not saturate. -/
theorem stateRel64_getBlockFastLength {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values))
    (positive : 0 < wanted) (queryBound : wanted < 2 ^ conf.lenBits - 1) :
    ∃ word : BitVec 64, WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      ((word &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1)) = (pointerBits conf 0 wanted ||| 1) ↔
        values.length = wanted) := by
  by_cases empty : values = []
  · subst values
    obtain ⟨word, run, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related name stamp tag [] sourceRun
    have low : word.getLsbD 0 = false := by
      simp only [List.length_nil, decide_true] at test
      change (word &&& (1 : BitVec 64) == 0) = true at test
      bv_decide
    refine ⟨word, run, ?_⟩
    have notZero : 0 ≠ wanted := by omega
    simp only [List.length_nil, notZero, iff_false]
    intro eq
    have bit := congrArg (fun x : BitVec 64 => x.getLsbD 0) eq
    have low' : word[0] = false := by simpa using low
    simp [low'] at bit
  · obtain ⟨word, ptr, run, encoding⟩ := stateRel64_getBlockPointer conf l1 l2 source target locs related
      name stamp tag values sourceRun empty
    refine ⟨word, run, ?_⟩
    rw [encoding, getAddr_lengthField64]
    exact pointerLengthField_eq64 conf values.length wanted related.2.2.2.2.2.2.2.1 queryBound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
