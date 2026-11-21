module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MaxoutBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerBits
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
public import Mathlib.Tactic
@[expose] public section

/-! Exact evaluation of pointer annotation construction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Sequential evaluation after a successful assignment, factored for this proof;
there is no separate HOL declaration. -/
private theorem seqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Sequential evaluation, factored for this proof; there is no separate HOL declaration. -/
private theorem seqEval {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

namespace MakePtrWitnesses
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MakePtrWitnesses

/-- Constructing pointer fields evaluates to the source constructor pointer.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Make_ptr_bits_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)
  (hol_unused_existential_inhabitants := [β._unused])]
theorem makePtrBits_correct {width : Nat} [NeZero width] {C F β : Type} [Nonempty β]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (tagReg lenReg dest tag len : Nat)
    (target : WordSemStateFiniteExact width C F) (f d : BitVec width)
    (differentTag : tagReg ≠ dest) (tagBound : tag < 2 ^ width) (tagBits : conf.tagBits < width)
    (differentLen : lenReg ≠ dest) (lenBound : len < 2 ^ width) (lenBits : conf.lenBits < width)
    (lenShift : conf.lenBits + 1 < width)
    (free : target.store.lookup .nextFree = some (.word f))
    (curr : target.store.lookup .currHeap = some (.word d))
    (tagRead : sptLookup tagReg target.locals = some (.word (BitVec.ofNat width tag)))
    (lenRead : sptLookup lenReg target.locals = some (.word (BitVec.ofNat width len)))
    (shiftBound : shiftLength conf < width + wordShiftAmount width) :
    ∃ (_unused : β), WordSemStateFiniteExact.evaluate (makePtrBitsCode conf tagReg lenReg dest) target =
      (none, target.setVar dest (Build.makeConsPtr conf (f - d) tag len)) := by
  let offset := shiftLength conf - wordShiftAmount width
  have offsetBound : offset < width := by dsimp [offset]; omega
  have offsetPow : offset < 2 ^ width := Nat.lt_trans offsetBound Nat.lt_two_pow_self
  let init : BitVec width := 1 ||| ((f - d) <<< offset)
  have initRead : target.wordExp (.op .or [.const 1,
      shiftN .lsl (.op .sub [.lookup .nextFree, .lookup .currHeap]) offset]) = some (.word init) := by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, free, curr,
      shiftN, wordShiftHOL, Nat.mod_eq_of_lt offsetPow, Nat.not_le_of_gt offsetBound,
      wordOpHOL, wordOp, theWords, init]
    change ((1 : BitVec width) ||| (((f - d) <<< offset) ||| 0)) = _
    simp
  refine ⟨Classical.choice inferInstance, ?_⟩
  simp only [makePtrBitsCode, wordListSeq]
  rw [seqAssign target dest _ (.word init) _ (by simpa [offset] using initRead), seqEval]
  have tagRun := evaluateMaxoutBitsCode conf.tagBits (1 + conf.lenBits) dest tagReg tag target init
    differentTag tagBound tagBits (by omega) tagRead
  rw [tagRun]
  simp only
  have lenRun := evaluateMaxoutBitsCode conf.lenBits 1 dest lenReg len target
    (init ||| maxoutBits tag conf.tagBits (1 + conf.lenBits))
    differentLen lenBound lenBits (by omega) lenRead
  rw [lenRun]
  rw [makeConsPtr_eq]
  simp only [init, offset, ptrBits]
  congr 2
  ac_rfl
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
