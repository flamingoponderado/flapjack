import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreListCodeThm
import Flapjack.Compiler.Backend.StackRemove.InitCode
import Flapjack.Misc.GoodDimindex
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory

/-! Native execution of the StackRemove initializer, towards
`init_code_thm` (`stack_removeProofScript.sml` 3225-3837). The lemmas here
are Flapjack proof factoring of the original symbolic execution (`tac1`);
none is a separately named HOL declaration.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
open Flapjack Flapjack.Compiler.Backend.StackLang

variable {width : Nat} [NeZero width] {C F : Type}

/-- A register move copies an arbitrary present value. -/
theorem stepMove (dest src : Nat) (value : WordLocW width)
    (s : StackSemStateFiniteExact width C F) (read : s.regs.lookup src = some value) :
    StackSemEvaluate.evaluate (moveHOL dest src, s) =
      (none, {s with regs := s.regs.updateEq (dest, value)}) := by
  simp [moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, read, StackSemStateOps.setVar]

/-- Register addition. -/
theorem stepAdd (r1 r2 : Nat) (x y : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read1 : s.regs.lookup r1 = some (.word x)) (read2 : s.regs.lookup r2 = some (.word y)) :
    StackSemEvaluate.evaluate (addInst r1 r2, s) =
      (none, {s with regs := s.regs.updateEq (r1, .word (x + y))}) := by
  simp [addInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, read1, read2, StackSemStateOps.setVar, wordOpHOL, wordOp]

/-- Register subtraction. -/
theorem stepSub (r1 r2 : Nat) (x y : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read1 : s.regs.lookup r1 = some (.word x)) (read2 : s.regs.lookup r2 = some (.word y)) :
    StackSemEvaluate.evaluate (subInst r1 r2, s) =
      (none, {s with regs := s.regs.updateEq (r1, .word (x - y))}) := by
  simp [subInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, read1, read2, StackSemStateOps.setVar, wordOpHOL, wordOp]

/-- Constant load. -/
theorem stepConst (r : Nat) (value : BitVec width) (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (constInst r value, s) =
      (none, {s with regs := s.regs.updateEq (r, .word value)}) := by
  simp [constInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, StackSemStateOps.setVar]

/-- Logical right shift by an in-range literal amount. -/
theorem stepLsr (r n : Nat) (x : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read : s.regs.lookup r = some (.word x)) (small : n < width) :
    StackSemEvaluate.evaluate (rightShiftInst r n, s) =
      (none, {s with regs := s.regs.updateEq (r, .word (x >>> n))}) := by
  have mod : n % 2 ^ width = n := Nat.mod_eq_of_lt (Nat.lt_trans small Nat.lt_two_pow_self)
  simp [rightShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, read, StackSemStateOps.setVar, wordShiftHOL, mod,
    Nat.not_le.mpr small]

/-- Left shift by an in-range literal amount. -/
theorem stepLsl (r n : Nat) (x : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read : s.regs.lookup r = some (.word x)) (small : n < width) :
    StackSemEvaluate.evaluate (leftShiftInst r n, s) =
      (none, {s with regs := s.regs.updateEq (r, .word (x <<< n))}) := by
  have mod : n % 2 ^ width = n := Nat.mod_eq_of_lt (Nat.lt_trans small Nat.lt_two_pow_self)
  simp [leftShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, read, StackSemStateOps.setVar, wordShiftHOL, mod,
    Nat.not_le.mpr small]

/-- Adding the byte width. -/
theorem stepAddBytes (r : Nat) (x : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read : s.regs.lookup r = some (.word x)) :
    StackSemEvaluate.evaluate (addBytesInWordInst r, s) =
      (none, {s with regs := s.regs.updateEq (r, .word (x + bytesInWord width))}) := by
  simp [addBytesInWordInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, read, StackSemStateOps.setVar, wordOpHOL, wordOp,
    wordSemBytesInWord, bytesInWord]

/-- Memory load through an address register. -/
theorem stepLoad (r a : Nat) (address : BitVec width) (value : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (read : s.regs.lookup a = some (.word address))
    (load : StackSemStateOps.memLoad address s = some value) :
    StackSemEvaluate.evaluate (loadInst r a, s) =
      (none, {s with regs := s.regs.updateEq (r, value)}) := by
  simp [loadInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp, read,
    StackSemStateOps.setVar, wordOpHOL, wordOp, load]

/-- Unsigned-lower conditional on two word registers. -/
theorem stepIteLower (r1 r2 : Nat) (x y : BitVec width) (c1 c2 : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (read1 : s.regs.lookup r1 = some (.word x)) (read2 : s.regs.lookup r2 = some (.word y)) :
    StackSemEvaluate.evaluate (.ite .lower r1 (.reg r2) c1 c2, s) =
      if x < y then StackSemEvaluate.evaluate (c1, s) else StackSemEvaluate.evaluate (c2, s) := by
  rw [StackSemEvaluate.evaluate_ite]
  by_cases lt : x < y <;>
    simp [StackSemStateOps.getVar, read1, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
      StackSemStateOps.getVarImm, read2, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, lt]

/-- Peeling one normal clock-preserving instruction off a literal list. -/
theorem stepList (x y : HolProg width) (rest : List (HolProg width))
    (s post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (x, s) = (none, post)) (clock : post.clock = s.clock) :
    StackSemEvaluate.evaluate (listSeqHOL (x :: y :: rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL (y :: rest), post) :=
  StoreListCodeThm.evaluateSeqNormal _ _ s post run clock

/-- Peeling one normal clock-preserving instruction off any nonempty
continuation list. -/
theorem stepCons (x : HolProg width) (rest : List (HolProg width))
    (s post : StackSemStateFiniteExact width C F) (nonempty : rest ≠ [])
    (run : StackSemEvaluate.evaluate (x, s) = (none, post)) (clock : post.clock = s.clock) :
    StackSemEvaluate.evaluate (listSeqHOL (x :: rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL rest, post) := by
  cases rest with
  | nil => exact absurd rfl nonempty
  | cons y rest => exact stepList x y rest s post run clock

/-- The constant stack-allocation margin word of the initializer. -/
def marginWord (width : Nat) [NeZero width] : BitVec width :=
  BitVec.ofNat width maxStackAlloc * bytesInWord width

/-- Original first initializer segment: the middle address in register 0 and
the margin-adjusted bounds in registers 2 and 4. -/
def segmentMiddle (width : Nat) [NeZero width] : List (HolProg width) :=
  [moveHOL 0 4, subInst 0 2,
    rightShiftInst 0 (1 + wordShiftAmount width),
    leftShiftInst 0 (wordShiftAmount width), addInst 0 2,
    constInst 5 (marginWord width),
    addInst 2 5, subInst 4 5]

/-- The rounded middle address computed by `segmentMiddle`. -/
def middleWord (p2 p4 : BitVec width) : BitVec width :=
  ((p4 - p2) >>> (1 + wordShiftAmount width)) <<< wordShiftAmount width + p2

theorem shiftSmall (good : goodDimindex width) : wordShiftAmount width + 1 < width := by
  unfold wordShiftAmount
  rcases good with h | h <;> simp [h]

theorem runSegmentMiddle (rest : List (HolProg width)) (nonempty : rest ≠ [])
    (s : StackSemStateFiniteExact width C F) (p2 p4 : BitVec width)
    (good : goodDimindex width)
    (read2 : s.regs.lookup 2 = some (.word p2)) (read4 : s.regs.lookup 4 = some (.word p4)) :
    StackSemEvaluate.evaluate (listSeqHOL (segmentMiddle width ++ rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL rest,
        {s with regs := ((((s.regs.updateEq (0, .word (middleWord p2 p4))).updateEq
          (5, .word (marginWord width))).updateEq (2, .word (p2 + marginWord width))).updateEq
          (4, .word (p4 - marginWord width)))}) := by
  have small := shiftSmall good
  simp only [segmentMiddle, List.cons_append, List.nil_append]
  rw [stepCons _ _ _ _ (by simp) (stepMove 0 4 _ s read4) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub 0 2 p4 p2 _ (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, read2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsr 0 (1 + wordShiftAmount width) (p4 - p2) _ (by simp [FUPDATE_HOL]) (by omega)) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsl 0 (wordShiftAmount width) ((p4 - p2) >>> (1 + wordShiftAmount width)) _
      (by simp [FUPDATE_HOL]) (by omega)) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAdd 0 2 (((p4 - p2) >>> (1 + wordShiftAmount width)) <<< wordShiftAmount width) p2 _
      (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, read2])) rfl]
  rw [stepCons _ _ _ _ (by simp) (stepConst 5 (marginWord width) _) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAdd 2 5 p2 (marginWord width) _ (by simp [FUPDATE_HOL, read2]) (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ nonempty
    (stepSub 4 5 p4 (marginWord width) _ (by simp [FUPDATE_HOL, read4]) (by simp [FUPDATE_HOL])) rfl]
  congr 3
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, middleWord]
  by_cases k0 : key = 0 <;> by_cases k2 : key = 2 <;> by_cases k4 : key = 4 <;>
    by_cases k5 : key = 5 <;> simp_all

/-- Updating a register with its present value leaves the map unchanged. -/
theorem updateEq_self (regs : HolFiniteMapExact Nat (WordLocW width)) (r : Nat)
    (value : WordLocW width) (read : regs.lookup r = some value) :
    regs.updateEq (r, value) = regs := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  by_cases same : key = r
  · subst same; simp [FUPDATE_HOL, read]
  · simp [FUPDATE_HOL, same]

/-- A second update of the same register overwrites the first. -/
theorem updateEq_updateEq_same {β : Type} (regs : HolFiniteMapExact Nat β) (r : Nat)
    (a b : β) : (regs.updateEq (r, a)).updateEq (r, b) = regs.updateEq (r, b) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  by_cases same : key = r <;> simp [FUPDATE_HOL, same]

/-- The third pointer chosen by the first conditional: the given pointer when
it lies inside the margins, the middle address otherwise. -/
def adjustedThird (p3 middle low high : BitVec width) : BitVec width :=
  if p3 < low then middle else if high < p3 then middle else p3

theorem runAdjust (s : StackSemStateFiniteExact width C F) (p3 middle low high : BitVec width)
    (read0 : s.regs.lookup 0 = some (.word middle)) (read2 : s.regs.lookup 2 = some (.word low))
    (read3 : s.regs.lookup 3 = some (.word p3)) (read4 : s.regs.lookup 4 = some (.word high)) :
    StackSemEvaluate.evaluate
      (.ite .lower 3 (.reg 2) (moveHOL 3 0) (.ite .lower 4 (.reg 3) (moveHOL 3 0) .skip), s) =
      (none, {s with regs := s.regs.updateEq (3, .word (adjustedThird p3 middle low high))}) := by
  rw [stepIteLower 3 2 p3 low _ _ s read3 read2]
  by_cases lowCase : p3 < low
  · simp only [lowCase, if_true, adjustedThird]
    exact stepMove 3 0 _ s read0
  · rw [if_neg lowCase, stepIteLower 4 3 high p3 _ _ s read4 read3]
    by_cases highCase : high < p3
    · simp only [highCase, if_true, adjustedThird, lowCase, if_false]
      exact stepMove 3 0 _ s read0
    · simp only [highCase, if_false, adjustedThird, lowCase, StackSemEvaluate.evaluate_skip,
        updateEq_self s.regs 3 _ read3]

/-- The heap-limited third pointer chosen by the second conditional. -/
def shrunkThird (p2 adjusted maxHeapWord : BitVec width) : BitVec width :=
  if maxHeapWord < adjusted - p2 then p2 + maxHeapWord else adjusted

theorem runShrink (s : StackSemStateFiniteExact width C F) (p2 adjusted maxHeapWord : BitVec width)
    (read0 : s.regs.lookup 0 = some (.word (adjusted - p2)))
    (read2 : s.regs.lookup 2 = some (.word p2))
    (read3 : s.regs.lookup 3 = some (.word adjusted))
    (read5 : s.regs.lookup 5 = some (.word maxHeapWord)) :
    StackSemEvaluate.evaluate
      (.ite .lower 5 (.reg 0) (.seq (moveHOL 3 2) (addInst 3 5)) .skip, s) =
      (none, {s with regs := s.regs.updateEq (3, .word (shrunkThird p2 adjusted maxHeapWord))}) := by
  rw [stepIteLower 5 0 maxHeapWord (adjusted - p2) _ _ s read5 read0]
  by_cases shrink : maxHeapWord < adjusted - p2
  · simp only [shrink, if_true, shrunkThird]
    rw [StoreListCodeThm.evaluateSeqNormal _ _ s _ (stepMove 3 2 _ s read2) rfl,
      stepAdd 3 5 p2 maxHeapWord _ (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, read5]),
      updateEq_updateEq_same]
  · simp only [shrink, if_false, shrunkThird, StackSemEvaluate.evaluate_skip,
      updateEq_self s.regs 3 _ read3]

/-- The initializer's guarded maximum-heap word. -/
def maxHeapWord (width : Nat) [NeZero width] (maxHeap : Nat) : BitVec width :=
  if maxHeap * (bytesInWord width).toNat < 2 ^ width then
    BitVec.ofNat width maxHeap * bytesInWord width
  else (0 : BitVec width) - 1

/-- Original segment restoring the bounds and computing the heap size. -/
def segmentLimits (width : Nat) [NeZero width] (maxHeap : Nat) : List (HolProg width) :=
  [constInst 0 (marginWord width), subInst 2 0, addInst 4 0, moveHOL 0 3, subInst 0 2,
    constInst 5 (maxHeapWord width maxHeap)]

theorem runSegmentLimits (maxHeap : Nat) (rest : List (HolProg width)) (nonempty : rest ≠ [])
    (s : StackSemStateFiniteExact width C F) (p2 p4 adjusted : BitVec width)
    (read2 : s.regs.lookup 2 = some (.word (p2 + marginWord width)))
    (read3 : s.regs.lookup 3 = some (.word adjusted))
    (read4 : s.regs.lookup 4 = some (.word (p4 - marginWord width))) :
    StackSemEvaluate.evaluate (listSeqHOL (segmentLimits width maxHeap ++ rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL rest,
        {s with regs := ((((s.regs.updateEq (0, .word (adjusted - p2))).updateEq
          (2, .word p2)).updateEq (4, .word p4)).updateEq
          (5, .word (maxHeapWord width maxHeap)))}) := by
  simp only [segmentLimits, List.cons_append, List.nil_append]
  rw [stepCons _ _ _ _ (by simp) (stepConst 0 (marginWord width) _) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub 2 0 (p2 + marginWord width) (marginWord width) _
      (by simp [FUPDATE_HOL, read2]) (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAdd 4 0 (p4 - marginWord width) (marginWord width) _
      (by simp [FUPDATE_HOL, read4]) (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp) (stepMove 0 3 (.word adjusted) _ (by simp [FUPDATE_HOL, read3])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub 0 2 adjusted p2 _ (by simp [FUPDATE_HOL])
      (by simp [FUPDATE_HOL, BitVec.add_sub_cancel])) rfl]
  rw [stepCons _ _ _ _ nonempty (stepConst 5 (maxHeapWord width maxHeap) _) rfl]
  congr 3
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, BitVec.add_sub_cancel,
    BitVec.sub_add_cancel]
  split_ifs <;> simp_all

/-- Original segment rounding the heap to an even number of words and
setting up the store, stack and heap registers. -/
def segmentRound (width : Nat) [NeZero width] (k : Nat) : List (HolProg width) :=
  [subInst 3 2, rightShiftInst 3 (wordShiftAmount width + 1),
    leftShiftInst 3 (wordShiftAmount width + 1), addInst 3 2,
    moveHOL 5 3, subInst 5 2, rightShiftInst 5 1,
    moveHOL (k + 2) 2, addInst 2 5,
    moveHOL k 4, moveHOL (k + 1) 3]

/-- The final heap end (third pointer) after rounding. -/
def roundedThird (p2 shrunk : BitVec width) : BitVec width :=
  ((shrunk - p2) >>> (wordShiftAmount width + 1)) <<< (wordShiftAmount width + 1) + p2

theorem runSegmentRound (k : Nat) (rest : List (HolProg width)) (nonempty : rest ≠ [])
    (s : StackSemStateFiniteExact width C F) (p2 p4 shrunk : BitVec width)
    (good : goodDimindex width) (k8 : 8 ≤ k)
    (read2 : s.regs.lookup 2 = some (.word p2))
    (read3 : s.regs.lookup 3 = some (.word shrunk))
    (read4 : s.regs.lookup 4 = some (.word p4)) :
    StackSemEvaluate.evaluate (listSeqHOL (segmentRound width k ++ rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL rest,
        {s with regs := ((((((s.regs.updateEq (3, .word (roundedThird p2 shrunk))).updateEq
          (5, .word ((roundedThird p2 shrunk - p2) >>> (1 : Nat)))).updateEq
          (k + 2, .word p2)).updateEq
          (2, .word (p2 + (roundedThird p2 shrunk - p2) >>> (1 : Nat)))).updateEq
          (k, .word p4)).updateEq (k + 1, .word (roundedThird p2 shrunk)))}) := by
  have small := shiftSmall good
  have one : 1 < width := by omega
  simp only [segmentRound, List.cons_append, List.nil_append]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub 3 2 shrunk p2 _ (by simp [read3]) (by simp [read2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsr 3 (wordShiftAmount width + 1) (shrunk - p2) _ (by simp [FUPDATE_HOL]) small) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsl 3 (wordShiftAmount width + 1) ((shrunk - p2) >>> (wordShiftAmount width + 1)) _
      (by simp [FUPDATE_HOL]) small) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAdd 3 2 (((shrunk - p2) >>> (wordShiftAmount width + 1)) <<< (wordShiftAmount width + 1))
      p2 _ (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, read2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepMove 5 3 (.word (roundedThird p2 shrunk)) _ (by simp [FUPDATE_HOL, roundedThird])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub 5 2 (roundedThird p2 shrunk) p2 _ (by simp [FUPDATE_HOL])
      (by simp [FUPDATE_HOL, read2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsr 5 1 (roundedThird p2 shrunk - p2) _ (by simp [FUPDATE_HOL]) one) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepMove (k + 2) 2 (.word p2) _ (by simp [FUPDATE_HOL, read2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAdd 2 5 p2 ((roundedThird p2 shrunk - p2) >>> (1 : Nat)) _
      (by simp [FUPDATE_HOL, read2])
      (by simp [FUPDATE_HOL, show (5 : Nat) ≠ k + 2 by omega])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepMove k 4 (.word p4) _
      (by simp [FUPDATE_HOL, read4, show (4 : Nat) ≠ k + 2 by omega])) rfl]
  rw [stepCons _ _ _ _ nonempty
    (stepMove (k + 1) 3 (.word (roundedThird p2 shrunk)) _
      (by simp [FUPDATE_HOL, roundedThird, show (3 : Nat) ≠ k + 2 by omega,
        show (3 : Nat) ≠ k by omega])) rfl]
  congr 3
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, roundedThird]
  split_ifs <;> simp_all

/-- Original segment loading the five header words. -/
def segmentLoads (width : Nat) [NeZero width] (k : Nat) : List (HolProg width) :=
  [loadInst 3 (k + 2), rightShiftInst 3 (wordShiftAmount width),
    moveHOL 0 (k + 2), addBytesInWordInst 0,
    loadInst 4 0, addBytesInWordInst 0, loadInst 6 0,
    addBytesInWordInst 0, loadInst 7 0, addBytesInWordInst 0,
    loadInst 1 0]

theorem memLoad_of {s : StackSemStateFiniteExact width C F} {address : BitVec width}
    {value : WordLocW width} (domain : s.mdomain address = true)
    (memory : s.memory address = value) : StackSemStateOps.memLoad address s = some value := by
  simp [StackSemStateOps.memLoad, domain, memory]

theorem runSegmentLoads (k : Nat) (rest : List (HolProg width)) (nonempty : rest ≠ [])
    (s : StackSemStateFiniteExact width C F) (p2 bitmapPointer : BitVec width)
    (v1 v2 v3 v4 : WordLocW width) (good : goodDimindex width) (k8 : 8 ≤ k)
    (readBase : s.regs.lookup (k + 2) = some (.word p2))
    (domain : ∀ i, i < 5 → s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true)
    (load0 : s.memory p2 = .word bitmapPointer)
    (load1 : s.memory (p2 + bytesInWord width) = v1)
    (load2 : s.memory (p2 + bytesInWord width + bytesInWord width) = v2)
    (load3 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width) = v3)
    (load4 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
      bytesInWord width) = v4) :
    StackSemEvaluate.evaluate (listSeqHOL (segmentLoads width k ++ rest), s) =
      StackSemEvaluate.evaluate (listSeqHOL rest,
        {s with regs := ((((((s.regs.updateEq
          (3, .word (bitmapPointer >>> wordShiftAmount width))).updateEq
          (0, .word (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
            bytesInWord width))).updateEq (4, v1)).updateEq (6, v2)).updateEq (7, v3)).updateEq
          (1, v4))}) := by
  have small := shiftSmall good
  have b := bytesInWord width
  have dom : ∀ i, i < 5 → ∀ address, address = p2 + BitVec.ofNat width i * bytesInWord width →
      s.mdomain address = true := fun i hi address eq => eq ▸ domain i hi
  have d0 := dom 0 (by omega) p2 (by simp)
  have d1 := dom 1 (by omega) (p2 + bytesInWord width) (by simp)
  have succ : ∀ i : Nat, p2 + BitVec.ofNat width (i + 1) * bytesInWord width =
      p2 + BitVec.ofNat width i * bytesInWord width + bytesInWord width := by
    intro i
    rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.add_assoc]
    simp
  have d2 := dom 2 (by omega) (p2 + bytesInWord width + bytesInWord width) (by
    rw [succ 1]; simp)
  have d3 := dom 3 (by omega) (p2 + bytesInWord width + bytesInWord width + bytesInWord width) (by
    rw [succ 2, succ 1]; simp)
  have d4 := dom 4 (by omega) (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
      bytesInWord width) (by rw [succ 3, succ 2, succ 1]; simp)
  simp only [segmentLoads, List.cons_append, List.nil_append]
  rw [stepCons _ _ _ _ (by simp) (stepLoad 3 (k + 2) p2 _ s readBase (memLoad_of d0 load0)) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLsr 3 (wordShiftAmount width) bitmapPointer _ (by simp [FUPDATE_HOL]) (by omega)) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepMove 0 (k + 2) (.word p2) _
      (by simp [FUPDATE_HOL, readBase, show k ≠ 1 by omega])) rfl]
  rw [stepCons _ _ _ _ (by simp) (stepAddBytes 0 p2 _ (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLoad 4 0 (p2 + bytesInWord width) v1 _ (by simp [FUPDATE_HOL])
      (by simp [StackSemStateOps.memLoad, d1, load1])) rfl]
  rw [stepCons _ _ _ _ (by simp) (stepAddBytes 0 (p2 + bytesInWord width) _ (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLoad 6 0 (p2 + bytesInWord width + bytesInWord width) v2 _ (by simp [FUPDATE_HOL])
      (by simp [StackSemStateOps.memLoad, d2, load2])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAddBytes 0 (p2 + bytesInWord width + bytesInWord width) _ (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepLoad 7 0 (p2 + bytesInWord width + bytesInWord width + bytesInWord width) v3 _
      (by simp [FUPDATE_HOL]) (by simp [StackSemStateOps.memLoad, d3, load3])) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepAddBytes 0 (p2 + bytesInWord width + bytesInWord width + bytesInWord width) _
      (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ nonempty
    (stepLoad 1 0 (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
      bytesInWord width) v4 _ (by simp [FUPDATE_HOL])
      (by simp [StackSemStateOps.memLoad, d4, load4])) rfl]
  congr 3
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  split_ifs <;> simp_all

/-- Memory store through an address register. -/
theorem stepStore (r a : Nat) (address : BitVec width) (value : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (readA : s.regs.lookup a = some (.word address)) (readR : s.regs.lookup r = some value)
    (domain : s.mdomain address = true) :
    StackSemEvaluate.evaluate (storeInst r a, s) =
      (none, {s with memory := fun key => if key = address then value else s.memory key}) := by
  simp [storeInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp, readA, readR,
    StackSemStateOps.getVar, StackSemStateOps.memStore, domain, wordOpHOL, wordOp]

/-- The initializer's stack-bottom setup before the store list. -/
theorem runInitMemory (k : Nat) (values : List (BitVec width ⊕ Nat))
    (s : StackSemStateFiniteExact width C F) (p4 : BitVec width) (k8 : 8 ≤ k)
    (readK : s.regs.lookup k = some (.word p4))
    (domain : s.mdomain (p4 - bytesInWord width) = true) :
    StackSemEvaluate.evaluate (initMemory k values, s) =
      StackSemEvaluate.evaluate (storeListCode (k + 1) 0 values,
        {s with
          memory := fun key => if key = p4 - bytesInWord width then .word 0 else s.memory key
          regs := ((s.regs.updateEq (0, .word (bytesInWord width))).updateEq
            (k, .word (p4 - bytesInWord width))).updateEq (0, .word 0)}) := by
  simp only [initMemory]
  rw [stepCons _ _ _ _ (by simp) (stepConst 0 (bytesInWord width) _) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepSub k 0 p4 (bytesInWord width) _ (by simp [FUPDATE_HOL, show k ≠ 0 by omega, readK])
      (by simp [FUPDATE_HOL])) rfl]
  rw [stepCons _ _ _ _ (by simp) (stepConst 0 0 _) rfl]
  rw [stepCons _ _ _ _ (by simp)
    (stepStore 0 k (p4 - bytesInWord width) (.word 0) _
      (by simp [FUPDATE_HOL, show k ≠ 0 by omega]) (by simp [FUPDATE_HOL])
      (by simpa using domain)) rfl]
  rfl

/-- The final location value. -/
theorem runLocValue (s : StackSemStateFiniteExact width C F) (entry : sptDomain s.code 1) :
    StackSemEvaluate.evaluate (.locValue 0 1 0, s) =
      (none, {s with regs := s.regs.updateEq (0, .loc 1 0)}) := by
  have check : StackSem.locCheckExact s.code (1, 0) := Or.inl ⟨rfl, entry⟩
  rw [StackSemEvaluate.evaluate_locValue, if_pos check]
  rfl

/-- The literal initializer is the concatenation of the verified segments. -/
theorem initCode_segments (generateGc : Bool) (maxHeap k : Nat) :
    initCode (width := width) generateGc maxHeap k =
      listSeqHOL (segmentMiddle width ++
        (.ite .lower 3 (.reg 2) (moveHOL 3 0) (.ite .lower 4 (.reg 3) (moveHOL 3 0) .skip) ::
          (segmentLimits width maxHeap ++
            (.ite .lower 5 (.reg 0) (.seq (moveHOL 3 2) (addInst 3 5)) .skip ::
              (segmentRound width k ++ (segmentLoads width k ++
                [initMemory k (storeList.reverse.map (storeInit generateGc k)),
                  .locValue 0 1 0])))))) := by
  rfl

/-- Registers named by the store initialisation values. -/
theorem storeInit_registers (generateGc : Bool) (k n : Nat) (name : StoreName)
    (h : storeInit (width := width) generateGc k name = .inr n) :
    n = k + 2 ∨ n = 2 ∨ n = 5 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 ∨ n = 1 := by
  cases name <;> simp only [storeInit, Sum.inr.injEq, reduceCtorEq] at h <;>
    first | omega | (split at h <;> omega)

set_option linter.unusedSimpArgs false in
/-- Goal-shaped execution of the initializer tail (stack bottom, store list,
location value) from any state with the needed registers and heap. -/
theorem runTailGoal (generateGc : Bool) (k : Nat) (s6 : StackSemStateFiniteExact width C F)
    (p4 reg3 : BitVec width) (k8 : 8 ≤ k)
    (readK : s6.regs.lookup k = some (.word p4))
    (readBase : s6.regs.lookup (k + 1) = some (.word reg3))
    (present : ∀ r, (r = k + 2 ∨ r = 2 ∨ r = 5 ∨ r = 3 ∨ r = 4 ∨ r = 6 ∨ r = 7 ∨ r = 1) →
      s6.regs.lookup r ≠ none)
    (lastDomain : s6.mdomain (p4 - bytesInWord width) = true)
    (entry : sptDomain s6.code 1)
    (ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (ylen : ys.length = storeList.length)
    (storeHeap : SetSep.star (Misc.wordList reg3 ys) frame
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0 else s6.memory key),
        fun a => s6.mdomain a = true)))
    (Q : StackSemStateFiniteExact width C F → Prop)
    (finish : ∀ (r1 : WordLocW width) (m1 : BitVec width → WordLocW width),
      SetSep.star (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc k)).map
          (MemVal.memVal ((((s6.regs.updateEq (0, .word (bytesInWord width))).updateEq
            (k, .word (p4 - bytesInWord width))).updateEq (0, .word 0)))))) frame
        (SetSep.fun2Set (m1, fun a => s6.mdomain a = true)) →
      Q {s6 with
        memory := m1
        regs := ((((((s6.regs.updateEq (0, .word (bytesInWord width))).updateEq
            (k, .word (p4 - bytesInWord width))).updateEq (0, .word 0)).updateListEq
            [(k + 1, .word (reg3 + bytesInWord width *
              BitVec.ofNat width (storeList.reverse.map (storeInit (width := width) generateGc k)).length)),
              (0, r1)])).updateEq (0, .loc 1 0))}) :
    ∃ t, StackSemEvaluate.evaluate
        (listSeqHOL [initMemory k (storeList.reverse.map (storeInit generateGc k)),
          .locValue 0 1 0], s6) = (none, t) ∧ Q t := by
  have k0 : k ≠ 0 := by omega
  set values := storeList.reverse.map (storeInit (width := width) generateGc k)
  set s7 : StackSemStateFiniteExact width C F := {s6 with
    memory := fun key => if key = p4 - bytesInWord width then .word 0 else s6.memory key
    regs := ((s6.regs.updateEq (0, .word (bytesInWord width))).updateEq
      (k, .word (p4 - bytesInWord width))).updateEq (0, .word 0)} with hs7
  obtain ⟨r1, m1, heap, run⟩ := StoreListCodeThm.storeListCodeThm (k + 1) 0 values s7 reg3 frame
    ys s7.memory (fun a => s7.mdomain a = true)
    ⟨storeHeap, rfl, rfl, by simp [values, ylen], by omega,
      by simp [s7, StackSemStateOps.getVar, FUPDATE_HOL, readBase, show k + 1 ≠ k by omega],
      by simp [s7, FUPDATE_HOL],
      fun x member n eq => by
        simp only [values, List.mem_map, List.mem_reverse] at member
        obtain ⟨name, _, rfl⟩ := member
        have regs := storeInit_registers generateGc k n name eq.symm
        refine ⟨by omega, by omega, ?_⟩
        have hn0 : n ≠ 0 := by omega
        have hnk : n ≠ k := by omega
        simpa [s7, FUPDATE_HOL, hn0, hnk] using present n regs⟩
  have initRun : StackSemEvaluate.evaluate (initMemory k values, s6) =
      (none, {s7 with memory := m1, regs := (s7.regs.updateListEq
        [(k + 1, .word (reg3 + bytesInWord width * BitVec.ofNat width values.length)), (0, r1)])}) := by
    rw [runInitMemory k values s6 p4 k8 readK lastDomain]
    exact run
  refine ⟨_, ?_, finish r1 m1 heap⟩
  show StackSemEvaluate.evaluate (.seq _ _, s6) = _
  rw [StoreListCodeThm.evaluateSeqNormal _ _ s6 _ initRun rfl]
  exact runLocValue _ entry

set_option linter.unusedSimpArgs false in
/-- The full native initializer run from its register, header and heap
preconditions: the post-state differs from the input only in registers and
memory, with the original register outcomes and the stored initial values. -/
theorem runInitCode (generateGc : Bool) (maxHeap k : Nat) (s : StackSemStateFiniteExact width C F)
    (p2 p3 p4 bitmapPointer : BitVec width) (v1 v2 v3 v4 : WordLocW width)
    (good : goodDimindex width) (k8 : 8 ≤ k)
    (read2 : s.regs.lookup 2 = some (.word p2)) (read3 : s.regs.lookup 3 = some (.word p3))
    (read4 : s.regs.lookup 4 = some (.word p4))
    (domain : ∀ i, i < 5 → s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true)
    (load0 : s.memory p2 = .word bitmapPointer)
    (load1 : s.memory (p2 + bytesInWord width) = v1)
    (load2 : s.memory (p2 + bytesInWord width + bytesInWord width) = v2)
    (load3 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width) = v3)
    (load4 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
      bytesInWord width) = v4)
    (lastDomain : s.mdomain (p4 - bytesInWord width) = true)
    (entry : sptDomain s.code 1)
    (ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (ylen : ys.length = storeList.length)
    (storeHeap : SetSep.star
      (Misc.wordList (roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
        (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))) ys) frame
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0 else s.memory key),
        fun a => s.mdomain a = true))) :
    let reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
      (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))
    let half := (reg3 - p2) >>> (1 : Nat)
    ∃ t : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (initCode generateGc maxHeap k, s) = (none, t) ∧
      t = {s with memory := t.memory, regs := t.regs} ∧
      t.regs.lookup 0 = some (.loc 1 0) ∧ t.regs.lookup 1 = some v4 ∧
      t.regs.lookup 2 = some (.word (p2 + half)) ∧
      t.regs.lookup 3 = some (.word (bitmapPointer >>> wordShiftAmount width)) ∧
      t.regs.lookup 4 = some v1 ∧ t.regs.lookup 5 = some (.word half) ∧
      t.regs.lookup 6 = some v2 ∧ t.regs.lookup 7 = some v3 ∧
      t.regs.lookup k = some (.word (p4 - bytesInWord width)) ∧
      t.regs.lookup (k + 1) =
        some (.word (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)) ∧
      t.regs.lookup (k + 2) = some (.word p2) ∧
      (∀ r, 8 ≤ r → r ≠ k → r ≠ k + 1 → r ≠ k + 2 → t.regs.lookup r = s.regs.lookup r) ∧
      SetSep.star
        (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc k)).map
          (MemVal.memVal t.regs))) frame
        (SetSep.fun2Set (t.memory, fun a => s.mdomain a = true)) := by
  intro reg3 half
  have hk : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 4 ∧ k ≠ 5 ∧ k ≠ 6 ∧ k ≠ 7 := by omega
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ := hk
  rw [initCode_segments, runSegmentMiddle _ (by simp) s p2 p4 good read2 read4]
  rw [stepCons _ _ _ _ (by simp)
    (runAdjust _ p3 (middleWord p2 p4) (p2 + marginWord width) (p4 - marginWord width)
      (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, read3])
      (by simp [FUPDATE_HOL])) rfl]
  set adjusted := adjustedThird p3 (middleWord p2 p4) (p2 + marginWord width)
    (p4 - marginWord width) with hadjusted
  set shrunk := shrunkThird p2 adjusted (maxHeapWord width maxHeap) with hshrunk
  rw [runSegmentLimits maxHeap _ (by simp) _ p2 p4 adjusted
    (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL])]
  rw [stepCons _ _ _ _ (by simp)
    (runShrink _ p2 adjusted (maxHeapWord width maxHeap)
      (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL])
      (by simp [FUPDATE_HOL])) rfl]
  rw [runSegmentRound k _ (by simp) _ p2 p4 shrunk good k8
    (by simp [FUPDATE_HOL]) (by simp [FUPDATE_HOL, hshrunk]) (by simp [FUPDATE_HOL])]
  rw [runSegmentLoads k _ (by simp) _ p2 bitmapPointer v1 v2 v3 v4 good k8
    (by simp [FUPDATE_HOL, k0, k1, k2, k3]) (by simpa using domain) (by simpa using load0) (by simpa using load1)
    (by simpa using load2) (by simpa using load3) (by simpa using load4)]
  have kk : (0 : Nat) ≠ k ∧ (1 : Nat) ≠ k ∧ (2 : Nat) ≠ k ∧ (3 : Nat) ≠ k ∧ (4 : Nat) ≠ k ∧
      (5 : Nat) ≠ k ∧ (6 : Nat) ≠ k ∧ (7 : Nat) ≠ k := by omega
  obtain ⟨k0', k1', k2', k3', k4', k5', k6', k7'⟩ := kk
  dsimp only
  refine runTailGoal generateGc k _ p4 reg3 k8 ?_ ?_ ?_ ?_ ?_ ys frame ylen ?_ _ ?_
  · simp [FUPDATE_HOL, k0, k1, k2, k3, k4, k5, k6, k7]
  · simp [FUPDATE_HOL, k0, k1, k2, k3, k4, k5, k6, k7, reg3, hshrunk, hadjusted]
  · intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FUPDATE_HOL, k0, k1, k2, k3, k4, k5, k6, k7, k0', k1', k2', k3', k4', k5', k6', k7']
  · simpa using lastDomain
  · simpa using entry
  · simpa [reg3, hshrunk] using storeHeap
  · intro r1 m1 heap
    have sl : (storeList.reverse.map (storeInit (width := width) generateGc k)).length =
        storeList.length := by simp
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?others, ?heapGoal⟩
    case others =>
      intro r h8 hk hk1 hk2
      have r0 : r ≠ 0 := by omega
      have r1' : r ≠ 1 := by omega
      have r2 : r ≠ 2 := by omega
      have r3 : r ≠ 3 := by omega
      have r4 : r ≠ 4 := by omega
      have r5 : r ≠ 5 := by omega
      have r6 : r ≠ 6 := by omega
      have r7 : r ≠ 7 := by omega
      simp [FUPDATE_HOL, FUPDATE_LIST_HOL, r0, r1', r2, r3, r4, r5, r6, r7, hk, hk1, hk2]
    case heapGoal =>
      rw [StoreListCodeThm.mapMemValCongr _ _ _ (fun n member => ?_)] at heap
      · exact heap
      simp only [List.mem_map, List.mem_reverse] at member
      obtain ⟨name, _, eq⟩ := member
      have regs := storeInit_registers generateGc k n name eq
      have n0 : n ≠ 0 := by omega
      have nk1 : n ≠ k + 1 := by omega
      simp [FUPDATE_HOL, FUPDATE_LIST_HOL, n0, nk1]
    all_goals simp [FUPDATE_HOL, FUPDATE_LIST_HOL, k0, k1, k2, k3, k4, k5, k6, k7,
      k0', k1', k2', k3', k4', k5', k6', k7', sl, half, reg3, hshrunk, hadjusted]

/-! ### Separation helpers -/

instance starAssocInst {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩

instance starCommInst {α : Type} : Std.Commutative (SetSep.star (α := α)) :=
  ⟨SetSep.starComm⟩

omit [NeZero width] in
/-- A framed existential word list is a framed concrete list of that length. -/
theorem starWordListExists {β : Type} [NeZero width] (P : ((BitVec width × β) → Prop) → Prop)
    (a : BitVec width) (n : Nat) (h : (BitVec width × β) → Prop) :
    SetSep.star P (Misc.wordListExists a n) h ↔
      ∃ xs : List β, xs.length = n ∧ SetSep.star P (Misc.wordList a xs) h := by
  constructor
  · rintro ⟨left, right, partition, pLeft, ⟨xs, hxs⟩⟩
    obtain ⟨listHeap, length⟩ := (WordListExists.starCond _ _ _).mp hxs
    exact ⟨xs, length, left, right, partition, pLeft, listHeap⟩
  · rintro ⟨xs, length, left, right, partition, pLeft, listHeap⟩
    exact ⟨left, right, partition, pLeft, ⟨xs, (WordListExists.starCond _ _ _).mpr ⟨listHeap, length⟩⟩⟩

omit [NeZero width] in
/-- Every entry of the right part of a framed heap is in the heap. -/
theorem starRightMember {α : Type} (P Q : (α → Prop) → Prop) (h : α → Prop)
    (hyp : SetSep.star P Q h) : ∃ part, Q part ∧ ∀ e, part e → h e := by
  obtain ⟨left, right, partition, _, q⟩ := hyp
  exact ⟨right, q, fun e member => by rw [← partition.1]; exact Or.inr member⟩

/-- Framed element read and domain membership of a word list. -/
theorem framedListRead {β : Type} (P : ((BitVec width × β) → Prop) → Prop)
    (a : BitVec width) (xs : List β) (m : BitVec width → β) (d : BitVec width → Prop)
    (hyp : SetSep.star P (Misc.wordList a xs) (SetSep.fun2Set (m, d)))
    (i : Nat) (hi : i < xs.length) :
    m (a + bytesInWord width * BitVec.ofNat width i) = xs[i] ∧
      d (a + bytesInWord width * BitVec.ofNat width i) := by
  obtain ⟨part, listHeap, sub⟩ := starRightMember _ _ _ hyp
  have member := sub _ (StackHeap.wordListNth a xs part i hi listHeap)
  exact (SetSep.fun2SetThm m d _ _).mp member

omit [NeZero width] in
theorem list_split {β : Type} (l : List β) (a b : Nat) (h : l.length = a + b) :
    ∃ l1 l2, l = l1 ++ l2 ∧ l1.length = a ∧ l2.length = b :=
  ⟨l.take a, l.drop a, (List.take_append_drop a l).symm, by simp; omega, by simp; omega⟩

omit [NeZero width] in
theorem list_split_last {β : Type} (l : List β) (c : Nat) (h : l.length = c + 1) :
    ∃ l1 x, l = l1 ++ [x] ∧ l1.length = c := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l1, x, rfl⟩
  · simp at h
  · exact ⟨l1, x, List.concat_eq_append, by simpa using h⟩

theorem wordListSingleton {β : Type} (a : BitVec width) (x : β) :
    Misc.wordList a [x] = SetSep.one (a, x) := by
  simp only [Misc.wordList]
  rw [SetSep.starComm, StackHeap.starEmptyLeft]

/-- The initial heap region split into the heap, the store, the rest of the
stack and the final stack word (source 3545-3586). -/
theorem initHeapSplit {β : Type} (P : ((BitVec width × β) → Prop) → Prop)
    (p2 reg3 p4 : BitVec width) (heapLength stackLength : Nat)
    (m : BitVec width → β) (d : BitVec width → Prop)
    (regEq : reg3 = p2 + bytesInWord width * BitVec.ofNat width heapLength)
    (endEq : p4 = reg3 + bytesInWord width * BitVec.ofNat width stackLength)
    (long : storeList.length + 1 ≤ stackLength)
    (hyp : SetSep.star P (Misc.wordListExists p2 (heapLength + stackLength))
      (SetSep.fun2Set (m, d))) :
    ∃ (heapValues storeValues restValues : List β) (last : β),
      heapValues.length = heapLength ∧ storeValues.length = storeList.length ∧
      restValues.length = stackLength - (storeList.length + 1) ∧
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P (Misc.wordList p2 heapValues))
        (Misc.wordList reg3 storeValues))
        (Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)
          restValues))
        (SetSep.one (p4 - bytesInWord width, last)) (SetSep.fun2Set (m, d)) := by
  obtain ⟨xs, xlen, listHeap⟩ := (starWordListExists P p2 _ _).mp hyp
  obtain ⟨heapValues, tail, rfl, hlen, tlen⟩ := list_split xs heapLength stackLength xlen
  obtain ⟨storeValues, tail2, rfl, slen, t2len⟩ :=
    list_split tail storeList.length (stackLength - storeList.length) (by omega)
  obtain ⟨restValues, last, rfl, rlen⟩ :=
    list_split_last tail2 (stackLength - (storeList.length + 1)) (by omega)
  refine ⟨heapValues, storeValues, restValues, last, hlen, slen, rlen, ?_⟩
  rw [StackHeap.wordListAppend, StackHeap.wordListAppend, StackHeap.wordListAppend,
    wordListSingleton, hlen, slen, rlen, ← regEq] at listHeap
  have lastAddr : reg3 + bytesInWord width * BitVec.ofNat width storeList.length +
      bytesInWord width * BitVec.ofNat width (stackLength - (storeList.length + 1)) =
      p4 - bytesInWord width := by
    have split : stackLength = storeList.length + (stackLength - (storeList.length + 1)) + 1 := by
      omega
    rw [endEq, split, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_add,
      BitVec.mul_one, ← split]
    simp only [← BitVec.add_assoc, BitVec.add_sub_cancel]
  rw [lastAddr] at listHeap
  rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star P (Misc.wordList p2 heapValues))
      (Misc.wordList reg3 storeValues))
      (Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length) restValues))
      (SetSep.one (p4 - bytesInWord width, last)) =
    SetSep.star P (SetSep.star (Misc.wordList p2 heapValues) (SetSep.star
      (Misc.wordList reg3 storeValues) (SetSep.star
        (Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length) restValues)
        (SetSep.one (p4 - bytesInWord width, last))))) by ac_rfl]
  exact listHeap

/-! ### Layout arithmetic of the computed pointers -/

theorem middleNat (good : goodDimindex width) (p2 p4 : BitVec width)
    (le : p2.toNat ≤ p4.toNat) :
    (middleWord p2 p4).toNat =
      p2.toNat + (p4.toNat - p2.toNat) / (2 * (width / 8)) * (width / 8) := by
  rcases good with rfl | rfl <;>
  · simp only [middleWord, wordShiftAmount]; norm_num; bv_omega

theorem lowNat (good : goodDimindex width) (p2 : BitVec width)
    (small : p2.toNat + 255 * (width / 8) < 2 ^ width) :
    (p2 + marginWord width).toNat = p2.toNat + 255 * (width / 8) := by
  rcases good with rfl | rfl <;>
  · simp only [marginWord, bytesInWord, maxStackAlloc] at *; norm_num at *; bv_omega

theorem highNat (good : goodDimindex width) (p4 : BitVec width)
    (large : 255 * (width / 8) ≤ p4.toNat) :
    (p4 - marginWord width).toNat = p4.toNat - 255 * (width / 8) := by
  rcases good with rfl | rfl <;>
  · simp only [marginWord, bytesInWord, maxStackAlloc] at *; norm_num at *; bv_omega

omit [NeZero width] in
theorem adjustedBounds (p3 middle low high : BitVec width)
    (lowMid : low.toNat ≤ middle.toNat) (midHigh : middle.toNat ≤ high.toNat) :
    low.toNat ≤ (adjustedThird p3 middle low high).toNat ∧
      (adjustedThird p3 middle low high).toNat ≤ high.toNat := by
  unfold adjustedThird
  split_ifs with h1 h2
  · exact ⟨lowMid, midHigh⟩
  · exact ⟨lowMid, midHigh⟩
  · rw [BitVec.lt_def] at h1 h2
    omega

omit [NeZero width] in
theorem adjustedInRange (p3 middle low high : BitVec width)
    (lowP : low.toNat ≤ p3.toNat) (pHigh : p3.toNat ≤ high.toNat) :
    adjustedThird p3 middle low high = p3 := by
  unfold adjustedThird
  rw [if_neg (by rw [BitVec.lt_def]; omega), if_neg (by rw [BitVec.lt_def]; omega)]

/-- Heap offset chosen by the shrink conditional. -/
theorem shrunkNat (good : goodDimindex width) (p2 adjusted : BitVec width) (maxHeap : Nat)
    (le : p2.toNat ≤ adjusted.toNat) :
    (shrunkThird p2 adjusted (maxHeapWord width maxHeap)).toNat =
      p2.toNat + (if maxHeap * (width / 8) < 2 ^ width ∧
          maxHeap * (width / 8) < adjusted.toNat - p2.toNat
        then maxHeap * (width / 8) else adjusted.toNat - p2.toNat) := by
  rcases good with rfl | rfl <;>
  · simp only [shrunkThird, maxHeapWord, bytesInWord] at *
    norm_num at *
    split_ifs <;> bv_omega

theorem roundedNat (good : goodDimindex width) (p2 shrunk : BitVec width)
    (le : p2.toNat ≤ shrunk.toNat) :
    (roundedThird p2 shrunk).toNat =
      p2.toNat + (shrunk.toNat - p2.toNat) / (2 * (width / 8)) * (2 * (width / 8)) := by
  rcases good with rfl | rfl <;>
  · simp only [roundedThird, wordShiftAmount]; norm_num; bv_omega

theorem halfNat (good : goodDimindex width) (p2 reg3 : BitVec width)
    (le : p2.toNat ≤ reg3.toNat) (even : (reg3.toNat - p2.toNat) % (2 * (width / 8)) = 0) :
    ((reg3 - p2) >>> (1 : Nat)).toNat = (reg3.toNat - p2.toNat) / 2 := by
  rcases good with rfl | rfl <;>
  · norm_num at *; bv_omega

/-- The heap/store/stack layout fixed by the initializer's pointer arithmetic:
the original `heap_length`/`stack_length` decomposition (source 3446-3550). -/
theorem initLayout (good : goodDimindex width) (maxHeap : Nat) (hm : maxStackAlloc ≤ maxHeap)
    (p2 p3 p4 : BitVec width) (le : p2.toNat ≤ p4.toNat)
    (big : 1024 * (width / 8) ≤ p4.toNat - p2.toNat)
    (a2 : p2.toNat % (width / 8) = 0) (a4 : p4.toNat % (width / 8) = 0) :
    let adjusted := adjustedThird p3 (middleWord p2 p4) (p2 + marginWord width)
      (p4 - marginWord width)
    let shrunk := shrunkThird p2 adjusted (maxHeapWord width maxHeap)
    let reg3 := roundedThird p2 shrunk
    p2.toNat ≤ adjusted.toNat ∧ p2.toNat ≤ shrunk.toNat ∧
    ∃ heapLength stackLength : Nat,
      reg3.toNat = p2.toNat + heapLength * (width / 8) ∧
      p4.toNat = reg3.toNat + stackLength * (width / 8) ∧
      heapLength % 2 = 0 ∧ heapLength ≤ maxHeap ∧
      maxStackAlloc ≤ heapLength + storeList.length ∧ maxStackAlloc ≤ stackLength := by
  intro adjusted shrunk reg3
  have p4lt : p4.toNat < 2 ^ width := p4.isLt
  have low := lowNat good p2 (by omega)
  have high := highNat good p4 (by omega)
  have mid := middleNat good p2 p4 le
  have sl : storeList.length = 48 := rfl
  have hm' : 255 ≤ maxHeap := hm
  have hcase : (width / 8 = 4 ∧ 2 ^ width = 2 ^ 32) ∨ (width / 8 = 8 ∧ 2 ^ width = 2 ^ 64) := by
    rcases good with h | h <;> subst h <;> norm_num
  rcases hcase with ⟨hB, hpow⟩ | ⟨hB, hpow⟩ <;>
  · norm_num at hpow
    rw [hB] at mid low high a2 a4 big
    rw [hpow] at p4lt
    have bounds : (p2 + marginWord width).toNat ≤ adjusted.toNat ∧
        adjusted.toNat ≤ (p4 - marginWord width).toNat :=
      adjustedBounds p3 (middleWord p2 p4) (p2 + marginWord width)
        (p4 - marginWord width) (by omega) (by omega)
    have adjLe : p2.toNat ≤ adjusted.toNat := bounds.1.trans' (by omega)
    have shr := shrunkNat good p2 adjusted maxHeap adjLe
    rw [hB, hpow] at shr
    have shr' : shrunk.toNat = _ := shr
    clear shr
    have shrLe : p2.toNat ≤ shrunk.toNat := by rw [shr']; split_ifs <;> omega
    have rnd := roundedNat good p2 shrunk shrLe
    rw [hB] at rnd
    have rnd' : reg3.toNat = _ := rnd
    clear rnd mid
    refine ⟨adjLe, shrLe, (shrunk.toNat - p2.toNat) / (2 * (width / 8)) * 2,
      (p4.toNat - reg3.toNat) / (width / 8), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hB, sl, maxStackAlloc] <;> split_ifs at shr' <;> omega

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
