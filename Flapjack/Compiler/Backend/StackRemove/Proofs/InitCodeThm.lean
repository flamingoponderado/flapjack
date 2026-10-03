import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreListCodeThm
import Flapjack.Compiler.Backend.StackRemove.InitCode
import Flapjack.Misc.GoodDimindex

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

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
