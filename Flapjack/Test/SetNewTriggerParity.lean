import Flapjack.Compiler.Backend.StackAlloc.Proofs.SetNewTrigger

/-! Kernel replay of original new_trig and actual StackSem SetNewTrigger rows.
Unobserved fields remain arbitrary, and observed untouched fields are checked. -/
namespace Flapjack.Test.SetNewTriggerParity
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordGcFunctions Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackRemove

private def fixture {width : Nat} [NeZero width]
    (s : StackSemStateFiniteExact width Unit Unit) (endh w : BitVec width) :=
  {s with
    regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).updateEq (0,.word 42)).updateEq (3,.word 100)).updateEq (8,.word endh)
    store := ((HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW width)).updateEq (.allocSize,.word w)).updateEq (.currHeap,.word 9)
    useStore := true
    clock := 6}

-- Original trigger_generation_cap.
example : newTrig (1000 : BitVec 64) 16 [4] = 32 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_generation_cap.
example (s : StackSemStateFiniteExact 64 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 1100 16)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 132),some (.word 16),some (.word 1000),
      some (.word 132),6,some (.word 42),some (.word 100),some (.word 1100),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_heap_cap.
example : newTrig (24 : BitVec 64) 16 [4] = 24 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_heap_cap.
example (s : StackSemStateFiniteExact 64 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 124 16)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 32),some (.word 16),some (.word 24),
      some (.word 124),6,some (.word 42),some (.word 100),some (.word 124),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_alloc_exceeds_heap.
example : newTrig (24 : BitVec 64) 64 [4] = 24 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_alloc_exceeds_heap.
example (s : StackSemStateFiniteExact 64 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 124 64)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 32),some (.word 64),some (.word 24),
      some (.word 124),6,some (.word 42),some (.word 100),some (.word 124),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_aligned_alloc.
example : newTrig (1000 : BitVec 64) 64 [4] = 64 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_aligned_alloc.
example (s : StackSemStateFiniteExact 64 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 1100 64)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 32),some (.word 164),some (.word 1000),
      some (.word 164),6,some (.word 42),some (.word 100),some (.word 1100),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, AndOp.and, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_unaligned_alloc.
example : newTrig (1000 : BitVec 64) 65 [4] = 1000 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_unaligned_alloc.
example (s : StackSemStateFiniteExact 64 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 1100 65)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 32),some (.word 65),some (.word 1000),
      some (.word 1100),6,some (.word 42),some (.word 100),some (.word 1100),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, AndOp.and, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_32_aligned_alloc.
example : newTrig (1000 : BitVec 32) 20 [4] = 20 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_32_aligned_alloc.
example (s : StackSemStateFiniteExact 32 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 1100 20)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 16),some (.word 120),some (.word 1000),
      some (.word 120),6,some (.word 42),some (.word 100),some (.word 1100),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, AndOp.and, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

-- Original trigger_32_unaligned_alloc.
example : newTrig (1000 : BitVec 32) 21 [4] = 1000 := by
  rw [newTrig_branch_eq _ _ _ (by simp [goodDimindex])]
  simp [getGenSize, wordSemBytesInWord]
-- Original trigger_run_32_unaligned_alloc.
example (s : StackSemStateFiniteExact 32 Unit Unit) :
    (let (r,t) := evaluate (setNewTrigger 8 3 [4],fixture s 1100 21)
     (r,t.regs.lookup 1,t.regs.lookup 7,t.regs.lookup 4,
      t.store.lookup .triggerGC,t.clock,t.regs.lookup 0,
      t.regs.lookup 3,t.regs.lookup 8,t.store.lookup .currHeap)) =
    (none,some (.word 16),some (.word 21),some (.word 1000),
      some (.word 1100),6,some (.word 42),some (.word 100),some (.word 1100),some (.word 9)) := by
  simp [fixture, setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
    constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, AndOp.and, setVar, setStore,
    wordOpHOL, wordOp, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    getGenSize, wordSemBytesInWord]

end Flapjack.Test.SetNewTriggerParity
