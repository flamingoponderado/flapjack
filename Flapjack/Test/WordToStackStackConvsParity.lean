import Flapjack.Compiler.Backend.WordToStack.Proofs.StackConventions

namespace Flapjack.Test.WordToStackStackConvsParity
open Flapjack Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.StackConventions
/- Same-input fresh original source EVERY EVALs and original whole-compiler
conventions theorem applications. All three target predicates include both
stubs. Config fields outside register count and avoid list remain arbitrary.
No eager irrelevant bitmap EVAL, original full-proof replay or equivalence is
claimed. Negative source guards remain independently false. -/

-- wsc_1_0_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_empty_alloc, wsc_1_0_empty_regs, wsc_1_0_empty_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_skip_alloc, wsc_1_0_skip_regs, wsc_1_0_skip_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.skip)] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_alloc_alloc, wsc_1_0_alloc_regs, wsc_1_0_alloc_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_seq_bitmap_alloc, wsc_1_0_seq_bitmap_regs, wsc_1_0_seq_bitmap_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_handler_alloc, wsc_1_0_handler_regs, wsc_1_0_handler_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_duplicate_ids_alloc, wsc_1_0_duplicate_ids_regs, wsc_1_0_duplicate_ids_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_huge_argcount_alloc, wsc_1_0_huge_argcount_regs, wsc_1_0_huge_argcount_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_tail_ignore_alloc, wsc_1_0_tail_ignore_regs, wsc_1_0_tail_ignore_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_1_0_rich_alloc, wsc_1_0_rich_regs, wsc_1_0_rich_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_0_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_1_0_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_1_0_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_1_1_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_empty_alloc, wsc_1_1_empty_regs, wsc_1_1_empty_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_skip_alloc, wsc_1_1_skip_regs, wsc_1_1_skip_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.skip)] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_alloc_alloc, wsc_1_1_alloc_regs, wsc_1_1_alloc_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_seq_bitmap_alloc, wsc_1_1_seq_bitmap_regs, wsc_1_1_seq_bitmap_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_handler_alloc, wsc_1_1_handler_regs, wsc_1_1_handler_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_duplicate_ids_alloc, wsc_1_1_duplicate_ids_regs, wsc_1_1_duplicate_ids_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_huge_argcount_alloc, wsc_1_1_huge_argcount_regs, wsc_1_1_huge_argcount_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_tail_ignore_alloc, wsc_1_1_tail_ignore_regs, wsc_1_1_tail_ignore_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_1_1_rich_alloc, wsc_1_1_rich_regs, wsc_1_1_rich_calls
example (conf : AsmConfigExact 1) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_1_1_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_1_1_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_1_1_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_2_0_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_empty_alloc, wsc_2_0_empty_regs, wsc_2_0_empty_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_skip_alloc, wsc_2_0_skip_regs, wsc_2_0_skip_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.skip)] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_alloc_alloc, wsc_2_0_alloc_regs, wsc_2_0_alloc_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_seq_bitmap_alloc, wsc_2_0_seq_bitmap_regs, wsc_2_0_seq_bitmap_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_handler_alloc, wsc_2_0_handler_regs, wsc_2_0_handler_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_duplicate_ids_alloc, wsc_2_0_duplicate_ids_regs, wsc_2_0_duplicate_ids_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_huge_argcount_alloc, wsc_2_0_huge_argcount_regs, wsc_2_0_huge_argcount_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_tail_ignore_alloc, wsc_2_0_tail_ignore_regs, wsc_2_0_tail_ignore_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_2_0_rich_alloc, wsc_2_0_rich_regs, wsc_2_0_rich_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_0_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_2_0_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_2_0_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_2_1_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_empty_alloc, wsc_2_1_empty_regs, wsc_2_1_empty_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_skip_alloc, wsc_2_1_skip_regs, wsc_2_1_skip_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.skip)] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_alloc_alloc, wsc_2_1_alloc_regs, wsc_2_1_alloc_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_seq_bitmap_alloc, wsc_2_1_seq_bitmap_regs, wsc_2_1_seq_bitmap_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_handler_alloc, wsc_2_1_handler_regs, wsc_2_1_handler_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_duplicate_ids_alloc, wsc_2_1_duplicate_ids_regs, wsc_2_1_duplicate_ids_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_huge_argcount_alloc, wsc_2_1_huge_argcount_regs, wsc_2_1_huge_argcount_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_tail_ignore_alloc, wsc_2_1_tail_ignore_regs, wsc_2_1_tail_ignore_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_2_1_rich_alloc, wsc_2_1_rich_regs, wsc_2_1_rich_calls
example (conf : AsmConfigExact 2) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_2_1_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_2_1_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_2_1_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 2))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_8_0_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_empty_alloc, wsc_8_0_empty_regs, wsc_8_0_empty_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_skip_alloc, wsc_8_0_skip_regs, wsc_8_0_skip_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.skip)] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_alloc_alloc, wsc_8_0_alloc_regs, wsc_8_0_alloc_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_seq_bitmap_alloc, wsc_8_0_seq_bitmap_regs, wsc_8_0_seq_bitmap_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_handler_alloc, wsc_8_0_handler_regs, wsc_8_0_handler_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_duplicate_ids_alloc, wsc_8_0_duplicate_ids_regs, wsc_8_0_duplicate_ids_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_huge_argcount_alloc, wsc_8_0_huge_argcount_regs, wsc_8_0_huge_argcount_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_tail_ignore_alloc, wsc_8_0_tail_ignore_regs, wsc_8_0_tail_ignore_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_8_0_rich_alloc, wsc_8_0_rich_regs, wsc_8_0_rich_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_0_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_8_0_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_8_0_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_8_1_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_empty_alloc, wsc_8_1_empty_regs, wsc_8_1_empty_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_skip_alloc, wsc_8_1_skip_regs, wsc_8_1_skip_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.skip)] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_alloc_alloc, wsc_8_1_alloc_regs, wsc_8_1_alloc_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_seq_bitmap_alloc, wsc_8_1_seq_bitmap_regs, wsc_8_1_seq_bitmap_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_handler_alloc, wsc_8_1_handler_regs, wsc_8_1_handler_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_duplicate_ids_alloc, wsc_8_1_duplicate_ids_regs, wsc_8_1_duplicate_ids_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_huge_argcount_alloc, wsc_8_1_huge_argcount_regs, wsc_8_1_huge_argcount_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_tail_ignore_alloc, wsc_8_1_tail_ignore_regs, wsc_8_1_tail_ignore_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_8_1_rich_alloc, wsc_8_1_rich_regs, wsc_8_1_rich_calls
example (conf : AsmConfigExact 8) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_8_1_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_8_1_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_8_1_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 8))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_64_0_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_empty_alloc, wsc_64_0_empty_regs, wsc_64_0_empty_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_skip_alloc, wsc_64_0_skip_regs, wsc_64_0_skip_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.skip)] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_alloc_alloc, wsc_64_0_alloc_regs, wsc_64_0_alloc_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_seq_bitmap_alloc, wsc_64_0_seq_bitmap_regs, wsc_64_0_seq_bitmap_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_handler_alloc, wsc_64_0_handler_regs, wsc_64_0_handler_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_duplicate_ids_alloc, wsc_64_0_duplicate_ids_regs, wsc_64_0_duplicate_ids_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_huge_argcount_alloc, wsc_64_0_huge_argcount_regs, wsc_64_0_huge_argcount_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_tail_ignore_alloc, wsc_64_0_tail_ignore_regs, wsc_64_0_tail_ignore_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_64_0_rich_alloc, wsc_64_0_rich_regs, wsc_64_0_rich_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_0_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_64_0_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_64_0_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_64_1_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_empty_alloc, wsc_64_1_empty_regs, wsc_64_1_empty_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_skip_alloc, wsc_64_1_skip_regs, wsc_64_1_skip_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.skip)] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_alloc_alloc, wsc_64_1_alloc_regs, wsc_64_1_alloc_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_seq_bitmap_alloc, wsc_64_1_seq_bitmap_regs, wsc_64_1_seq_bitmap_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_handler_alloc, wsc_64_1_handler_regs, wsc_64_1_handler_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_duplicate_ids_alloc, wsc_64_1_duplicate_ids_regs, wsc_64_1_duplicate_ids_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_huge_argcount_alloc, wsc_64_1_huge_argcount_regs, wsc_64_1_huge_argcount_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_tail_ignore_alloc, wsc_64_1_tail_ignore_regs, wsc_64_1_tail_ignore_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_64_1_rich_alloc, wsc_64_1_rich_regs, wsc_64_1_rich_calls
example (conf : AsmConfigExact 64) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_64_1_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_64_1_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_64_1_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_80_0_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_empty_alloc, wsc_80_0_empty_regs, wsc_80_0_empty_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_skip_alloc, wsc_80_0_skip_regs, wsc_80_0_skip_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.skip)] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_alloc_alloc, wsc_80_0_alloc_regs, wsc_80_0_alloc_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_seq_bitmap_alloc, wsc_80_0_seq_bitmap_regs, wsc_80_0_seq_bitmap_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_handler_alloc, wsc_80_0_handler_regs, wsc_80_0_handler_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_duplicate_ids_alloc, wsc_80_0_duplicate_ids_regs, wsc_80_0_duplicate_ids_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_huge_argcount_alloc, wsc_80_0_huge_argcount_regs, wsc_80_0_huge_argcount_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_tail_ignore_alloc, wsc_80_0_tail_ignore_regs, wsc_80_0_tail_ignore_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = true := by cbv

-- wsc_80_0_rich_alloc, wsc_80_0_rich_regs, wsc_80_0_rich_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 9, avoidRegs := []} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 6) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 9, avoidRegs := []} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 4 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_0_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_80_0_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_80_0_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 4 row.2.2) = false := by cbv

-- wsc_80_1_empty_guard
example : (([] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_empty_alloc, wsc_80_1_empty_regs, wsc_80_1_empty_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false []).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_skip_guard
example : (([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_skip_alloc, wsc_80_1_skip_regs, wsc_80_1_skip_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.skip)]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.skip)] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_alloc_guard
example : (([(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_alloc_alloc, wsc_80_1_alloc_regs, wsc_80_1_alloc_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,3,.alloc 2 (.ln,sptInsert 32 () .ln))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_seq_bitmap_guard
example : (([(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_seq_bitmap_alloc, wsc_80_1_seq_bitmap_regs, wsc_80_1_seq_bitmap_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,0,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(21,9,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_handler_guard
example : (([(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_handler_alloc, wsc_80_1_handler_regs, wsc_80_1_handler_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,7,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop .ln (.alloc 2 (.ln,sptInsert 32 () .ln)) .ln,7,9)) none [2,4,6,8,10] (some (2,.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_duplicate_ids_guard
example : (([(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_duplicate_ids_alloc, wsc_80_1_duplicate_ids_regs, wsc_80_1_duplicate_ids_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,2,.alloc 2 (.ln,sptInsert 32 () .ln)),(20,8,.get 1180591620717411303424 .currHeap),(20,3,.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_huge_argcount_guard
example : (([(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_huge_argcount_alloc, wsc_80_1_huge_argcount_regs, wsc_80_1_huge_argcount_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(20,1180591620717411303424,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_tail_ignore_guard
example : (([(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_tail_ignore_alloc, wsc_80_1_tail_ignore_regs, wsc_80_1_tail_ignore_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(21,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_rich_guard
example : (([(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = true := by cbv

-- wsc_80_1_rich_alloc, wsc_80_1_rich_regs, wsc_80_1_rich_calls
example (conf : AsmConfigExact 80) :
    let outputs := (compileNative {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} false [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))]).2.2.2;
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p 10) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  dsimp only
  apply wordToStackStackConvs {conf with regCount := 16, avoidRegs := [2,2,1180591620717411303424]} [(0,0,.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)),(1,2,.loop .ln (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) .ln),(2,3,.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.alloc 2 (.ln,sptInsert 32 () .ln))),(3,17,.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9)))] _ _ _ _ 8 rfl
  · cbv
  · rfl
  · cbv

-- wsc_80_1_negative_odd
example : (([(20,0,.get 3 .currHeap)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_80_1_negative_alloc_bad
example : (([(20,0,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

-- wsc_80_1_negative_call_bad
example : (([(20,0,.call none none [2] none)] : List (Nat × Nat × WordLangProgHOL (BitVec 80))).all fun row => postAllocConventionsHOL 8 row.2.2) = false := by cbv

end Flapjack.Test.WordToStackStackConvsParity
