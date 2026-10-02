import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundCompiler

namespace Flapjack.Test.WordToStackRegCompilerParity
open Flapjack Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.RegisterBoundCompiler
/- Same-input fresh original source-guard EVALs and whole original theorem
applications. Deep nested programs exercise actual bitmap threading through
Alloc, Seq, If, Loop and returned/handler Calls. No eager bitmap evaluation or
cross-language equivalence is claimed. -/

-- rbc_1_0_must_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_0_must_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_loop_if_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_0_loop_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_seq_loops_guard
example : postAllocConventionsHOL (width := 1) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_0_seq_loops_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_if_must_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_0_if_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_nested_handler_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_1_0_nested_handler_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_handler_in_loop_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_0_handler_in_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_handler_in_if_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_1_0_handler_in_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_deep_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_0_deep_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_0_tail_ignore_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_1_0_tail_ignore_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_must_seq_guard
example : postAllocConventionsHOL (width := 1) 8 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_1_must_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_loop_if_guard
example : postAllocConventionsHOL (width := 1) 8 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_1_loop_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_seq_loops_guard
example : postAllocConventionsHOL (width := 1) 8 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_1_seq_loops_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_if_must_guard
example : postAllocConventionsHOL (width := 1) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_1_if_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_nested_handler_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_1_1_nested_handler_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_handler_in_loop_guard
example : postAllocConventionsHOL (width := 1) 8 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_1_handler_in_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_handler_in_if_guard
example : postAllocConventionsHOL (width := 1) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_1_1_handler_in_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_deep_seq_guard
example : postAllocConventionsHOL (width := 1) 8 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_1_deep_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_1_tail_ignore_guard
example : postAllocConventionsHOL (width := 1) 8 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_1_1_tail_ignore_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_must_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_2_must_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_loop_if_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_2_loop_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_seq_loops_guard
example : postAllocConventionsHOL (width := 1) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_2_seq_loops_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_if_must_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_1_2_if_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_nested_handler_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_1_2_nested_handler_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_handler_in_loop_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_1_2_handler_in_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_handler_in_if_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_1_2_handler_in_if_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_deep_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_1_2_deep_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_1_2_tail_ignore_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_1_2_tail_ignore_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_must_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_0_must_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_loop_if_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_0_loop_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_seq_loops_guard
example : postAllocConventionsHOL (width := 2) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_0_seq_loops_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_if_must_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_0_if_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_nested_handler_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_2_0_nested_handler_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_handler_in_loop_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_0_handler_in_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_handler_in_if_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_2_0_handler_in_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_deep_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_0_deep_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_0_tail_ignore_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_2_0_tail_ignore_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_must_seq_guard
example : postAllocConventionsHOL (width := 2) 8 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_1_must_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_loop_if_guard
example : postAllocConventionsHOL (width := 2) 8 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_1_loop_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_seq_loops_guard
example : postAllocConventionsHOL (width := 2) 8 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_1_seq_loops_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_if_must_guard
example : postAllocConventionsHOL (width := 2) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_1_if_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_nested_handler_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_2_1_nested_handler_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_handler_in_loop_guard
example : postAllocConventionsHOL (width := 2) 8 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_1_handler_in_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_handler_in_if_guard
example : postAllocConventionsHOL (width := 2) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_2_1_handler_in_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_deep_seq_guard
example : postAllocConventionsHOL (width := 2) 8 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_1_deep_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_1_tail_ignore_guard
example : postAllocConventionsHOL (width := 2) 8 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_2_1_tail_ignore_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_must_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_2_must_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_loop_if_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_2_loop_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_seq_loops_guard
example : postAllocConventionsHOL (width := 2) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_2_seq_loops_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_if_must_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_2_2_if_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_nested_handler_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_2_2_nested_handler_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_handler_in_loop_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_2_2_handler_in_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_handler_in_if_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_2_2_handler_in_if_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_deep_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_2_2_deep_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_2_2_tail_ignore_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_2_2_tail_ignore_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_must_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_0_must_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_loop_if_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_0_loop_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_seq_loops_guard
example : postAllocConventionsHOL (width := 8) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_0_seq_loops_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_if_must_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_0_if_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_nested_handler_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_8_0_nested_handler_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_handler_in_loop_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_0_handler_in_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_handler_in_if_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_8_0_handler_in_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_deep_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_0_deep_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_0_tail_ignore_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_8_0_tail_ignore_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_must_seq_guard
example : postAllocConventionsHOL (width := 8) 8 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_1_must_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_loop_if_guard
example : postAllocConventionsHOL (width := 8) 8 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_1_loop_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_seq_loops_guard
example : postAllocConventionsHOL (width := 8) 8 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_1_seq_loops_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_if_must_guard
example : postAllocConventionsHOL (width := 8) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_1_if_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_nested_handler_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_8_1_nested_handler_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_handler_in_loop_guard
example : postAllocConventionsHOL (width := 8) 8 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_1_handler_in_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_handler_in_if_guard
example : postAllocConventionsHOL (width := 8) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_8_1_handler_in_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_deep_seq_guard
example : postAllocConventionsHOL (width := 8) 8 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_1_deep_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_1_tail_ignore_guard
example : postAllocConventionsHOL (width := 8) 8 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_8_1_tail_ignore_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_must_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_2_must_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_loop_if_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_2_loop_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_seq_loops_guard
example : postAllocConventionsHOL (width := 8) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_2_seq_loops_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_if_must_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_8_2_if_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_nested_handler_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_8_2_nested_handler_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_handler_in_loop_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_8_2_handler_in_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_handler_in_if_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_8_2_handler_in_if_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_deep_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_8_2_deep_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_8_2_tail_ignore_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_8_2_tail_ignore_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_must_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_0_must_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_loop_if_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_0_loop_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_seq_loops_guard
example : postAllocConventionsHOL (width := 64) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_0_seq_loops_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_if_must_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_0_if_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_nested_handler_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_64_0_nested_handler_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_handler_in_loop_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_0_handler_in_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_handler_in_if_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_64_0_handler_in_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_deep_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_0_deep_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_0_tail_ignore_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_64_0_tail_ignore_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_must_seq_guard
example : postAllocConventionsHOL (width := 64) 8 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_1_must_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_loop_if_guard
example : postAllocConventionsHOL (width := 64) 8 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_1_loop_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_seq_loops_guard
example : postAllocConventionsHOL (width := 64) 8 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_1_seq_loops_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_if_must_guard
example : postAllocConventionsHOL (width := 64) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_1_if_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_nested_handler_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_64_1_nested_handler_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_handler_in_loop_guard
example : postAllocConventionsHOL (width := 64) 8 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_1_handler_in_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_handler_in_if_guard
example : postAllocConventionsHOL (width := 64) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_64_1_handler_in_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_deep_seq_guard
example : postAllocConventionsHOL (width := 64) 8 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_1_deep_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_1_tail_ignore_guard
example : postAllocConventionsHOL (width := 64) 8 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_64_1_tail_ignore_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_must_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_2_must_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_loop_if_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_2_loop_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_seq_loops_guard
example : postAllocConventionsHOL (width := 64) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_2_seq_loops_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_if_must_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_64_2_if_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_nested_handler_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_64_2_nested_handler_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_handler_in_loop_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_64_2_handler_in_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_handler_in_if_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_64_2_handler_in_if_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_deep_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_64_2_deep_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_64_2_tail_ignore_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_64_2_tail_ignore_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_must_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_0_must_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_loop_if_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_0_loop_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_seq_loops_guard
example : postAllocConventionsHOL (width := 80) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_0_seq_loops_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_if_must_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_0_if_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_nested_handler_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_80_0_nested_handler_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_handler_in_loop_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_0_handler_in_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_handler_in_if_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_80_0_handler_in_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_deep_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_0_deep_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_0_tail_ignore_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_80_0_tail_ignore_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_must_seq_guard
example : postAllocConventionsHOL (width := 80) 8 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_1_must_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_loop_if_guard
example : postAllocConventionsHOL (width := 80) 8 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_1_loop_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_seq_loops_guard
example : postAllocConventionsHOL (width := 80) 8 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_1_seq_loops_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_if_must_guard
example : postAllocConventionsHOL (width := 80) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_1_if_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_nested_handler_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_80_1_nested_handler_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_handler_in_loop_guard
example : postAllocConventionsHOL (width := 80) 8 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_1_handler_in_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_handler_in_if_guard
example : postAllocConventionsHOL (width := 80) 8 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_80_1_handler_in_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_deep_seq_guard
example : postAllocConventionsHOL (width := 80) 8 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_1_deep_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_1_tail_ignore_guard
example : postAllocConventionsHOL (width := 80) 8 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_80_1_tail_ignore_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_must_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_2_must_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_loop_if_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_2_loop_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_seq_loops_guard
example : postAllocConventionsHOL (width := 80) 4 (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_2_seq_loops_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln)) (.loop (sptInsert 32 () .ln) (.get 1180591620717411303424 .currHeap) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_if_must_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) = true := by cbv

-- rbc_80_2_if_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln))) (.mustTerminate (.get 1180591620717411303424 .currHeap))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_nested_handler_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) = true := by cbv

-- rbc_80_2_nested_handler_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.loop (sptInsert 32 () .ln) (.seq (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (sptInsert 34 () .ln),7,9)) none [2,4,6,8,10] (some (2,.mustTerminate (.ite .equal 1180591620717411303424 (.imm 7) (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln))),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_handler_in_loop_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) = true := by cbv

-- rbc_80_2_handler_in_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop (sptInsert 32 () .ln) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.mustTerminate (.alloc 2 (.ln,sptInsert 32 () .ln)),7,9)) none [2,4,6,8,10] (some (2,.seq (.get 1180591620717411303424 .currHeap) (.alloc 2 (.ln,sptInsert 32 () .ln)),70,90))) (sptInsert 34 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_handler_in_if_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) = true := by cbv

-- rbc_80_2_handler_in_if_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.get 1180591620717411303424 .currHeap,70,90))) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.get 1180591620717411303424 .currHeap,7,9)) none [2,4,6,8,10] (some (2,.alloc 2 (.ln,sptInsert 32 () .ln),70,90)))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_deep_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) = true := by cbv

-- rbc_80_2_deep_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.loop (sptInsert 32 () .ln) (.seq (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 2 (.ln,sptInsert 32 () .ln)) (.get 1180591620717411303424 .currHeap)) (.call (some ([2,4],(.ln,sptInsert 32 () .ln),.alloc 2 (.ln,sptInsert 32 () .ln),7,9)) none [2,4,6,8,10] (some (2,.loop (sptInsert 32 () .ln) (.alloc 2 (.ln,sptInsert 32 () .ln)) (sptInsert 34 () .ln),70,90)))) (sptInsert 34 () .ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

-- rbc_80_2_tail_ignore_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbc_80_2_tail_ignore_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none none [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBound
  · cbv
  · cbv
  · rfl

end Flapjack.Test.WordToStackRegCompilerParity
