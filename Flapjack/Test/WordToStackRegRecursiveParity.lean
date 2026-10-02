import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive

namespace Flapjack.Test.WordToStackRegRecursiveParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.RegisterBoundRecursive
open Flapjack.WordToStackProofs.RegisterBoundFlat
/- Same-input original guard EVALs and original full-theorem applications.
Nested Alloc cases avoid eager irrelevant bitmap computation. Configurations are
arbitrary, so immediate acceptance and rejection are both retained. Regression
evidence, not a replay of the full original proof or cross-language equivalence. -/

-- rbr_1_0_must_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_0_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_loop_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_1_0_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_0_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_if_reg_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_0_if_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_if_imm_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_0_if_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_tail_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_0_tail_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_0_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_0_tail_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_0_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_0_tail_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_0_return_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_1_0_return_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_1_0_return_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_1_0_return_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_handler_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_0_handler_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_0_handler_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_0_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_0_handler_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_must_guard
example : postAllocConventionsHOL (width := 1) 8 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_1_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_loop_guard
example : postAllocConventionsHOL (width := 1) 8 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_1_1_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_seq_guard
example : postAllocConventionsHOL (width := 1) 8 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_1_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_if_reg_guard
example : postAllocConventionsHOL (width := 1) 8 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_1_if_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_if_imm_guard
example : postAllocConventionsHOL (width := 1) 8 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_1_if_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_tail_direct_guard
example : postAllocConventionsHOL (width := 1) 8 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_1_tail_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_1_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 8 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_1_tail_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_1_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 8 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_1_tail_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_1_return_direct_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_1_1_return_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_1_1_return_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_1_1_return_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_handler_direct_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_1_handler_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_1_handler_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_1_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_1_handler_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_must_guard
example : postAllocConventionsHOL (width := 1) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_2_must_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_loop_guard
example : postAllocConventionsHOL (width := 1) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_1_2_loop_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_seq_guard
example : postAllocConventionsHOL (width := 1) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_2_seq_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_if_reg_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_2_if_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_if_imm_guard
example : postAllocConventionsHOL (width := 1) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_1_2_if_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_tail_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_2_tail_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_2_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_2_tail_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_2_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_1_2_tail_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_1_2_return_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_1_2_return_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_1_2_return_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_1_2_return_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_handler_direct_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_2_handler_direct_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_2_handler_indirect_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_1_2_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_1_2_handler_indirect_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_must_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_0_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_loop_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_2_0_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_0_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_if_reg_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_0_if_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_if_imm_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_0_if_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_tail_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_0_tail_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_0_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_0_tail_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_0_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_0_tail_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_0_return_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_2_0_return_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_2_0_return_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_2_0_return_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_handler_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_0_handler_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_0_handler_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_0_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_0_handler_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_must_guard
example : postAllocConventionsHOL (width := 2) 8 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_1_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_loop_guard
example : postAllocConventionsHOL (width := 2) 8 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_2_1_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_seq_guard
example : postAllocConventionsHOL (width := 2) 8 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_1_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_if_reg_guard
example : postAllocConventionsHOL (width := 2) 8 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_1_if_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_if_imm_guard
example : postAllocConventionsHOL (width := 2) 8 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_1_if_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_tail_direct_guard
example : postAllocConventionsHOL (width := 2) 8 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_1_tail_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_1_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 8 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_1_tail_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_1_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 8 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_1_tail_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_1_return_direct_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_2_1_return_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_2_1_return_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_2_1_return_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_handler_direct_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_1_handler_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_1_handler_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_1_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_1_handler_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_must_guard
example : postAllocConventionsHOL (width := 2) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_2_must_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_loop_guard
example : postAllocConventionsHOL (width := 2) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_2_2_loop_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_seq_guard
example : postAllocConventionsHOL (width := 2) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_2_seq_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_if_reg_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_2_if_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_if_imm_guard
example : postAllocConventionsHOL (width := 2) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_2_2_if_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_tail_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_2_tail_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_2_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_2_tail_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_2_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_2_2_tail_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_2_2_return_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_2_2_return_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_2_2_return_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_2_2_return_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_handler_direct_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_2_handler_direct_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_2_handler_indirect_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_2_2_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_2_2_handler_indirect_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_must_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_0_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_loop_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_8_0_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_0_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_if_reg_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_0_if_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_if_imm_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_0_if_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_tail_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_0_tail_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_0_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_0_tail_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_0_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_0_tail_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_0_return_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_8_0_return_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_8_0_return_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_8_0_return_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_handler_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_0_handler_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_0_handler_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_0_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_0_handler_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_must_guard
example : postAllocConventionsHOL (width := 8) 8 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_1_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_loop_guard
example : postAllocConventionsHOL (width := 8) 8 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_8_1_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_seq_guard
example : postAllocConventionsHOL (width := 8) 8 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_1_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_if_reg_guard
example : postAllocConventionsHOL (width := 8) 8 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_1_if_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_if_imm_guard
example : postAllocConventionsHOL (width := 8) 8 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_1_if_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_tail_direct_guard
example : postAllocConventionsHOL (width := 8) 8 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_1_tail_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_1_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 8 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_1_tail_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_1_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 8 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_1_tail_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_1_return_direct_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_8_1_return_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_8_1_return_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_8_1_return_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_handler_direct_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_1_handler_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_1_handler_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_1_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_1_handler_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_must_guard
example : postAllocConventionsHOL (width := 8) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_2_must_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_loop_guard
example : postAllocConventionsHOL (width := 8) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_8_2_loop_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_seq_guard
example : postAllocConventionsHOL (width := 8) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_2_seq_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_if_reg_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_2_if_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_if_imm_guard
example : postAllocConventionsHOL (width := 8) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_8_2_if_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_tail_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_2_tail_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_2_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_2_tail_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_2_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_8_2_tail_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_8_2_return_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_8_2_return_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_8_2_return_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_8_2_return_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_handler_direct_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_2_handler_direct_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_2_handler_indirect_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_8_2_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_8_2_handler_indirect_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_must_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_0_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_loop_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_64_0_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_0_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_if_reg_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_0_if_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_if_imm_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_0_if_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_tail_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_0_tail_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_0_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_0_tail_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_0_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_0_tail_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_0_return_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_64_0_return_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_64_0_return_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_64_0_return_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_handler_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_0_handler_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_0_handler_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_0_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_0_handler_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_must_guard
example : postAllocConventionsHOL (width := 64) 8 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_1_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_loop_guard
example : postAllocConventionsHOL (width := 64) 8 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_64_1_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_seq_guard
example : postAllocConventionsHOL (width := 64) 8 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_1_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_if_reg_guard
example : postAllocConventionsHOL (width := 64) 8 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_1_if_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_if_imm_guard
example : postAllocConventionsHOL (width := 64) 8 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_1_if_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_tail_direct_guard
example : postAllocConventionsHOL (width := 64) 8 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_1_tail_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_1_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 8 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_1_tail_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_1_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 8 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_1_tail_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_1_return_direct_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_64_1_return_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_64_1_return_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_64_1_return_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_handler_direct_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_1_handler_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_1_handler_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_1_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_1_handler_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_must_guard
example : postAllocConventionsHOL (width := 64) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_2_must_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_loop_guard
example : postAllocConventionsHOL (width := 64) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_64_2_loop_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_seq_guard
example : postAllocConventionsHOL (width := 64) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_2_seq_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_if_reg_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_2_if_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_if_imm_guard
example : postAllocConventionsHOL (width := 64) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_64_2_if_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_tail_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_2_tail_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_2_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_2_tail_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_2_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_64_2_tail_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_64_2_return_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_64_2_return_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_64_2_return_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_64_2_return_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_handler_direct_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_2_handler_direct_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_2_handler_indirect_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_64_2_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_64_2_handler_indirect_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_must_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_0_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_loop_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_80_0_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_0_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_if_reg_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_0_if_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_if_imm_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_0_if_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_tail_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_0_tail_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_0_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_0_tail_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_0_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_0_tail_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_0_return_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_80_0_return_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_80_0_return_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_80_0_return_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_handler_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_0_handler_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_0_handler_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_0_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_0_handler_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_must_guard
example : postAllocConventionsHOL (width := 80) 8 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_1_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_loop_guard
example : postAllocConventionsHOL (width := 80) 8 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_80_1_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_seq_guard
example : postAllocConventionsHOL (width := 80) 8 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_1_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_if_reg_guard
example : postAllocConventionsHOL (width := 80) 8 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_1_if_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_if_imm_guard
example : postAllocConventionsHOL (width := 80) 8 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_1_if_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_tail_direct_guard
example : postAllocConventionsHOL (width := 80) 8 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_1_tail_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_1_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 8 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_1_tail_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_1_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 8 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_1_tail_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_1_return_direct_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_80_1_return_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_80_1_return_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_80_1_return_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_handler_direct_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_1_handler_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_1_handler_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_1_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 8 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_1_handler_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_must_guard
example : postAllocConventionsHOL (width := 80) 4 (.mustTerminate (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_2_must_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMustTerminate
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_loop_guard
example : postAllocConventionsHOL (width := 80) 4 (.loop .ln (.alloc 2 (.ln,.ln)) .ln) = true := by cbv

-- rbr_80_2_loop_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLoop
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_seq_guard
example : postAllocConventionsHOL (width := 80) 4 (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_2_seq_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSeq
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_if_reg_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_2_if_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 1180591620717411303424 (.reg 1180591620717411303424) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_if_imm_guard
example : postAllocConventionsHOL (width := 80) 4 (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) = true := by cbv

-- rbr_80_2_if_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.alloc 2 (.ln,.ln))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundIf
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_tail_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (some 123) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_2_tail_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (some 123) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_2_tail_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (none) [] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_2_tail_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_2_tail_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) = true := by cbv

-- rbr_80_2_tail_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call none (none) [0,2,4,6,8,10] (some (3,.raise 0,7,9))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallTail
  · cbv
  · cbv
  · rfl

-- rbr_80_2_return_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) = true := by cbv

-- rbr_80_2_return_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_return_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) = true := by cbv

-- rbr_80_2_return_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_return_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) = true := by cbv

-- rbr_80_2_return_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (none)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallReturn
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_handler_direct_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_2_handler_direct_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (some 123) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_handler_indirect_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_2_handler_indirect_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

-- rbr_80_2_handler_indirect_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) = true := by cbv

-- rbr_80_2_handler_indirect_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 2 (.ln,.ln),7,9)) (none) [2,4,6,8,10] (some (2,.alloc 2 (.ln,.ln),70,90))) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCallHandler
  · cbv
  · cbv
  · rfl
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain
  · intro bs frame conv room plain
    exact wordToStackRegBoundAlloc conf false 2 (.ln,.ln) bs frame conv room plain

end Flapjack.Test.WordToStackRegRecursiveParity
