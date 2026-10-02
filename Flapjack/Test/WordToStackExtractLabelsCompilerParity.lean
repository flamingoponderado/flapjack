import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsCompiler

/-! Independent complete original comp/list/top label projections.
Generic theorem applications and axiom audits are separate from captured outputs.
These regressions do not establish HOL-to-Lean equivalence. -/
namespace Flapjack.Test.WordToStackExtractLabelsCompilerParity
open Flapjack Flapjack.Compiler.Backend StackLang
open Flapjack.Compiler.Encoders.Asm
open WordToStack.Native WordToStack.Native.ExtractLabelsCompiler

-- elc_1_0_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_0_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_0_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_0_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_0_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_0_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_0_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_1_0_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_1_0_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_1_0_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_0_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_0_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_1_0_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_1_0_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_0_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_0_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_0_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_0_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_1_0_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_1_0_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_1_0_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_1_0_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_1_0_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_1_0_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_0_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_0_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_1_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_1_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_1_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_1_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_1_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_1_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_1_1_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_1_1_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_1_1_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_1_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_1_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_1_1_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_1_1_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_1_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_1_1_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_1_1_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_1_1_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_1_1_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_1_1_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_1_1_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_1_1_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_1_1_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_1_1_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_1_1_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_1_1_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 1) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_0_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_0_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_0_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_0_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_0_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_0_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_8_0_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_8_0_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_8_0_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_0_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_0_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_8_0_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_8_0_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_0_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_0_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_0_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_0_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_8_0_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_8_0_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_8_0_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_8_0_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_8_0_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_8_0_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_0_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_0_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_1_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_1_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_1_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_1_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_1_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_1_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_8_1_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_8_1_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_8_1_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_1_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_1_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_8_1_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_8_1_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_1_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_8_1_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_8_1_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_8_1_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_8_1_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_8_1_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_8_1_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_8_1_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_8_1_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_8_1_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_8_1_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_8_1_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 8) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_0_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_0_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_0_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_0_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_0_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_0_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_64_0_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_64_0_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_64_0_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_0_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_0_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_64_0_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_64_0_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_0_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_0_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_0_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_0_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_64_0_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_64_0_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_64_0_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_64_0_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_64_0_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_64_0_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_0_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_0_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_1_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_1_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_1_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_1_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_1_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_1_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_64_1_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_64_1_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_64_1_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_1_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_1_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_64_1_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_64_1_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_1_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_64_1_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_64_1_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_64_1_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_64_1_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_64_1_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_64_1_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_64_1_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_64_1_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_64_1_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_64_1_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_64_1_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 64) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_0_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_0_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_0_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_0_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_0_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_0_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_80_0_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_80_0_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_80_0_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_0_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_0_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_80_0_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_80_0_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_0_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_0_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_0_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_0_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_80_0_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_80_0_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_80_0_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_80_0_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_80_0_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_80_0_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_0_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_0_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) false [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_skip_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.skip) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_1_skip_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.skip),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_1_skip_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.skip),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_1_inst_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.inst (.const 1180591620717411303424 7)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_1_inst_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_1_inst_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.inst (.const 1180591620717411303424 7)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_1_return_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2)] := by
  cbv

-- elc_80_1_return_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2)]), (7,[])] := by
  cbv

-- elc_80_1_return_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2)]), (7,[])] := by
  cbv

-- elc_80_1_both_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_1_both_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_both_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_must_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_1_must_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_must_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.mustTerminate (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_seq_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2), (7,3)] := by
  cbv

-- elc_80_1_seq_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_seq_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_if_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.ite .equal 1180591620717411303424 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3), (7,2)] := by
  cbv

-- elc_80_1_if_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_if_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.ite .equal 2 (.imm 7) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_loop_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_1_loop_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_loop_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.loop .ln (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3))) .ln),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_tail_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [] := by
  cbv

-- elc_80_1_tail_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[]), (7,[])] := by
  cbv

-- elc_80_1_tail_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call none none [2,1180591620717411303424] (some (99,.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,3))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[]), (7,[])] := by
  cbv

-- elc_80_1_nested_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,4), (7,5), (7,2), (7,3), (7,2)] := by
  cbv

-- elc_80_1_nested_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_nested_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)),7,4)) none [] (some (99,.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none,7,5))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,4), (7,5), (7,2), (7,3), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_duplicates_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,2)] := by
  cbv

-- elc_80_1_duplicates_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_duplicates_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none) (.call (some ([],(.ln,.ln),.tick,7,2)) (some 9) [] none)),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,2)]), (7,[])] := by
  cbv

-- elc_80_1_wide_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(1180591620717411303424,1180591620717411303425)] := by
  cbv

-- elc_80_1_wide_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_80_1_wide_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.call (some ([],(.ln,.ln),.tick,1180591620717411303424,1180591620717411303425)) (some 9) [] none),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(1180591620717411303424,1180591620717411303425)]), (7,[])] := by
  cbv

-- elc_80_1_bitmaps_comp: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : StackProps.extractLabels (compNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true (.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))) (.append (.list [8]) (.list [2]),99) (4,8,7)).1 = [(7,2), (7,3)] := by
  cbv

-- elc_80_1_bitmaps_list: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileWordToStackNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true 4 [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)] (.append (.list [8]) (.list [2]),99)).1.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(7,[(7,2), (7,3)]), (7,[])] := by
  cbv

-- elc_80_1_bitmaps_top: independently evaluated original ordered labels.
example (c : AsmConfigExact 80) : (compileNative ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => true }) true [(7,3,.seq (.alloc 99 (.ln,sptInsert 32 () .ln)) (.call (some ([2,4,6],(.ln,.ln),.tick,7,2)) none [2,40] (some (99,.tick,7,3)))),(7,0,.tick)]).2.2.2.map (fun row => (row.1,StackProps.extractLabels row.2)) = [(5,[]), (6,[]), (7,[(7,2), (7,3)]), (7,[])] := by
  cbv

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (perf : Bool) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    Flapjack.extractLabels p = StackProps.extractLabels (compNative c perf p bs frame).1 :=
  wordToStackLabPres c perf p bs frame

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (perf : Bool) (k : Nat)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat)
    (source : ∀ row ∈ rows,
      (∀ label ∈ Flapjack.extractLabels row.2.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (Flapjack.extractLabels row.2.2).Nodup) :
    ∀ row ∈ (compileWordToStackNative c perf k rows bs).1,
      (∀ label ∈ StackProps.extractLabels row.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (StackProps.extractLabels row.2).Nodup :=
  compileWordToStackLabPres c perf k rows bs _ _ rfl source

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (source : ∀ row ∈ rows,
      (∀ label ∈ Flapjack.extractLabels row.2.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (Flapjack.extractLabels row.2.2).Nodup) :
    let output := (compileNative c false rows).2.2.2
    output.map Prod.fst = raiseStubLocation :: storeConstsStubLocation :: rows.map Prod.fst ∧
    ∀ row ∈ output,
      (∀ label ∈ StackProps.extractLabels row.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (StackProps.extractLabels row.2).Nodup :=
  wordToStackCompileLabPres c rows source

#print axioms wordToStackLabPres
#print axioms compileWordToStackLabPres
#print axioms wordToStackCompileLabPres

def runChecks : IO Bool := do
  IO.println "PASS original ordered compiler labels (312 kernel output rows, three full theorem applications)"
  pure true
end Flapjack.Test.WordToStackExtractLabelsCompilerParity
