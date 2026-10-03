import Flapjack.Compiler.Backend.WordSimp

/-!
# `word_simp$compile_exp` replay of fresh original HOL evaluations

Each example replays one row of `scripts/hol-probes/word_simp_compile_exp_probe.out`
(fresh `EVAL` of the original `word_simp$compile_exp` at 64-bit words) through the
tagged `compileExp`, by kernel reduction.  The rows exercise constant folding,
`drop_consts` before `Call`/`FFI`/`Alloc`/`Install`, static `If` selection,
`push_out_if`, the `simp_duplicate_if` hoist, shift folding, `Move` constant
propagation, `Loop` resets, `ShareInst` addresses and a returning call.
-/

namespace Flapjack.Test.WordSimpCompileExpParity

open Flapjack Flapjack.Compiler.Backend.WordSimp

abbrev P := WordLangProgHOL (BitVec 64)

-- fold_chain=Seq (Seq (Assign 1 (Const 5w)) (Assign 2 (Const 9w))) (Assign 3 (Const 9w))
example : compileExp (.seq (.assign 1 (.const 5))
    (.seq (.assign 2 (.op .add [.var 1, .const 4])) (.assign 3 (.var 2))) : P) =
    .seq (.seq (.assign 1 (.const 5)) (.assign 2 (.const 9))) (.assign 3 (.const 9)) := by
  with_unfolding_all rfl

-- call_drop_consts=Seq (Seq (Assign 2 (Const 7w)) (Assign 6 (Const 5w)))
--   (Seq (Seq (Assign 6 (Const 5w)) (Assign 2 (Const 7w))) (Call NONE (SOME 10) [2; 6] NONE))
example : compileExp (.seq (.assign 2 (.const 7))
    (.seq (.assign 6 (.const 5)) (.call none (some 10) [2, 6] none)) : P) =
    .seq (.seq (.assign 2 (.const 7)) (.assign 6 (.const 5)))
      (.seq (.seq (.assign 6 (.const 5)) (.assign 2 (.const 7)))
        (.call none (some 10) [2, 6] none)) := by
  with_unfolding_all rfl

-- static_if=Seq (Assign 1 (Const 0w)) (Assign 2 (Const 3w))
example : compileExp (.seq (.assign 1 (.const 0))
    (.ite .equal 1 (.imm 0) (.assign 2 (.const 3)) (.assign 2 (.const 4))) : P) =
    .seq (.assign 1 (.const 0)) (.assign 2 (.const 3)) := by
  with_unfolding_all rfl

-- push_out_if=Seq (If Equal 1 (Imm 0w) (Return 0 [1]) Skip) (Assign 2 (Const 3w))
example : compileExp (.ite .equal 1 (.imm 0) (.return 0 [1]) (.assign 2 (.const 3)) : P) =
    .seq (.ite .equal 1 (.imm 0) (.return 0 [1]) .skip) (.assign 2 (.const 3)) := by
  with_unfolding_all rfl

-- hoist_if=If Lower 1 (Reg 2)
--   (Seq (Seq (Assign 5 (Const 1w)) (Assign 7 (Var 3))) (Assign 8 (Const 9w)))
--   (Seq (Seq (Assign 5 (Const 2w)) (Assign 7 (Var 3))) (Assign 8 (Const 10w)))
example : compileExp (.seq (.ite .lower 1 (.reg 2) (.assign 5 (.const 1)) (.assign 5 (.const 2)))
    (.seq (.assign 7 (.var 3))
      (.ite .equal 5 (.imm 1) (.assign 8 (.const 9)) (.assign 8 (.const 10)))) : P) =
    .ite .lower 1 (.reg 2)
      (.seq (.seq (.assign 5 (.const 1)) (.assign 7 (.var 3))) (.assign 8 (.const 9)))
      (.seq (.seq (.assign 5 (.const 2)) (.assign 7 (.var 3))) (.assign 8 (.const 10))) := by
  with_unfolding_all rfl

-- shift_move_loop=Seq (Seq (Seq (Assign 1 (Const 8w)) (Move 0 [(4,1); (5,9)]))
--   (Loop ⦕ 4 ⦖ (Assign 6 (Var 4)) LN)) (Assign 7 (Op Sub [Var 4; Var 1]))
example : compileExp (.seq (.assign 1 (.shift .lsl (.const 1) (.const 3)))
    (.seq (.move 0 [(4, 1), (5, 9)])
      (.seq (.loop (sptInsert 4 () .ln) (.assign 6 (.var 4)) .ln)
        (.assign 7 (.op .sub [.var 4, .var 1])))) : P) =
    .seq (.seq (.seq (.assign 1 (.const 8)) (.move 0 [(4, 1), (5, 9)]))
      (.loop (sptInsert 4 () .ln) (.assign 6 (.var 4)) .ln))
      (.assign 7 (.op .sub [.var 4, .var 1])) := by
  with_unfolding_all rfl

-- ffi_install_share=Seq (Seq (Seq (Assign 2 (Const 8w))
--   (Seq (Assign 2 (Const 8w)) (FFI «f» 2 3 4 5 (⦕ 2 ⦖,LN)))) (ShareInst Load 3 (Const 9w)))
--   (Seq (Assign 2 (Const 8w)) (Install 2 3 4 5 (⦕ 2 ⦖,LN)))
example : compileExp (.seq (.assign 2 (.const 8))
    (.seq (.ffi (.implode [0x66]) 2 3 4 5 (sptInsert 2 () .ln, .ln))
      (.seq (.shareInst .load 3 (.op .add [.var 2, .const 1]))
        (.install 2 3 4 5 (sptInsert 2 () .ln, .ln)))) : P) =
    .seq (.seq (.seq (.assign 2 (.const 8))
        (.seq (.assign 2 (.const 8)) (.ffi (.implode [0x66]) 2 3 4 5 (sptInsert 2 () .ln, .ln))))
        (.shareInst .load 3 (.const 9)))
      (.seq (.assign 2 (.const 8)) (.install 2 3 4 5 (sptInsert 2 () .ln, .ln))) := by
  with_unfolding_all rfl

-- inst_alloc_ret_call=Seq (Seq (Seq (Assign 2 (Const 6w)) (Inst (Const 3 4w)))
--   (Seq (Assign 2 (Const 6w)) (Alloc 2 (⦕ 2 ⦖,LN))))
--   (Call (SOME ([1],(⦕ 3 ⦖,LN),Assign 9 (Var 3),5,6)) (SOME 11) [3] NONE)
example : compileExp (.seq (.assign 2 (.const 6))
    (.seq (.inst (.const 3 4))
      (.seq (.alloc 2 (sptInsert 2 () .ln, .ln))
        (.call (some ([1], (sptInsert 3 () .ln, .ln), .assign 9 (.var 3), 5, 6))
          (some 11) [3] none))) : P) =
    .seq (.seq (.seq (.assign 2 (.const 6)) (.inst (.const 3 4)))
        (.seq (.assign 2 (.const 6)) (.alloc 2 (sptInsert 2 () .ln, .ln))))
      (.call (some ([1], (sptInsert 3 () .ln, .ln), .assign 9 (.var 3), 5, 6))
        (some 11) [3] none) := by
  with_unfolding_all rfl

end Flapjack.Test.WordSimpCompileExpParity
