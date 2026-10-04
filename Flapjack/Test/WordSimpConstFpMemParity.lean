import Flapjack.RiscV.WordSimp

/-! Original HOL `const_fp` rows captured in
`scripts/hol-probes/word_simp_const_fp_mem_probe.out`: through
`const_fp_inst_cs_def` only `Load`/`Load8`/`Load32` forget their destination,
so after a store or a sixteen-bit operation the known `2 := 7` still folds
`Var 2 + 3` to `10`. Each row compares the executed `wordConstFpLoop` from
empty knowledge (HOL `const_fp p = FST (const_fp_loop p LN)`) with that output. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Flapjack.Test.WordSimpConstFpMemParity
open Flapjack RiscV

private def input (op : WordMemOp) : WordProg (BitVec 64) :=
  .seq (.assign 2 (.const 7))
    (.seq (.inst (.mem op 2 3)) (.assign 4 (.op .add [.var 2, .const 3])))

/-- HOL kept the constant: the final assignment folded to `Const 10w`. -/
private def folded (op : WordMemOp) : Bool :=
  match (wordConstFpLoop (input op) []).1 with
  | .seq (.assign 2 (.const 7)) (.seq (.inst (.mem op' 2 3)) (.assign 4 (.const 10))) =>
      op' == op
  | _ => false

/-- HOL forgot the constant: the final assignment is unchanged. -/
private def unfolded (op : WordMemOp) : Bool :=
  match (wordConstFpLoop (input op) []).1 with
  | .seq (.assign 2 (.const 7))
      (.seq (.inst (.mem op' 2 3)) (.assign 4 (.op .add [.var 2, .const 3]))) => op' == op
  | _ => false

-- mem_store, mem_store8, mem_store16, mem_store32, mem_load16
example : [folded .store, folded .store8, folded .store16, folded .store32,
    folded .load16] = List.replicate 5 true := by decide +kernel
-- mem_load, mem_load8, mem_load32
example : [unfolded .load, unfolded .load8, unfolded .load32] =
    List.replicate 3 true := by decide +kernel

end Flapjack.Test.WordSimpConstFpMemParity
