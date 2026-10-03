import Flapjack.Compiler.Backend.WordInst

/-!
# `word_inst` replay of fresh original HOL evaluations

Each example replays one row of `scripts/hol-probes/word_inst_select_probe.out`
(fresh `EVAL` of the original `inst_select`/`three_to_two_reg_prog` at 64-bit
words) through the tagged `instSelect`/`threeToTwoRegProg`, by kernel reduction.
The HOL configuration leaves every `asm_config` field other than `valid_imm`,
`addr_offset`, `hw_offset` and `byte_offset` unspecified (`ARB with ...`), and
`inst_select` reads only those four; the Lean configuration fixes the same four
(signed `<=` is `toInt` order) and arbitrary values elsewhere.
-/

namespace Flapjack.Test.WordInstSelectExactParity

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordInst

abbrev P := WordLangProgHOL (BitVec 64)

def lo : BitVec 64 := -2048
def hi : BitVec 64 := 2047

/-- The four fields `inst_select` reads, as in the probe; the rest are arbitrary. -/
def cfg : AsmConfigExact 64 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 0
  linkReg := none
  avoidRegs := []
  regCount := 0
  fpRegCount := 0
  twoRegArith := false
  validImm := fun _ i => decide (lo.toInt ≤ i.toInt) && decide (i.toInt ≤ hi.toInt)
  addrOffset := (lo, hi)
  hwOffset := (lo, hi)
  byteOffset := (lo, hi)
  jumpOffset := (0, 0)
  cjumpOffset := (0, 0)
  locOffset := (0, 0)

-- add3
example : instSelect cfg 100 (.assign 5 (.op .add [.var 1, .const 3, .var 2]) : P) =
    .seq (.seq (.move 0 [(100, 2)]) (.seq (.move 0 [(101, 1)])
      (.inst (.arith (.binop .add 100 100 (.reg 101))))))
      (.inst (.arith (.binop .add 5 100 (.imm 3)))) := by
  with_unfolding_all rfl

-- sub_const
example : instSelect cfg 100 (.assign 5 (.op .sub [.var 1, .const 3]) : P) =
    .seq (.move 0 [(100, 1)]) (.inst (.arith (.binop .add 5 100 (.imm 0xFFFFFFFFFFFFFFFD)))) := by
  with_unfolding_all rfl

-- big_imm
example : instSelect cfg 100 (.assign 5 (.op .add [.var 1, .const 5000]) : P) =
    .seq (.move 0 [(100, 1)]) (.seq (.inst (.const 101 5000))
      (.inst (.arith (.binop .add 5 100 (.reg 101))))) := by
  with_unfolding_all rfl

-- store_off
example : instSelect cfg 100 (.store (.op .add [.var 1, .const 8]) 4 : P) =
    .seq (.move 0 [(100, 1)]) (.inst (.mem .store 4 (.addr 100 8))) := by
  with_unfolding_all rfl

-- load_off
example : instSelect cfg 100 (.assign 5 (.load (.op .add [.var 1, .const 16])) : P) =
    .seq (.move 0 [(100, 1)]) (.inst (.mem .load 5 (.addr 100 16))) := by
  with_unfolding_all rfl

-- shifts
example : instSelect cfg 100 (.seq (.assign 5 (.shift .lsl (.var 1) (.const 3)))
    (.seq (.assign 6 (.shift .lsr (.var 1) (.const 0)))
      (.assign 7 (.shift .asr (.var 1) (.const 64)))) : P) =
    .seq (.seq (.move 0 [(100, 1)]) (.inst (.arith (.shift .lsl 5 100 (.imm 3)))))
      (.seq (.seq (.move 0 [(100, 1)]) (.move 0 [(6, 100)])) (.inst (.const 7 0))) := by
  with_unfolding_all rfl

-- curr_heap
example : instSelect cfg 100 (.assign 5 (.op .add [.var 1, .lookup .currHeap]) : P) =
    .seq (.move 0 [(100, 1)]) (.opCurrHeap .add 5 100) := by
  with_unfolding_all rfl

-- share_load8
example : instSelect cfg 100 (.shareInst .load8 3 (.op .add [.var 1, .const 4]) : P) =
    .seq (.move 0 [(100, 1)]) (.shareInst .load8 3 (.op .add [.var 100, .const 4])) := by
  with_unfolding_all rfl

-- set_and
example : instSelect cfg 100
    (.set .globals (.op .and [.var 1, .op .and [.var 2, .const 255]]) : P) =
    .seq (.seq (.seq (.move 0 [(100, 2)]) (.seq (.move 0 [(101, 1)])
        (.inst (.arith (.binop .and 100 100 (.reg 101))))))
        (.inst (.arith (.binop .and 100 100 (.imm 255)))))
      (.set .globals (.var 100)) := by
  with_unfolding_all rfl

-- const_fold
example : instSelect cfg 100
    (.assign 5 (.op .xor [.const 3, .const 5, .op .sub [.const 9, .const 4]]) : P) =
    .inst (.const 5 3) := by
  with_unfolding_all rfl

-- two_reg
example : threeToTwoRegProg true (.seq (.inst (.arith (.binop .add 5 1 (.imm 3))))
    (.seq (.opCurrHeap .sub 6 2)
      (.ite .equal 1 (.imm 0) (.inst (.arith (.shift .lsl 7 8 (.imm 2)))) .skip)) : P) =
    .seq (.seq (.move 0 [(5, 1)]) (.inst (.arith (.binop .add 5 5 (.imm 3)))))
      (.seq (.seq (.move 0 [(6, 2)]) (.opCurrHeap .sub 6 6))
        (.ite .equal 1 (.imm 0)
          (.seq (.move 0 [(7, 8)]) (.inst (.arith (.shift .lsl 7 7 (.imm 2))))) .skip)) := by
  with_unfolding_all rfl

end Flapjack.Test.WordInstSelectExactParity
