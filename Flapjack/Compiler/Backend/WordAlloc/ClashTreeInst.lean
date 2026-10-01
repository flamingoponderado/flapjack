import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Backend.RegAlloc.ClashTree

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc
open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `get_delta_inst_def` (`word_allocScript.sml:1085-1119`), clause by
clause over the exact `HolInst` carrier and the literal `ClashTree` carrier.

`Skip` yields `Delta [] []`; `Const reg w` writes `reg`; `Binop`/`Shift` match
their `reg_imm` right operand, with a `Reg r3` adding `r3` to the reads and any
immediate (`Imm`) leaving only `r2`. `Div` writes `r1` and reads `r3;r2`;
`AddCarry` writes `r1;r4` and reads `r4;r3;r2`; `AddOverflow`/`SubOverflow`
write `r1;r4` and read `r3;r2`; `LongMul` writes `r1;r2` and reads `r4;r3`;
`LongDiv` writes `r1;r2` and reads `r5;r4;r3`. The six memory operations split
by direction: `Load`/`Load32`/`Load8` write the destination and read the address
base, while `Store`/`Store32`/`Store8` write nothing and read both the value
register and the address base (in that order). `FPLess`/`FPLessEqual`/`FPEqual`
write the integer result register. `FPMovToReg` writes `r1` only at width 64 and
`r1;r2` otherwise; `FPMovFromReg` reads `r1` only at width 64 and `r1;r2`
otherwise. HOL's `dimindex(:'a) = 64` test is rendered as `width = 64`, which is
the `dimindex` of the positive-width Lean `BitVec width` carrier. The final HOL
catchall returns `Delta [] []`, so every unlisted instruction (`FPMovToReg`'s
sibling `FP` operations such as `FPNeg`/`FPAdd`, `Load16`, etc.) falls through to
the empty delta.

This proof-side port does not replace the executed caller yet. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_delta_inst_def"
  (words_as_type_indexed_bitvec)]
def getDeltaInst {width : Nat} [NeZero width] : HolInst width → ClashTree
  | .skip => .delta [] []
  | .const reg _ => .delta [reg] []
  | .arith (.binop _ r1 r2 (.reg r3)) => .delta [r1] [r2, r3]
  | .arith (.binop _ r1 r2 (.imm _)) => .delta [r1] [r2]
  | .arith (.shift _ r1 r2 (.reg r3)) => .delta [r1] [r2, r3]
  | .arith (.shift _ r1 r2 (.imm _)) => .delta [r1] [r2]
  | .arith (.div r1 r2 r3) => .delta [r1] [r3, r2]
  | .arith (.addCarry r1 r2 r3 r4) => .delta [r1, r4] [r4, r3, r2]
  | .arith (.addOverflow r1 r2 r3 r4) => .delta [r1, r4] [r3, r2]
  | .arith (.subOverflow r1 r2 r3 r4) => .delta [r1, r4] [r3, r2]
  | .arith (.longMul r1 r2 r3 r4) => .delta [r1, r2] [r4, r3]
  | .arith (.longDiv r1 r2 r3 r4 r5) => .delta [r1, r2] [r5, r4, r3]
  | .mem .load r (.addr a _) => .delta [r] [a]
  | .mem .store r (.addr a _) => .delta [] [r, a]
  | .mem .load32 r (.addr a _) => .delta [r] [a]
  | .mem .store32 r (.addr a _) => .delta [] [r, a]
  | .mem .load8 r (.addr a _) => .delta [r] [a]
  | .mem .store8 r (.addr a _) => .delta [] [r, a]
  | .fp (.fpLess r _ _) => .delta [r] []
  | .fp (.fpLessEqual r _ _) => .delta [r] []
  | .fp (.fpEqual r _ _) => .delta [r] []
  | .fp (.fpMovToReg r1 r2 _) =>
      if width = 64 then .delta [r1] [] else .delta [r1, r2] []
  | .fp (.fpMovFromReg _ r1 r2) =>
      if width = 64 then .delta [] [r1] else .delta [] [r1, r2]
  | _ => .delta [] []

end Flapjack.WordAlloc
