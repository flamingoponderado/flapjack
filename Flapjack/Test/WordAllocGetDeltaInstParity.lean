import Flapjack.Compiler.Backend.WordAlloc.ClashTreeInst

namespace Flapjack.Test.WordAllocGetDeltaInstParity

open Flapjack.WordAlloc
open Flapjack.RegAlloc
open Flapjack.Compiler.Encoders.Asm

/-! Direct original HOL rows replaying every probe row in
`scripts/hol-probes/word_alloc_get_delta_inst_probe.out`. These are regression
observations over the exact positive-width `HolInst` carrier and the literal
`ClashTree` carrier, not an independent cross-language equivalence theorem. -/

-- gdi_skip=T
example : getDeltaInst (.skip : HolInst 8) = .delta [] [] := by decide +kernel

-- gdi_const=T
example : getDeltaInst (.const 1 (7 : BitVec 8)) = .delta [1] [] := by decide +kernel

-- gdi_binop_reg=T
example : getDeltaInst (.arith (.binop .add 1 2 (.reg 3)) : HolInst 8) =
    .delta [1] [2, 3] := by decide +kernel

-- gdi_binop_imm=T
example : getDeltaInst (.arith (.binop .add 1 2 (.imm (7 : BitVec 8))) : HolInst 8) =
    .delta [1] [2] := by decide +kernel

-- gdi_shift_reg=T
example : getDeltaInst (.arith (.shift .lsl 1 2 (.reg 3)) : HolInst 8) =
    .delta [1] [2, 3] := by decide +kernel

-- gdi_shift_imm=T
example : getDeltaInst (.arith (.shift .lsl 1 2 (.imm (7 : BitVec 8))) : HolInst 8) =
    .delta [1] [2] := by decide +kernel

-- gdi_div=T
example : getDeltaInst (.arith (.div 1 2 3) : HolInst 8) =
    .delta [1] [3, 2] := by decide +kernel

-- gdi_addcarry=T
example : getDeltaInst (.arith (.addCarry 1 2 3 4) : HolInst 8) =
    .delta [1, 4] [4, 3, 2] := by decide +kernel

-- gdi_addoverflow=T
example : getDeltaInst (.arith (.addOverflow 1 2 3 4) : HolInst 8) =
    .delta [1, 4] [3, 2] := by decide +kernel

-- gdi_suboverflow=T
example : getDeltaInst (.arith (.subOverflow 1 2 3 4) : HolInst 8) =
    .delta [1, 4] [3, 2] := by decide +kernel

-- gdi_longmul=T
example : getDeltaInst (.arith (.longMul 1 2 3 4) : HolInst 8) =
    .delta [1, 2] [4, 3] := by decide +kernel

-- gdi_longdiv=T
example : getDeltaInst (.arith (.longDiv 1 2 3 4 5) : HolInst 8) =
    .delta [1, 2] [5, 4, 3] := by decide +kernel

-- gdi_load=T
example : getDeltaInst (.mem .load 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [1] [2] := by decide +kernel

-- gdi_store=T
example : getDeltaInst (.mem .store 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [] [1, 2] := by decide +kernel

-- gdi_load32=T
example : getDeltaInst (.mem .load32 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [1] [2] := by decide +kernel

-- gdi_store32=T
example : getDeltaInst (.mem .store32 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [] [1, 2] := by decide +kernel

-- gdi_load8=T
example : getDeltaInst (.mem .load8 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [1] [2] := by decide +kernel

-- gdi_store8=T
example : getDeltaInst (.mem .store8 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
    .delta [] [1, 2] := by decide +kernel

-- gdi_fpless=T
example : getDeltaInst (.fp (.fpLess 1 2 3) : HolInst 8) =
    .delta [1] [] := by decide +kernel

-- gdi_fpmovtoreg64=T
example : getDeltaInst (.fp (.fpMovToReg 1 2 3) : HolInst 64) =
    .delta [1] [] := by decide +kernel

-- gdi_fpmovtoreg32=T
example : getDeltaInst (.fp (.fpMovToReg 1 2 3) : HolInst 32) =
    .delta [1, 2] [] := by decide +kernel

-- gdi_fpmovfromreg64=T
example : getDeltaInst (.fp (.fpMovFromReg 3 1 2) : HolInst 64) =
    .delta [] [1] := by decide +kernel

-- gdi_fpmovfromreg32=T
example : getDeltaInst (.fp (.fpMovFromReg 3 1 2) : HolInst 32) =
    .delta [] [1, 2] := by decide +kernel

-- gdi_fpneg_catchall=T
example : getDeltaInst (.fp (.fpNeg 1 2) : HolInst 8) =
    .delta [] [] := by decide +kernel

/-- Runtime PASS lines mirroring `CompilerParity`'s other parity registrations;
the same propositions are already kernel-checked above. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("getDeltaInst Skip", decide (getDeltaInst (.skip : HolInst 8) = .delta [] [])),
      ("getDeltaInst Const",
        decide (getDeltaInst (.const 1 (7 : BitVec 8)) = .delta [1] [])),
      ("getDeltaInst Binop Reg",
        decide (getDeltaInst (.arith (.binop .add 1 2 (.reg 3)) : HolInst 8) =
          .delta [1] [2, 3])),
      ("getDeltaInst Binop Imm",
        decide (getDeltaInst (.arith (.binop .add 1 2 (.imm (7 : BitVec 8))) : HolInst 8) =
          .delta [1] [2])),
      ("getDeltaInst Shift Reg",
        decide (getDeltaInst (.arith (.shift .lsl 1 2 (.reg 3)) : HolInst 8) =
          .delta [1] [2, 3])),
      ("getDeltaInst Shift Imm",
        decide (getDeltaInst (.arith (.shift .lsl 1 2 (.imm (7 : BitVec 8))) : HolInst 8) =
          .delta [1] [2])),
      ("getDeltaInst Div",
        decide (getDeltaInst (.arith (.div 1 2 3) : HolInst 8) = .delta [1] [3, 2])),
      ("getDeltaInst AddCarry",
        decide (getDeltaInst (.arith (.addCarry 1 2 3 4) : HolInst 8) =
          .delta [1, 4] [4, 3, 2])),
      ("getDeltaInst AddOverflow",
        decide (getDeltaInst (.arith (.addOverflow 1 2 3 4) : HolInst 8) =
          .delta [1, 4] [3, 2])),
      ("getDeltaInst SubOverflow",
        decide (getDeltaInst (.arith (.subOverflow 1 2 3 4) : HolInst 8) =
          .delta [1, 4] [3, 2])),
      ("getDeltaInst LongMul",
        decide (getDeltaInst (.arith (.longMul 1 2 3 4) : HolInst 8) =
          .delta [1, 2] [4, 3])),
      ("getDeltaInst LongDiv",
        decide (getDeltaInst (.arith (.longDiv 1 2 3 4 5) : HolInst 8) =
          .delta [1, 2] [5, 4, 3])),
      ("getDeltaInst Load",
        decide (getDeltaInst (.mem .load 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [1] [2])),
      ("getDeltaInst Store",
        decide (getDeltaInst (.mem .store 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [] [1, 2])),
      ("getDeltaInst Load32",
        decide (getDeltaInst (.mem .load32 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [1] [2])),
      ("getDeltaInst Store32",
        decide (getDeltaInst (.mem .store32 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [] [1, 2])),
      ("getDeltaInst Load8",
        decide (getDeltaInst (.mem .load8 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [1] [2])),
      ("getDeltaInst Store8",
        decide (getDeltaInst (.mem .store8 1 (.addr 2 (0 : BitVec 8)) : HolInst 8) =
          .delta [] [1, 2])),
      ("getDeltaInst FPLess",
        decide (getDeltaInst (.fp (.fpLess 1 2 3) : HolInst 8) = .delta [1] [])),
      ("getDeltaInst FPMovToReg 64",
        decide (getDeltaInst (.fp (.fpMovToReg 1 2 3) : HolInst 64) = .delta [1] [])),
      ("getDeltaInst FPMovToReg 32",
        decide (getDeltaInst (.fp (.fpMovToReg 1 2 3) : HolInst 32) = .delta [1, 2] [])),
      ("getDeltaInst FPMovFromReg 64",
        decide (getDeltaInst (.fp (.fpMovFromReg 3 1 2) : HolInst 64) = .delta [] [1])),
      ("getDeltaInst FPMovFromReg 32",
        decide (getDeltaInst (.fp (.fpMovFromReg 3 1 2) : HolInst 32) = .delta [] [1, 2])),
      ("getDeltaInst FPNeg catchall",
        decide (getDeltaInst (.fp (.fpNeg 1 2) : HolInst 8) = .delta [] [])) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.WordAllocGetDeltaInstParity
