module

public import Flapjack.Pancake.WordConvs

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# `wordConvs$inst_ok_less` Lean regression

Kernel-checked observations of the reviewed exact `inst_ok_less` port
(`instOkLessExact`, tagged `inst_ok_less_def`) at the 8-bit word width, applied
through `AsmConfig.toExact` and the native instruction codec
`HolInst.ofWordLangInst`, matching the direct HOL fixture
`scripts/hol-probes/word_convs_inst_ok_less_probe.out` row for row.
`inst_ok_less` is the weaker per-instruction well-formedness predicate consumed
by `compile_to_word_conventions2`; unlike `asm$inst_ok` it omits
operand-register checks.

Reference: `cakeml/compiler/backend/semantics/wordConvsScript.sml:208-249`.
-/

namespace Flapjack.Test.WordLangInstOkLessParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def cfg : AsmConfig 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := [3]
  regCount := 8
  fpRegCount := 4
  twoRegArith := true
  validImm := fun _ value => value == w8 1
  addrOffset := (w8 0, w8 100)
  hwOffset := (w8 0, w8 100)
  byteOffset := (w8 0, w8 100)
  jumpOffset := (w8 0, w8 100)
  cjumpOffset := (w8 0, w8 100)
  locOffset := (w8 0, w8 100)

/-- The reviewed exact `inst_ok_less` port read through the production
configuration and the native instruction codec, at the probe's 8-bit width. -/
private def instOkLessExactAt (i : WordLangInst W) : Bool :=
  instOkLessExact cfg.toExact (HolInst.ofWordLangInst i)

example : instOkLessExactAt (.arith (.binop .add 0 0 (.imm (w8 1)))) = true := by decide
example : instOkLessExactAt (.arith (.binop .add 0 0 (.imm (w8 2)))) = false := by decide
example : instOkLessExactAt (.arith (.binop .add 0 0 (.reg 5))) = true := by decide
example : instOkLessExactAt (.arith (.shift .lsl 0 0 (.imm (w8 0)))) = true := by decide
example : instOkLessExactAt (.arith (.shift .lsr 0 0 (.imm (w8 0)))) = false := by decide
example : instOkLessExactAt (.arith (.shift .lsl 0 0 (.imm (w8 8)))) = false := by decide
example : instOkLessExactAt (.arith (.div 0 1 2)) = true := by decide
example : instOkLessExactAt (.arith (.longMul 0 1 0 2)) = false := by decide
example : instOkLessExactAt (.arith (.longDiv 0 1 2 3 4)) = false := by decide
example : instOkLessExactAt (.arith (.addCarry 0 1 2 3)) = true := by decide
example : instOkLessExactAt (.arith (.addCarry 0 1 0 3)) = false := by decide
example : instOkLessExactAt (.arith (.addOverflow 0 1 0 3)) = false := by decide
example : instOkLessExactAt (.arith (.subOverflow 0 1 0 3)) = false := by decide
example : instOkLessExactAt (.mem .load 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLessExactAt (.mem .load8 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLessExactAt (.mem .load16 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLessExactAt .skip = true := by decide
example : instOkLessExactAt (.const 0 (w8 0)) = true := by decide
example : instOkLessExactAt (.fp (.fpLess 0 1 2)) = true := by decide
example : instOkLessExactAt (.fp (.fpLess 0 1 5)) = false := by decide
example : instOkLessExactAt (.fp (.fpFma 0 1 2)) = false := by decide
example : instOkLessExactAt (.fp (.fpMovToReg 1 1 0)) = true := by decide
example : instOkLessExactAt (.fp (.fpMovToReg 1 2 9)) = false := by decide
example : instOkLessExactAt (.fp (.fpMovFromReg 9 1 2)) = false := by decide

private def guards : List Bool :=
  [ instOkLessExactAt (.arith (.binop .add 0 0 (.imm (w8 1))))
  , instOkLessExactAt (.arith (.binop .add 0 0 (.imm (w8 2))))
  , instOkLessExactAt (.arith (.binop .add 0 0 (.reg 5)))
  , instOkLessExactAt (.arith (.shift .lsl 0 0 (.imm (w8 0))))
  , instOkLessExactAt (.arith (.shift .lsr 0 0 (.imm (w8 0))))
  , instOkLessExactAt (.arith (.shift .lsl 0 0 (.imm (w8 8))))
  , instOkLessExactAt (.arith (.div 0 1 2))
  , instOkLessExactAt (.arith (.longMul 0 1 0 2))
  , instOkLessExactAt (.arith (.longDiv 0 1 2 3 4))
  , instOkLessExactAt (.arith (.addCarry 0 1 2 3))
  , instOkLessExactAt (.arith (.addCarry 0 1 0 3))
  , instOkLessExactAt (.arith (.addOverflow 0 1 0 3))
  , instOkLessExactAt (.arith (.subOverflow 0 1 0 3))
  , instOkLessExactAt (.mem .load 0 (.addr 0 (w8 1)))
  , instOkLessExactAt (.mem .load8 0 (.addr 0 (w8 1)))
  , instOkLessExactAt (.mem .load16 0 (.addr 0 (w8 1)))
  , instOkLessExactAt .skip
  , instOkLessExactAt (.const 0 (w8 0))
  , instOkLessExactAt (.fp (.fpLess 0 1 2))
  , instOkLessExactAt (.fp (.fpLess 0 1 5))
  , instOkLessExactAt (.fp (.fpFma 0 1 2))
  , instOkLessExactAt (.fp (.fpMovToReg 1 1 0))
  , instOkLessExactAt (.fp (.fpMovToReg 1 2 9))
  , instOkLessExactAt (.fp (.fpMovFromReg 9 1 2)) ]

private def expected : List Bool :=
  [ true, false, true, true, false, false, true, false, false, true, false,
    false, false, true, true, true, true, true, true, false, false, true,
    false, false ]

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS wordConvs inst_ok_less matches all 24 oracle rows"
  else
    IO.println "FAIL wordConvs inst_ok_less oracle rows"
  pure (guards == expected)

end Flapjack.Test.WordLangInstOkLessParity
