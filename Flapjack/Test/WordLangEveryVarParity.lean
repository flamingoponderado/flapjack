import Flapjack.Pancake.WordLang

namespace Flapjack.Test.WordLangEveryVarParity

open Flapjack

private abbrev W := BitVec 8

private def even (n : Nat) : Bool := n % 2 = 0

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def eVar : WordLangExp W := .var 2
private def eVarOdd : WordLangExp W := .var 3
private def eConst : WordLangExp W := .const (w8 0)
private def eLoad : WordLangExp W := .load (.var 4)
private def eOpOk : WordLangExp W := .op .add [.var 2, .var 4]
private def eOpBad : WordLangExp W := .op .add [.var 2, .var 3]
private def eShiftBad : WordLangExp W := .shift .lsl (.var 2) (.var 3)
private def eLookup : WordLangExp W := .lookup .nextFree

private def iRegOk : WordRegImm W := .reg 4
private def iRegBad : WordRegImm W := .reg 3
private def iImm : WordRegImm W := .imm (w8 0)

private def vConstOk : WordLangInst W := .const 2 (w8 0)
private def vBinopOk : WordLangInst W := .arith (.binop .add 2 4 (.reg 4))
private def vBinopBad : WordLangInst W := .arith (.binop .add 2 3 (.reg 4))
private def vShiftOk : WordLangInst W := .arith (.shift .lsl 2 4 (.imm (w8 0)))
private def vDivOk : WordLangInst W := .arith (.div 2 4 6)
private def vAddCarryBad : WordLangInst W := .arith (.addCarry 2 4 6 3)
private def vLongDivOk : WordLangInst W := .arith (.longDiv 2 4 6 8 0)
private def vMemLoadOk : WordLangInst W := .mem .load 2 (.addr 4 0)
private def vMemLoadBad : WordLangInst W := .mem .load 3 (.addr 4 0)
private def vMemLoad8Ok : WordLangInst W := .mem .load8 2 (.addr 4 0)
private def vMemLoad16 : WordLangInst W := .mem .load16 3 (.addr 4 0)
private def vSkip : WordLangInst W := .skip

example : everyVarExp even eVar = true := by decide
example : everyVarExp even eVarOdd = false := by decide
example : everyVarExp even eConst = true := by decide
example : everyVarExp even eLoad = true := by decide
example : everyVarExp even eOpOk = true := by decide
example : everyVarExp even eOpBad = false := by decide
example : everyVarExp even eShiftBad = false := by decide
example : everyVarExp even eLookup = true := by decide
example : everyVarImm even iRegOk = true := by decide
example : everyVarImm even iRegBad = false := by decide
example : everyVarImm even iImm = true := by decide
example : everyVarInst even vConstOk = true := by decide
example : everyVarInst even vBinopOk = true := by decide
example : everyVarInst even vBinopBad = false := by decide
example : everyVarInst even vShiftOk = true := by decide
example : everyVarInst even vDivOk = true := by decide
example : everyVarInst even vAddCarryBad = false := by decide
example : everyVarInst even vLongDivOk = true := by decide
example : everyVarInst even vMemLoadOk = true := by decide
example : everyVarInst even vMemLoadBad = false := by decide
example : everyVarInst even vMemLoad8Ok = true := by decide
example : everyVarInst even vMemLoad16 = true := by decide
example : everyVarInst even vSkip = true := by decide

/-! ## Exact-carrier HOL variants (`flapjack-yuc3`)

`everyVarImmHOL` / `everyVarInstHOL` are the tagged exact ports of HOL
`wordLang$every_var_imm` / `every_var_inst`.  They must agree with the
production helpers on every fixture (same clause set) and admit the positive
width binder required by HOL's `dimindex (:α) ≥ 1`; the 64-bit FP-move fixture
exercises HOL's `dimindex (:α) = 64` branch. -/

example : everyVarImmHOL (width := 8) even iRegOk = true := by decide
example : everyVarImmHOL (width := 8) even iRegBad = false := by decide
example : everyVarImmHOL (width := 8) even iImm = true := by decide

private def guardsHOL : List Bool :=
  [everyVarImmHOL (width := 8) even iRegOk, everyVarImmHOL (width := 8) even iRegBad, everyVarImmHOL (width := 8) even iImm, everyVarInstHOL (width := 8) even vConstOk, everyVarInstHOL (width := 8) even vBinopOk, everyVarInstHOL (width := 8) even vBinopBad, everyVarInstHOL (width := 8) even vShiftOk, everyVarInstHOL (width := 8) even vDivOk, everyVarInstHOL (width := 8) even vAddCarryBad, everyVarInstHOL (width := 8) even vLongDivOk, everyVarInstHOL (width := 8) even vMemLoadOk, everyVarInstHOL (width := 8) even vMemLoadBad, everyVarInstHOL (width := 8) even vMemLoad8Ok, everyVarInstHOL (width := 8) even vMemLoad16, everyVarInstHOL (width := 8) even vSkip]

private def expectedHOL : List Bool :=
  [true, false, true, true, true, false, true, true, false, true, true, false, true, true, true]

#guard guardsHOL == expectedHOL

private def guards : List Bool :=
  [everyVarExp even eVar, everyVarExp even eVarOdd, everyVarExp even eConst, everyVarExp even eLoad, everyVarExp even eOpOk, everyVarExp even eOpBad, everyVarExp even eShiftBad, everyVarExp even eLookup, everyVarImm even iRegOk, everyVarImm even iRegBad, everyVarImm even iImm, everyVarInst even vConstOk, everyVarInst even vBinopOk, everyVarInst even vBinopBad, everyVarInst even vShiftOk, everyVarInst even vDivOk, everyVarInst even vAddCarryBad, everyVarInst even vLongDivOk, everyVarInst even vMemLoadOk, everyVarInst even vMemLoadBad, everyVarInst even vMemLoad8Ok, everyVarInst even vMemLoad16, everyVarInst even vSkip]

private def expected : List Bool :=
  [true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true]

#guard guards == expected

def runChecks : IO Bool := do
  if guards == expected && guardsHOL == expectedHOL then
    IO.println "PASS wordLang every_var_exp/every_var_imm/every_var_inst match all 23 retained integer oracle rows"
    IO.println "PASS wordLang exact everyVarImmHOL/everyVarInstHOL match all 15 retained integer oracle rows"
  else
    IO.println "FAIL wordLang every_var family oracle rows"
  pure (guards == expected && guardsHOL == expectedHOL)

end Flapjack.Test.WordLangEveryVarParity