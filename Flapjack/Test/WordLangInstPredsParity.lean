module

public import Flapjack.Pancake.WordConvs

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.WordConvs
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Kernel-checked parity for the backend `wordConvs` instruction predicates
`distinct_tar_reg`, `two_reg_inst`, and `every_inst` against the direct HOL
oracle `scripts/hol-probes/word_convs_inst_preds_probe.out`.

The programs are built at the HOL word width `8 word` (`BitVec 8`), matching
the oracle fixture.
-/

namespace Flapjack.Test.WordLangInstPredsParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def emptySet : WordLangNumSetHOL := .ln

private def cutsets : WordLangCutsetsHOL := (emptySet, emptySet)

/-- `P i = (i = Skip)`, the HOL probe's test predicate. -/
private def isSkip : WordLangInst W → Bool
  | .skip => true
  | _ => false

-- Instruction fixtures (oracle rows 1-7).
private def binopSame : WordLangInst W := .arith (.binop .add 1 2 (.reg 1))
private def binopDiff : WordLangInst W := .arith (.binop .add 1 2 (.reg 3))
private def addCarrySame : WordLangInst W := .arith (.addCarry 1 2 1 3)
private def binopTwoSame : WordLangInst W := .arith (.binop .add 1 1 (.reg 0))
private def binopTwoDiff : WordLangInst W := .arith (.binop .add 1 2 (.reg 0))
private def instSkipInst : WordLangInst W := .skip

-- Program fixtures (oracle rows 8-15).
private def instSkip : WordLangProgHOL W := .inst instSkipInst
private def instConst : WordLangProgHOL W := .inst (.const 1 (0 : W))
private def opCurrHeap : WordLangProgHOL W := .opCurrHeap .add 1 2
private def callHandlerBad : WordLangProgHOL W :=
  .call none none [] (some (2, .inst (.const 1 (0 : W)), 20, 21))
private def callRetBad : WordLangProgHOL W :=
  .call (some ([1], cutsets, .inst instSkipInst, 10, 11))
    none [] (some (2, .inst (.const 1 (0 : W)), 20, 21))
private def callRetOk : WordLangProgHOL W :=
  .call (some ([1], cutsets, .inst instSkipInst, 10, 11)) none [] none
private def loopOk : WordLangProgHOL W := .loop emptySet (.inst instSkipInst) emptySet
private def allocProg : WordLangProgHOL W := .alloc 0 cutsets

-- 15 kernel-checked rows matching the HOL oracle.
example : distinctTarRegExact (HolInst.ofWordLangInst binopSame) = false := by decide
example : distinctTarRegExact (HolInst.ofWordLangInst binopDiff) = true := by decide
example : distinctTarRegExact (HolInst.ofWordLangInst addCarrySame) = false := by decide
example : distinctTarRegExact (HolInst.ofWordLangInst instSkipInst) = true := by decide

example : twoRegInstExact (HolInst.ofWordLangInst binopTwoSame) = true := by decide
example : twoRegInstExact (HolInst.ofWordLangInst binopTwoDiff) = false := by decide
example : twoRegInstExact (HolInst.ofWordLangInst instSkipInst) = true := by decide

example : everyInst isSkip instSkip = true := by decide
example : everyInst isSkip instConst = false := by decide
example : everyInst isSkip opCurrHeap = false := by decide
example : everyInst isSkip callHandlerBad = true := by decide
example : everyInst isSkip callRetBad = false := by decide
example : everyInst isSkip callRetOk = true := by decide
example : everyInst isSkip loopOk = true := by decide
example : everyInst isSkip allocProg = true := by decide

#guard distinctTarRegExact (HolInst.ofWordLangInst binopSame) == false
#guard distinctTarRegExact (HolInst.ofWordLangInst binopDiff) == true
#guard distinctTarRegExact (HolInst.ofWordLangInst addCarrySame) == false
#guard distinctTarRegExact (HolInst.ofWordLangInst instSkipInst) == true
#guard twoRegInstExact (HolInst.ofWordLangInst binopTwoSame) == true
#guard twoRegInstExact (HolInst.ofWordLangInst binopTwoDiff) == false
#guard twoRegInstExact (HolInst.ofWordLangInst instSkipInst) == true
#guard everyInst isSkip instSkip == true
#guard everyInst isSkip instConst == false
#guard everyInst isSkip opCurrHeap == false
#guard everyInst isSkip callHandlerBad == true
#guard everyInst isSkip callRetBad == false
#guard everyInst isSkip callRetOk == true
#guard everyInst isSkip loopOk == true
#guard everyInst isSkip allocProg == true

def runChecks : IO Bool := do
  let checks :=
    [ (distinctTarRegExact (HolInst.ofWordLangInst binopSame) == false,
        "PASS wordConvs distinct_tar_reg rejects targeting the source register")
    , (distinctTarRegExact (HolInst.ofWordLangInst addCarrySame) == false,
        "PASS wordConvs distinct_tar_reg excludes the source registers for AddCarry")
    , (twoRegInstExact (HolInst.ofWordLangInst binopTwoSame) == true,
        "PASS wordConvs two_reg_inst accepts equal source/destination")
    , (twoRegInstExact (HolInst.ofWordLangInst binopTwoDiff) == false,
        "PASS wordConvs two_reg_inst rejects distinct source/destination")
    , (everyInst isSkip callHandlerBad == true,
        "PASS wordConvs every_inst ignores a handler without return metadata")
    , (everyInst isSkip callRetBad == false,
        "PASS wordConvs every_inst descends into return and handler bodies")
    , (everyInst isSkip loopOk == true,
        "PASS wordConvs every_inst descends into Loop and Inst bodies")
    ]
  for (ok, message) in checks do
    if ok then IO.println message else IO.println s!"FAIL {message}"
  pure (checks.all (fun check => check.1))

end Flapjack.Test.WordLangInstPredsParity