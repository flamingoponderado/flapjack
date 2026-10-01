import Flapjack.Compiler.Backend.LabToTarget.Encoding

/-!
# Native kernel replays of `lab_to_target_encoding_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_encoding_probeScript.sml`, which `EVAL`s the
original `lab_to_target` encoding definitions at dimension 8 with a concrete
instruction encoder (`Inst Skip` to `[1w]`, every other asm to `[2w;3w]`).

Every captured row is replayed below as a kernel-checked `rfl` example and as
a `runChecks` runtime comparison against the same concrete values.
-/

namespace Flapjack.Test.LabToTargetEncodingParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

private abbrev Line8 :=
  Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
    (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)
private abbrev Sec8 := Section Line8

/-- The probe's concrete encoder: `Inst Skip` to `[1w]`, every other asm to
`[2w;3w]`. -/
private def Enc : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [1]
  | _ => [2, 3]

private def jumpL : AsmWithLab HolCmp (HolRegImm 8) MlString := .jump (.lab 1 2)
private def jumpCmpL : AsmWithLab HolCmp (HolRegImm 8) MlString :=
  .jumpCmp .equal 1 (.reg 2) (.lab 3 4)
private def callL : AsmWithLab HolCmp (HolRegImm 8) MlString := .call (.lab 5 6)
private def locValueL : AsmWithLab HolCmp (HolRegImm 8) MlString := .locValue 7 (.lab 8 9)
private def haltL : AsmWithLab HolCmp (HolRegImm 8) MlString := .halt
private def installL : AsmWithLab HolCmp (HolRegImm 8) MlString := .install
private def callFFIL : AsmWithLab HolCmp (HolRegImm 8) MlString := .callFFI (ofString "f")

private def asmiSkip : AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8) := .asmi (.inst .skip)
private def cbwL : AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8) := .cbw 1 2
private def shareMemL : AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8) :=
  .shareMem .load 2 (.addr 3 0)

private def labelL : Line8 := .label 3 4 99
private def asmSkipL : Line8 := .asm asmiSkip [] 0
private def asmCbwL : Line8 := .asm cbwL [] 0
private def labAsmL : Line8 := .labAsm haltL 0 [] 0
private def secL : Sec8 := { sectionId := 3, lines := [labelL, asmSkipL] }

-- FFIOffset
example : ffiOffset = 16 := rfl
-- LabInstJump
example : labInst (0 : BitVec 8) jumpL = HolAsm.jump (0 : BitVec 8) := rfl
-- LabInstJumpCmp
example : labInst (0 : BitVec 8) jumpCmpL =
    HolAsm.jumpCmp .equal 1 (.reg 2) (0 : BitVec 8) := rfl
-- LabInstCall
example : labInst (0 : BitVec 8) callL = HolAsm.call (0 : BitVec 8) := rfl
-- LabInstLocValue
example : labInst (0 : BitVec 8) locValueL = HolAsm.loc 7 (0 : BitVec 8) := rfl
-- LabInstHalt
example : labInst (0 : BitVec 8) haltL = HolAsm.jump (0 : BitVec 8) := rfl
-- LabInstInstall
example : labInst (0 : BitVec 8) installL = HolAsm.jump (0 : BitVec 8) := rfl
-- LabInstCallFFI
example : labInst (0 : BitVec 8) callFFIL = HolAsm.jump (0 : BitVec 8) := rfl
-- CbwToAsmAsmi
example : cbwToAsmExact asmiSkip = HolAsm.inst (HolInst.skip) := rfl
-- CbwToAsmCbw
example : cbwToAsmExact cbwL =
    HolAsm.inst (HolInst.mem .store8 2 (.addr 1 (0 : BitVec 8))) := rfl
-- CbwToAsmShareMem
example : cbwToAsmExact shareMemL =
    HolAsm.inst (HolInst.mem .load 2 (.addr 3 (0 : BitVec 8))) := rfl
-- EncLineLabel
example : encLine Enc 7 labelL = .label 3 4 7 := rfl
-- EncLineAsm
example : encLine Enc 7 asmSkipL = .asm asmiSkip [1] 1 := rfl
-- EncLineAsmCbw
example : encLine Enc 7 asmCbwL = .asm cbwL [2, 3] 2 := rfl
-- EncLineLabAsm
example : encLine Enc 7 labAsmL = .labAsm haltL (0 : BitVec 8) [2, 3] 2 := rfl
-- EncSec
example : encSec Enc 7 secL =
    { sectionId := 3, lines := [.label 3 4 7, .asm asmiSkip [1] 1] } := rfl
-- EncSecList
example : encSecList Enc [secL] =
    [{ sectionId := 3, lines := [.label 3 4 1, .asm asmiSkip [1] 1] }] := rfl

private def checkEq (name : String) (actual expected : String) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

/-- Runtime replay of the 17 probe rows through `repr`, which is available for
the exact `Line`/`Section`/`HolAsm` carriers (some lack `BEq`). -/
def runChecks : IO Bool := do
  let results ← [
    checkEq "lab_to_target encoding FFIOffset" (reprStr ffiOffset) (reprStr (16 : Nat)),
    checkEq "lab_to_target encoding LabInstJump"
      (reprStr (labInst (0 : BitVec 8) jumpL)) (reprStr (HolAsm.jump (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstJumpCmp"
      (reprStr (labInst (0 : BitVec 8) jumpCmpL))
      (reprStr (HolAsm.jumpCmp .equal 1 (.reg 2) (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstCall"
      (reprStr (labInst (0 : BitVec 8) callL)) (reprStr (HolAsm.call (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstLocValue"
      (reprStr (labInst (0 : BitVec 8) locValueL)) (reprStr (HolAsm.loc 7 (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstHalt"
      (reprStr (labInst (0 : BitVec 8) haltL)) (reprStr (HolAsm.jump (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstInstall"
      (reprStr (labInst (0 : BitVec 8) installL)) (reprStr (HolAsm.jump (0 : BitVec 8))),
    checkEq "lab_to_target encoding LabInstCallFFI"
      (reprStr (labInst (0 : BitVec 8) callFFIL)) (reprStr (HolAsm.jump (0 : BitVec 8))),
    checkEq "lab_to_target encoding CbwToAsmAsmi"
      (reprStr (cbwToAsmExact asmiSkip)) (reprStr (HolAsm.inst (HolInst.skip : HolInst 8))),
    checkEq "lab_to_target encoding CbwToAsmCbw"
      (reprStr (cbwToAsmExact cbwL))
      (reprStr (HolAsm.inst (HolInst.mem .store8 2 (.addr 1 (0 : BitVec 8))))),
    checkEq "lab_to_target encoding CbwToAsmShareMem"
      (reprStr (cbwToAsmExact shareMemL))
      (reprStr (HolAsm.inst (HolInst.mem .load 2 (.addr 3 (0 : BitVec 8))))),
    checkEq "lab_to_target encoding EncLineLabel"
      (reprStr (encLine Enc 7 labelL)) (reprStr (.label 3 4 7 : Line8)),
    checkEq "lab_to_target encoding EncLineAsm"
      (reprStr (encLine Enc 7 asmSkipL)) (reprStr (.asm asmiSkip [1] 1 : Line8)),
    checkEq "lab_to_target encoding EncLineAsmCbw"
      (reprStr (encLine Enc 7 asmCbwL)) (reprStr (.asm cbwL [2, 3] 2 : Line8)),
    checkEq "lab_to_target encoding EncLineLabAsm"
      (reprStr (encLine Enc 7 labAsmL)) (reprStr (.labAsm haltL (0 : BitVec 8) [2, 3] 2 : Line8)),
    checkEq "lab_to_target encoding EncSec"
      (reprStr (encSec Enc 7 secL))
      (reprStr ({ sectionId := 3, lines := [.label 3 4 7, .asm asmiSkip [1] 1] } : Sec8)),
    checkEq "lab_to_target encoding EncSecList"
      (reprStr (encSecList Enc [secL]))
      (reprStr ([{ sectionId := 3, lines := [.label 3 4 1, .asm asmiSkip [1] 1] }] : List Sec8))
    ].mapM id
  pure (results.all id)

end Flapjack.Test.LabToTargetEncodingParity
