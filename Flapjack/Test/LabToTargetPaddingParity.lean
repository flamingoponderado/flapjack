import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Test.LabToTargetSecondPassParity

/-!
# Native kernel replays of `lab_to_target_padding_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_padding_probeScript.sml`, which `EVAL`s the
original `lab_to_target` label-checking, padding and symbol-collection
definitions (`line_ok_light_def`, `sec_ok_light_def`, `pad_bytes_def`,
`add_nop_def`, `pad_section_def`, `pad_code_def`, `sec_length_def`,
`get_symbols_def`) on concrete 64-bit `labLang$line`/`labLang$sec` values
(bead `flapjack-pxn.18.5.15.10.14`).

The 64-bit assembler configuration has `code_alignment = 2`, jump/cjump/loc
offset bounds `(0, 100)`, `avoid_regs = [3]` and `reg_count = 8`, so a jump
target `8` is in range and two-aligned (`true`), `3` is unaligned (`false`),
`101` is out of range (`false`), and `Call` is unconditionally rejected.  Every
captured row is replayed below as a kernel-checked example.
-/

namespace Flapjack.Test.LabToTargetPaddingParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString
private abbrev Line64 :=
  Line (AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64))
    (AsmWithLab HolCmp (HolRegImm 64) MlS) (BitVec 64)
private abbrev Sec64 := Section Line64

private instance line64DecidableEq : DecidableEq Line64 := instDecidableEqLine
private instance sec64DecidableEq : DecidableEq Sec64 := instDecidableEqSection

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def cfg : AsmConfigExact 64 :=
  { isa := .riscv
    encode := fun _ => []
    bigEndian := false
    codeAlignment := 2
    linkReg := none
    avoidRegs := [3]
    regCount := 8
    fpRegCount := 4
    twoRegArith := true
    validImm := fun _ _ => true
    addrOffset := (0, 100)
    hwOffset := (0, 100)
    byteOffset := (0, 100)
    jumpOffset := (0, 100)
    cjumpOffset := (0, 100)
    locOffset := (0, 100) }

private def addNopLines : List Line64 :=
  [.label 1 2 3, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 2, .label 4 5 6]

private def padLines : List Line64 :=
  [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 3, .label 4 5 2]

private def symSecs : List Sec64 :=
  [⟨1, addNopLines⟩,
   ⟨2, [.label 7 8 1,
        .labAsm (.jump (.lab 1 2)) (0 : BitVec 64) [w8 1] 2]⟩]

-- PadBytesFits
example : padBytes ([w8 1, w8 2, w8 3] : List (BitVec 8)) 2 [w8 9] =
    [w8 1, w8 2, w8 3] := by decide +kernel

-- PadBytesAppend
example : padBytes ([w8 1, w8 2] : List (BitVec 8)) 3 [w8 9] =
    [w8 1, w8 2, w8 9] := by decide +kernel

-- PadBytesLonger
example : padBytes ([w8 1] : List (BitVec 8)) 3 [w8 9, w8 8] =
    [w8 1, w8 9, w8 8] := by decide +kernel

-- AddNopEmpty
example : addNop [w8 7] ([] : List Line64) = [] := by decide +kernel

-- AddNopLabelThenAsm
example :
    addNop [w8 7] addNopLines =
      [.label 1 2 3, .asm (.asmi (.inst .skip)) [w8 1, w8 2, w8 7] 3,
       .label 4 5 6] :=
  by decide +kernel

-- AddNopAsmHead
example :
    addNop [w8 7]
        ([.asm (.asmi (.inst .skip)) [w8 1] 1, .label 9 9 9] : List Line64) =
      [.asm (.asmi (.inst .skip)) [w8 1, w8 7] 2, .label 9 9 9] :=
  by decide +kernel

-- AddNopLabAsmHead
example :
    addNop [w8 7]
        ([.labAsm (.jump (.lab 1 2)) (0 : BitVec 64) [w8 1] 1,
          .label 9 9 9] : List Line64) =
      [.labAsm (.jump (.lab 1 2)) (0 : BitVec 64) [w8 1, w8 7] 2,
       .label 9 9 9] :=
  by decide +kernel

-- PadSectionEmpty
example :
    padSection [w8 9] ([] : List Line64) ([.label 1 2 3] : List Line64) =
      [.label 1 2 3] :=
  by decide +kernel

-- PadSectionConcrete
example :
    padSection [w8 9] padLines [] =
      [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2, w8 9, w8 9] 4,
       .label 4 5 0] :=
  by decide +kernel

-- PadCodeEmpty
example : padCode [w8 9] ([] : List Sec64) = [] := by decide +kernel

-- PadCodeTwo
example :
    padCode [w8 9]
        ([⟨1, [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 3]⟩,
          ⟨2, []⟩] : List Sec64) =
      [⟨1, [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2, w8 9] 3]⟩,
       ⟨2, []⟩] :=
  by decide +kernel

-- SecLengthEmpty
example : secLength ([] : List Line64) 5 = 5 := by decide +kernel

-- SecLengthConcrete
example : secLength addNopLines 10 = 21 := by decide +kernel

-- GetSymbolsEmpty
example : getSymbols 10 ([] : List Sec64) = [] := by decide +kernel

-- GetSymbolsTwo
example : getSymbols 10 symSecs = [(1, 10, 11), (2, 21, 3)] := by decide +kernel

-- LineOkLightLabel
example : lineOkLight cfg (.label 1 2 3 : Line64) = true := by decide +kernel

-- LineOkLightAsm
example :
    lineOkLight cfg (.asm (.asmi (.inst .skip)) [w8 1] 1 : Line64) = true :=
  by decide +kernel

-- LineOkLightHaltOk
example :
    lineOkLight cfg (.labAsm .halt (8 : BitVec 64) [] 0 : Line64) = true :=
  by decide +kernel

-- LineOkLightHaltBad
example :
    lineOkLight cfg (.labAsm .halt (3 : BitVec 64) [] 0 : Line64) = false :=
  by decide +kernel

-- LineOkLightInstall
example :
    lineOkLight cfg (.labAsm .install (8 : BitVec 64) [] 0 : Line64) = true :=
  by decide +kernel

-- LineOkLightCallFFIOk
example :
    lineOkLight cfg
        (.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.ofString "x"))
          (8 : BitVec 64) [] 0 : Line64) = true :=
  by decide +kernel

-- LineOkLightCall
example :
    lineOkLight cfg
        (.labAsm (.call (.lab 1 2)) (8 : BitVec 64) [] 0 : Line64) = false :=
  by decide +kernel

-- LineOkLightJumpCmpOk
example :
    lineOkLight cfg
        (.labAsm (.jumpCmp .equal 2 (.imm (1 : BitVec 64)) (.lab 1 2))
          (8 : BitVec 64) [] 0 : Line64) = true :=
  by decide +kernel

-- LineOkLightJumpCmpBad
example :
    lineOkLight cfg
        (.labAsm (.jumpCmp .equal 2 (.imm (1 : BitVec 64)) (.lab 1 2))
          (101 : BitVec 64) [] 0 : Line64) = false :=
  by decide +kernel

-- LineOkLightLocValue
example :
    lineOkLight cfg
        (.labAsm (.locValue 2 (.lab 1 2)) (8 : BitVec 64) [] 0 : Line64) =
      true :=
  by decide +kernel

-- SecOkLightMixed
example :
    secOkLight cfg
      (⟨1, [.label 1 2 3, .asm (.asmi (.inst .skip)) [w8 1] 1,
            .labAsm .halt (8 : BitVec 64) [] 0]⟩ : Sec64) = true :=
  by decide +kernel

-- SecOkLightCall
example :
    secOkLight cfg
      (⟨1, [.labAsm (.call (.lab 1 2)) (8 : BitVec 64) [] 0]⟩ : Sec64) =
      false :=
  by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target line_ok_light/sec_ok_light/pad_bytes/add_nop/pad_section/pad_code/sec_length/get_symbols match all 28 oracle rows"
  pure true

end Flapjack.Test.LabToTargetPaddingParity
