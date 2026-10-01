import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Test.LabToTargetPaddingParity

/-!
# Native kernel replays of `lab_to_target_removelabels_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_removelabels_probeScript.sml`, which `EVAL`s
the original `lab_to_target` zero-label accumulation and label-removal
definitions (`zero_labs_acc_of_def`, `line_get_zero_labs_acc_def`,
`sec_get_zero_labs_acc_def`, `get_zero_labs_acc_def`,
`zero_labs_acc_exist_def`, `remove_labels_loop_def`, `remove_labels_def`,
`line_bytes_def`, `prog_to_bytes_def`) on concrete 64-bit
`labLang$line`/`labLang$sec` values (bead `flapjack-pxn.18.5.15.10.16`).

The 64-bit assembler configuration is the same 8/64 record used by the sibling
padding probe, with an encoder that discards its argument.  Every captured row
is replayed below as a kernel-checked example.
-/

namespace Flapjack.Test.LabToTargetRemoveLabelsParity

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

private def labJumpLine : Line64 :=
  .labAsm (.jump (.lab 6 0)) (0 : BitVec 64) [] 1

private def zeroCode : List Sec64 :=
  [⟨1, [.label 1 5 1,
        .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1,
        .labAsm (.jump (.lab 1 5)) (0 : BitVec 64) [] 1,
        .labAsm (.jumpCmp .equal 2 (.imm (1 : BitVec 64)) (.lab 3 0))
          (0 : BitVec 64) [] 1,
        .labAsm .halt (0 : BitVec 64) [] 1]⟩]

private def bytesCode : List Sec64 :=
  [⟨1, [.label 1 2 3, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 2]⟩,
   ⟨2, []⟩,
   ⟨3, [.labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [w8 3] 1]⟩]

private def loopCode : List Sec64 :=
  [⟨1, [.label 1 5 1, .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1]⟩]

private def loopLabs : Spt (Spt Nat) :=
  sptInsert 1 (sptFromAList ((0, 10) :: [(5, 10)])) .ln

-- ZeroLabsAccOfLocHit
example : sptToAList (zeroLabsAccOf (width := 64) (.locValue 2 (.lab 4 0)) .ln) = [(4, ())] := by
  decide +kernel

-- ZeroLabsAccOfLocNonzero
example : sptToAList (zeroLabsAccOf (width := 64) (.locValue 2 (.lab 4 7)) .ln) = [] := by
  decide +kernel

-- ZeroLabsAccOfJumpHit
example : sptToAList (zeroLabsAccOf (width := 64) (.jump (.lab 6 0)) .ln) = [(6, ())] := by
  decide +kernel

-- ZeroLabsAccOfJumpNonzero
example : sptToAList (zeroLabsAccOf (width := 64) (.jump (.lab 6 3)) .ln) = [] := by
  decide +kernel

-- ZeroLabsAccOfJumpCmpHit
example :
    sptToAList
        (zeroLabsAccOf (width := 64) (.jumpCmp .equal 2 (.imm (1 : BitVec 64)) (.lab 8 0)) .ln) =
      [(8, ())] := by
  decide +kernel

-- ZeroLabsAccOfJumpCmpNonzero
example :
    sptToAList
        (zeroLabsAccOf (width := 64) (.jumpCmp .equal 2 (.imm (1 : BitVec 64)) (.lab 8 9)) .ln) =
      [] := by
  decide +kernel

-- ZeroLabsAccOfCatchAll
example : sptToAList (zeroLabsAccOf (width := 64) .halt .ln) = [] := by decide +kernel

-- LineGetZeroLabsAccLabAsm
example : sptToAList (lineGetZeroLabsAcc (width := 64) labJumpLine .ln) = [(6, ())] := by
  decide +kernel

-- LineGetZeroLabsAccLabel
example : sptToAList (lineGetZeroLabsAcc (width := 64) (.label 1 2 3) .ln) = [] := by
  decide +kernel

-- LineGetZeroLabsAccAsm
example :
    sptToAList
        (lineGetZeroLabsAcc (width := 64) (.asm (.asmi (.inst .skip)) [w8 1] 1) .ln) = [] := by
  decide +kernel

-- GetZeroLabsAccEmpty
example : sptToAList (getZeroLabsAcc ([] : List Sec64)) = [] := by decide +kernel

-- GetZeroLabsAccConcrete
example : sptToAList (getZeroLabsAcc zeroCode) = [(3, ()), (1, ())] := by
  decide +kernel

private def goodLabs : Spt (Spt Nat) :=
  sptInsert 1 (sptInsert 0 10 .ln) (sptInsert 3 (sptInsert 0 10 .ln) .ln)

private def badLabs : Spt (Spt Nat) :=
  sptInsert 1 (sptInsert 0 10 .ln) .ln

-- ZeroLabsAccExistTrue
example : zeroLabsAccExist goodLabs zeroCode = true := by decide +kernel

-- ZeroLabsAccExistFalse
example : zeroLabsAccExist badLabs zeroCode = false := by decide +kernel

-- The original inner payload is arbitrary, not restricted to natural numbers.
example : zeroLabsAccExist
    (sptInsert 1 (sptInsert 0 true .ln)
      (sptInsert 3 (sptInsert 0 false .ln) .ln)) zeroCode = true := by
  decide +kernel

example : zeroLabsAccExist
    (sptInsert 1 (sptInsert 0 ([] : List Nat) .ln) .ln) zeroCode = false := by
  decide +kernel

-- LineBytesLabel
example : lineBytes (.label 1 2 3 : Line64) = [] := by decide +kernel

-- LineBytesAsm
example : lineBytes (.asm (.asmi (.inst .skip)) [w8 1, w8 2] 2 : Line64) =
    [w8 1, w8 2] := by decide +kernel

-- LineBytesLabAsm
example : lineBytes labJumpLine = [] := by decide +kernel

-- ProgToBytesEmpty
example : progToBytes (width := 64) ([] : List Sec64) = [] := by
  simp only [progToBytes.eq_1]

-- ProgToBytesConcrete
example : progToBytes (width := 64) bytesCode = [w8 1, w8 2, w8 3] := by
  simp only [progToBytes.eq_1, progToBytes.eq_2, progToBytes.eq_3, bytesCode,
    lineBytes, w8]
  decide +kernel

-- RemoveLabelsLoopZero
example :
    removeLabelsLoop 0 cfg 10 .ln [] loopCode =
      some ([⟨1, [.label 1 5 0,
                   .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1]⟩],
        loopLabs) := by
  decide +kernel

-- RemoveLabelsLoopOne
example :
    removeLabelsLoop 1 cfg 10 .ln [] loopCode =
      some ([⟨1, [.label 1 5 0,
                   .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1]⟩],
        loopLabs) := by
  decide +kernel

-- RemoveLabelsZero
example :
    removeLabels 0 cfg 10 .ln [] loopCode =
      some ([⟨1, [.label 1 5 0,
                   .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 0]⟩],
        loopLabs) := by
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target zero_labs_acc_of/line_get_zero_labs_acc/sec_get_zero_labs_acc/get_zero_labs_acc/zero_labs_acc_exist/remove_labels_loop/remove_labels/line_bytes/prog_to_bytes match all 22 oracle rows"
  pure true

end Flapjack.Test.LabToTargetRemoveLabelsParity
