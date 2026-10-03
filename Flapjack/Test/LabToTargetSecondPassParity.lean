import Flapjack.Compiler.Backend.LabToTarget.SecondPass

/-! The exact `HolAsm`/`HolInst`/`HolArith`/`HolAddr`/`HolRegImm` carriers expose
only `Repr`, so `decide +kernel` cannot compare the whole `Line`/`Section`
values.  The missing decidable-equality instances are derived below (test-only
infrastructure; they add no correctness content). -/
deriving instance DecidableEq for Flapjack.Compiler.Encoders.Asm.HolRegImm
deriving instance DecidableEq for Flapjack.Compiler.Encoders.Asm.HolArith
deriving instance DecidableEq for Flapjack.Compiler.Encoders.Asm.HolAddr
deriving instance DecidableEq for Flapjack.Compiler.Encoders.Asm.HolInst
deriving instance DecidableEq for Flapjack.Compiler.Encoders.Asm.HolAsm

/-!
# Native kernel replays of `lab_to_target_secondpass_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_secondpass_probeScript.sml`, which `EVAL`s the
original `lab_to_target` second-pass definitions (`enc_lines_again_def`,
`enc_secs_again_def`, `lines_upd_lab_len_def`, `upd_lab_len_def`) on concrete
64-bit `labLang$line`/`labLang$sec` values (bead `flapjack-pxn.18.5.15.10.13`).

The section map is section 7 to `{0 -> 10, 3 -> 13}` so `find_pos (Lab 7 0) = 10`
and, at `pos = 10`, `get_jump_offset (Jump (Lab 7 0)) = 0`.  The supplied
encoder returns the three bytes `[1,2,3]` for every `asm`, making the re-encoded
length observable.  Every captured row is replayed below as a kernel-checked
example.
-/

namespace Flapjack.Test.LabToTargetSecondPassParity

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

private def labs : Spt (Spt Nat) :=
  sptInsert 7 (sptInsert 0 10 (sptInsert 3 13 (.ln : Spt Nat))) (.ln : Spt (Spt Nat))

private def enc : HolAsm 64 → List (BitVec 8) := fun _ => [1, 2, 3]

private def lineKeep : List Line64 :=
  [.labAsm (.jump (.lab 7 0)) (0 : BitVec 64) [] 7, .label 5 0 4,
   .asm (.asmi (.inst .skip)) [9] 2]

private def lineReencode : List Line64 :=
  [.labAsm (.jump (.lab 7 0)) (99 : BitVec 64) [] 1]

private def lineReencodeLong : List Line64 :=
  [.labAsm (.jump (.lab 7 0)) (99 : BitVec 64) [] 7]

private def secsTwo : List Sec64 :=
  [⟨5, [.labAsm (.jump (.lab 7 0)) (99 : BitVec 64) [] 1]⟩,
   ⟨6, [.label 4 0 2, .asm (.asmi (.inst .skip)) [9] 5]⟩]

private def updLines : List Line64 :=
  [.label 5 0 7, .asm (.asmi (.inst .skip)) [9] 2,
   .labAsm (.jump (.lab 7 3)) (3 : BitVec 64) [] 4]

private def updSecs : List Sec64 :=
  [⟨5, [.label 5 0 9, .asm (.asmi (.inst .skip)) [9] 2]⟩,
   ⟨6, [.labAsm (.jump (.lab 7 3)) (3 : BitVec 64) [] 3]⟩]

-- EncLinesAgainEmpty
example : encLinesAgain labs [] 10 enc ([] : List Line64) [] true = ([], 10, true) :=
  by decide +kernel

-- EncLinesAgainKeep
example :
    encLinesAgain labs [] 10 enc lineKeep [] true =
      ([.labAsm (.jump (.lab 7 0)) (0 : BitVec 64) [] 7, .label 5 0 4,
        .asm (.asmi (.inst .skip)) [9] 2], 23, true) :=
  by decide +kernel

-- EncLinesAgainReencodeShort
example :
    encLinesAgain labs [] 10 enc lineReencode [] true =
      ([.labAsm (.jump (.lab 7 0)) (0 : BitVec 64) [1, 2, 3] 3], 13, false) :=
  by decide +kernel

-- EncLinesAgainReencodeLong
example :
    encLinesAgain labs [] 10 enc lineReencodeLong [] true =
      ([.labAsm (.jump (.lab 7 0)) (0 : BitVec 64) [1, 2, 3] 7], 17, true) :=
  by decide +kernel

-- EncSecsAgainEmpty
example : encSecsAgain 10 labs [] enc ([] : List Sec64) = ([], true) :=
  by decide +kernel

-- EncSecsAgainTwo
example :
    encSecsAgain 10 labs [] enc secsTwo =
      ([⟨5, [.labAsm (.jump (.lab 7 0)) (0 : BitVec 64) [1, 2, 3] 3]⟩,
        ⟨6, [.label 4 0 2, .asm (.asmi (.inst .skip)) [9] 5]⟩], false) :=
  by decide +kernel

-- LinesUpdLabLenEmpty
example : linesUpdLabLen 5 ([] : List Line64) [] = ([], 5) := by decide +kernel

-- LinesUpdLabLenEven
example :
    linesUpdLabLen 0 updLines [] =
      ([.label 5 0 0, .asm (.asmi (.inst .skip)) [9] 2,
        .labAsm (.jump (.lab 7 3)) (3 : BitVec 64) [] 4], 6) :=
  by decide +kernel

-- LinesUpdLabLenOdd
example :
    linesUpdLabLen 1 updLines [] =
      ([.label 5 0 1, .asm (.asmi (.inst .skip)) [9] 2,
        .labAsm (.jump (.lab 7 3)) (3 : BitVec 64) [] 4], 8) :=
  by decide +kernel

-- UpdLabLenEmpty
example : updLabLen 5 ([] : List Sec64) = [] := by decide +kernel

-- UpdLabLenTwo
example :
    updLabLen 0 updSecs =
      [⟨5, [.label 5 0 0, .asm (.asmi (.inst .skip)) [9] 2]⟩,
       ⟨6, [.labAsm (.jump (.lab 7 3)) (3 : BitVec 64) [] 3]⟩] :=
  by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target enc_lines_again/enc_secs_again/lines_upd_lab_len/upd_lab_len match all 11 oracle rows"
  pure true

end Flapjack.Test.LabToTargetSecondPassParity
