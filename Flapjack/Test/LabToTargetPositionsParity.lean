import Flapjack.Compiler.Backend.LabToTarget.Positions

/-!
# Native kernel replays of `lab_to_target_positions_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_positions_probeScript.sml`, which `EVAL`s the
original `lab_to_target` position, label, FFI-index and jump-offset definitions
(`find_pos_def`, `get_label_def`, `get_ffi_index_def`, `get_jump_offset_def`) on
concrete `labLang$lab`, `labLang$asm_with_lab`, `num spt spt` and `ffiname list`
values (bead `flapjack-pxn.18.5.15.10.11`).

The opaque `cmp`/`reg_imm` fields of `get_label` are instantiated at `Unit`
(it never inspects them).  `get_jump_offset` is observed at 64-bit; HOL's result
word dimension is independent of the instruction word, so the replay fixes both
independently.  Every captured row is replayed below as a kernel-checked
example.
-/

namespace Flapjack.Test.LabToTargetPositionsParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString
private abbrev AWL := AsmWithLab Unit Unit Unit
private abbrev AWL64 := AsmWithLab HolCmp (HolRegImm 64) MlS

private def labs : Spt (Spt Nat) :=
  sptInsert 7 (sptInsert 0 10 (sptInsert 3 13 (.ln : Spt Nat))) (.ln : Spt (Spt Nat))

private def ffis : List HolFfiName :=
  [.extCall (Flapjack.Basis.Pure.MlString.ofString "a"),
   .extCall (Flapjack.Basis.Pure.MlString.ofString "b")]

-- FindPosHit / FindPosHitZero / FindPosDefaultLabel / FindPosDefaultSection
example : findPos (.lab 7 3) labs = 13 := by decide +kernel
example : findPos (.lab 7 0) labs = 10 := by decide +kernel
example : findPos (.lab 7 9) labs = 0 := by decide +kernel
example : findPos (.lab 5 3) labs = 0 := by decide +kernel

-- GetLabelJump / GetLabelJumpCmp / GetLabelCall / GetLabelLocValue / GetLabelDefault
example : getLabel (.jump (.lab 1 2) : AWL) = .lab 1 2 := rfl
example : getLabel (.jumpCmp () 0 () (.lab 3 4) : AWL) = .lab 3 4 := rfl
example : getLabel (.call (.lab 5 6) : AWL) = .lab 5 6 := rfl
example : getLabel (.locValue 7 (.lab 8 9) : AWL) = .lab 8 9 := rfl
example : getLabel (.halt : AWL) = .lab 0 0 := rfl

-- GetFfiIndexHit / GetFfiIndexDefault
example :
    getFfiIndex ffis (.extCall (Flapjack.Basis.Pure.MlString.ofString "b")) = 1 := by
  decide +kernel
example :
    getFfiIndex ffis (.extCall (Flapjack.Basis.Pure.MlString.ofString "c")) = 0 := by
  decide +kernel

-- GetJumpOffsetCallFFI / GetJumpOffsetInstall / GetJumpOffsetHalt / GetJumpOffsetJump
example :
    getJumpOffset (regImmWidth := 64) (width := 64)
      (.callFFI (Flapjack.Basis.Pure.MlString.ofString "b") : AWL64) ffis labs 10 =
      (0xFFFFFFFFFFFFFFB6 : BitVec 64) := by decide +kernel
example :
    getJumpOffset (regImmWidth := 64) (width := 64)
      (.install : AWL64) ffis labs 10 = (0xFFFFFFFFFFFFFFD6 : BitVec 64) := by decide +kernel
example :
    getJumpOffset (regImmWidth := 64) (width := 64)
      (.halt : AWL64) ffis labs 10 = (0xFFFFFFFFFFFFFFE6 : BitVec 64) := by decide +kernel
example :
    getJumpOffset (regImmWidth := 64) (width := 64)
      (.jump (.lab 7 3) : AWL64) ffis labs 10 = (3 : BitVec 64) := by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target find_pos/get_label/get_ffi_index/get_jump_offset match all 15 oracle rows"
  pure true

end Flapjack.Test.LabToTargetPositionsParity
