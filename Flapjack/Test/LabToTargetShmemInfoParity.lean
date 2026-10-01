import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Test.LabToTargetRemoveLabelsParity

/-!
# Native kernel replays of `lab_to_target_shmeminfo_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_shmeminfo_probeScript.sml`, which `EVAL`s the
original `lab_to_target` shared-memory/FFI name definitions
(`shmem_info_num`, `list_add_if_fresh_def`, `find_ffi_names_def`,
`get_memop_info_def`, `get_shmem_info_def`) on concrete 64-bit
`labLang$line`/`labLang$sec` values (bead `flapjack-pxn.18.5.15.10.20`).

Every captured row is replayed below as a kernel-checked example.
-/

namespace Flapjack.Test.LabToTargetShmemInfoParity

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
private instance shmemDecidableEq : DecidableEq ShmemInfoNum :=
  instDecidableEqShmemInfoNum

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def foo : MlS := Flapjack.Basis.Pure.MlString.MlString.implode [w8 102, w8 111, w8 111]
private def bar : MlS := Flapjack.Basis.Pure.MlString.MlString.implode [w8 98, w8 97, w8 114]

-- GetMemopInfoLoad
example : getMemopInfo .load = (.mappedRead, (0 : BitVec 8)) := by decide +kernel

-- GetMemopInfoLoad32
example : getMemopInfo .load32 = (.mappedRead, (4 : BitVec 8)) := by decide +kernel

-- GetMemopInfoLoad16
example : getMemopInfo .load16 = (.mappedRead, (2 : BitVec 8)) := by decide +kernel

-- GetMemopInfoLoad8
example : getMemopInfo .load8 = (.mappedRead, (1 : BitVec 8)) := by decide +kernel

-- GetMemopInfoStore
example : getMemopInfo .store = (.mappedWrite, (0 : BitVec 8)) := by decide +kernel

-- GetMemopInfoStore32
example : getMemopInfo .store32 = (.mappedWrite, (4 : BitVec 8)) := by decide +kernel

-- GetMemopInfoStore16
example : getMemopInfo .store16 = (.mappedWrite, (2 : BitVec 8)) := by decide +kernel

-- GetMemopInfoStore8
example : getMemopInfo .store8 = (.mappedWrite, (1 : BitVec 8)) := by decide +kernel

-- ListAddIfFreshEmpty
example : listAddIfFresh (3 : Nat) [] = [3] := by decide +kernel

-- ListAddIfFreshPresent
example : listAddIfFresh (2 : Nat) [1, 2] = [1, 2] := by decide +kernel

-- ListAddIfFreshAbsent
example : listAddIfFresh (3 : Nat) [1, 2] = [1, 2, 3] := by decide +kernel

private def ffiCode : List Sec64 :=
  [⟨1, [.labAsm (.callFFI foo) (0 : BitVec 64) [] 1,
        .labAsm (.callFFI bar) (0 : BitVec 64) [] 1,
        .labAsm (.callFFI foo) (0 : BitVec 64) [] 1]⟩,
   ⟨2, []⟩,
   ⟨3, [.labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1]⟩]

-- FindFfiNamesEmpty
example : findFfiNames (width := 64) ([] : List Sec64) = [] := by
  simp only [findFfiNames.eq_1]

-- FindFfiNamesConcrete
example : findFfiNames (width := 64) ffiCode = [.extCall foo, .extCall bar] := by
  simp only [findFfiNames.eq_1, findFfiNames.eq_2, findFfiNames.eq_3,
    findFfiNames.eq_4, ffiCode, listAddIfFresh]
  decide +kernel

private def nonCallFFICode : List Sec64 :=
  [⟨3, [.labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1]⟩]

-- FindFfiNamesNonCallFFI
example : findFfiNames (width := 64) nonCallFFICode = [] := by
  simp only [findFfiNames.eq_1, findFfiNames.eq_2, findFfiNames.eq_3,
    findFfiNames.eq_4, nonCallFFICode]

private def labelSkipCode : List Sec64 :=
  [⟨1, [.label 1 0 1,
        .asm (.shareMem .store 5 (.addr 7 (10 : BitVec 64)))
          [w8 1, w8 2, w8 3, w8 4] 4]⟩]

private def shareMemCode : List Sec64 :=
  [⟨1, [.asm (.shareMem .store32 5 (.addr 7 (10 : BitVec 64)))
          [w8 1, w8 2, w8 3, w8 4] 4]⟩]

private def asmAdvanceCode : List Sec64 :=
  [⟨1, [.asm (.asmi (.inst .skip)) [w8 9, w8 9] 2,
        .asm (.shareMem .store 4 (.addr 3 (2 : BitVec 64))) [w8 1] 1]⟩,
   ⟨2, []⟩]

-- GetShmemInfoEmpty
example : getShmemInfo (width := 64) ([] : List Sec64) 0 [] [] = ([], []) := by
  simp only [getShmemInfo.eq_1]

-- GetShmemInfoLabelSkip
example :
    getShmemInfo (width := 64) labelSkipCode 0 [] [] =
      ([.sharedMem .mappedWrite],
        [{ entryPc := 0, nbytes := 0, addrReg := 7, addrOff := 10, reg := 5,
           exitPc := 4 }]) := by
  simp only [getShmemInfo.eq_1, getShmemInfo.eq_2, getShmemInfo.eq_3,
    getShmemInfo.eq_4, getShmemInfo.eq_5, getShmemInfo.eq_6, labelSkipCode]
  decide +kernel

-- GetShmemInfoShareMem
example :
    getShmemInfo (width := 64) shareMemCode 0 [] [] =
      ([.sharedMem .mappedWrite],
        [{ entryPc := 0, nbytes := 4, addrReg := 7, addrOff := 10, reg := 5,
           exitPc := 4 }]) := by
  simp only [getShmemInfo.eq_1, getShmemInfo.eq_2, getShmemInfo.eq_3,
    getShmemInfo.eq_4, getShmemInfo.eq_5, getShmemInfo.eq_6, shareMemCode]
  decide +kernel

-- GetShmemInfoAsmAdvance
example :
    getShmemInfo (width := 64) asmAdvanceCode 0 [] [] =
      ([.sharedMem .mappedWrite],
        [{ entryPc := 2, nbytes := 0, addrReg := 3, addrOff := 2, reg := 4,
           exitPc := 3 }]) := by
  simp only [getShmemInfo.eq_1, getShmemInfo.eq_2, getShmemInfo.eq_3,
    getShmemInfo.eq_4, getShmemInfo.eq_5, getShmemInfo.eq_6, asmAdvanceCode]
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target shmem_info_num/list_add_if_fresh/find_ffi_names/get_memop_info/get_shmem_info match all 18 oracle rows"
  pure true

end Flapjack.Test.LabToTargetShmemInfoParity