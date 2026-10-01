import Flapjack.Compiler.Backend.LabFilter
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Misc.ListSubset
import Flapjack.Test.LabToTargetRemoveLabelsParity

/-!
# Native kernel replays of `lab_to_target_compile_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_compile_probeScript.sml`, which `EVAL`s the
original `lab_filter` and `lab_to_target` definitions (`list_subset_def`,
`not_skip_def`, `filter_skip_def`, `config`, `compile_lab_def`, `compile_def`)
on concrete 64-bit `labLang$line`/`labLang$sec` values (bead
`flapjack-pxn.18.5.15.10.27`).

The 64-bit assembler configuration is the same 8/64 record used by the sibling
label-removal probe, with an encoder that discards its argument.  Every captured
row is replayed below as a kernel-checked example.
-/

namespace Flapjack.Test.LabToTargetCompileParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Misc
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

private def foo : MlS := Flapjack.Basis.Pure.MlString.MlString.implode [w8 102, w8 111, w8 111]

private def mkCfg (ffiNames : Option (List HolFfiName)) : Config :=
  { labels := .ln
    secPosLen := []
    pos := 10
    initClock := 0
    ffiNames := ffiNames
    shmemExtra := []
    hashSize := 0 }

private def lcfg : Config := mkCfg none

private abbrev skipLine : Line64 := .asm (.asmi (.inst .skip)) [w8 1] 1
private abbrev constLine : Line64 := .asm (.asmi (.inst (.const 1 (0 : BitVec 64)))) [] 1
private abbrev labelLine : Line64 := .label 1 5 1
private abbrev jumpLine : Line64 := .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 1

private abbrev loopCode : List Sec64 := [⟨1, [labelLine, jumpLine]⟩]
private abbrev loopCodeAfter : List Sec64 :=
  [⟨1, [.label 1 5 0, .labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [] 0]⟩]
private abbrev compileSkipCode : List Sec64 := [⟨1, [skipLine, labelLine, jumpLine]⟩]
private abbrev ffiCode : List Sec64 := [⟨1, [.labAsm (.callFFI foo) (0 : BitVec 64) [] 1]⟩]
private abbrev callCode : List Sec64 := [⟨1, [.labAsm (.call (.lab 0 0)) (0 : BitVec 64) [] 0]⟩]

private abbrev loopLabs : Spt (Spt Nat) :=
  sptInsert 1 (sptFromAList ((0, 10) :: [(5, 10)])) .ln

private abbrev loopResult : Option (List (BitVec 8) × Config) :=
  some ([], { mkCfg (some []) with labels := loopLabs, secPosLen := [(1, 10, 0)] })

private theorem hFind : findFfiNames (width := 64) loopCode = [] := by
  simp only [findFfiNames.eq_1, findFfiNames.eq_2, findFfiNames.eq_3, findFfiNames.eq_4,
    loopCode, labelLine, jumpLine]

private theorem hRemove : removeLabels 0 cfg 10 .ln [] loopCode =
    some (loopCodeAfter, loopLabs) := by
  decide +kernel

private theorem hProg : progToBytes (width := 64) loopCodeAfter = [] := by
  simp only [progToBytes.eq_1, progToBytes.eq_2, progToBytes.eq_3, loopCodeAfter,
    lineBytes, List.append_nil]

private theorem hSymbols : getSymbols (width := 64) 10 loopCodeAfter = [(1, 10, 0)] := by
  simp only [getSymbols.eq_1, getSymbols.eq_2, loopCodeAfter, secLength]

private theorem hShmem : getShmemInfo (width := 64) loopCodeAfter 10 [] [] = ([], []) := by
  simp only [getShmemInfo.eq_1, getShmemInfo.eq_2, getShmemInfo.eq_3, getShmemInfo.eq_4,
    getShmemInfo.eq_5, getShmemInfo.eq_6, loopCodeAfter]

private theorem hFindFfi : findFfiNames (width := 64) ffiCode = [.extCall foo] := by
  simp only [findFfiNames.eq_1, findFfiNames.eq_2, findFfiNames.eq_3, findFfiNames.eq_4,
    ffiCode, listAddIfFresh]

private theorem hFindCall : findFfiNames (width := 64) callCode = [] := by
  simp only [findFfiNames.eq_1, findFfiNames.eq_2, findFfiNames.eq_3, findFfiNames.eq_4,
    callCode]

private theorem hRemoveCall : removeLabels 0 cfg 10 .ln [] callCode = none := by
  decide +kernel

private theorem hFilter : filterSkip (width := 64) compileSkipCode = loopCode := by
  decide +kernel

-- ListSubsetTrue
example : listSubset [1, 2] [2, 3, 1] = true := by decide +kernel

-- ListSubsetFalse
example : listSubset [1] ([] : List Nat) = false := by decide +kernel

-- NotSkipSkip
example : notSkip (width := 64) skipLine = false := by decide +kernel

-- NotSkipAsm
example : notSkip (width := 64) constLine = true := by decide +kernel

-- NotSkipLabel
example : notSkip (width := 64) labelLine = true := by decide +kernel

-- NotSkipLabAsm
example : notSkip (width := 64) jumpLine = true := by decide +kernel

-- FilterSkipEmpty
example : filterSkip (width := 64) ([] : List Sec64) = [] := by decide +kernel

-- FilterSkipOne
example : filterSkip (width := 64) [⟨1, [skipLine, jumpLine]⟩] =
    [⟨1, [jumpLine]⟩] := by decide +kernel

-- FilterSkipTwo
example : filterSkip (width := 64)
    [⟨1, [skipLine]⟩, ⟨2, [jumpLine, skipLine]⟩] =
      [⟨1, []⟩, ⟨2, [jumpLine]⟩] := by decide +kernel

-- ConfigLabels
example : lcfg.labels = (.ln : Spt (Spt Nat)) := by decide +kernel

-- ConfigSecPosLen
example : lcfg.secPosLen = ([] : List (Nat × Nat × Nat)) := by decide +kernel

-- ConfigPos
example : lcfg.pos = 10 := by decide +kernel

-- ConfigInitClock
example : lcfg.initClock = 0 := by decide +kernel

-- ConfigFfiNames
example : lcfg.ffiNames = (none : Option (List HolFfiName)) := by decide +kernel

-- ConfigShmemExtra
example : lcfg.shmemExtra = ([] : List ShmemInfoNum) := by decide +kernel

-- ConfigHashSize
example : lcfg.hashSize = 0 := by decide +kernel

-- CompileLabSuccess
example : compileLab cfg lcfg loopCode = loopResult := by
  simp only [compileLab, mkCfg, lcfg, hFind, hRemove, hProg, hSymbols, hShmem]
  rfl

-- CompileLabFfiSubsetFail
example : compileLab cfg (mkCfg (some [])) ffiCode = none := by
  simp only [compileLab, mkCfg, hFindFfi, listSubset]
  rfl

-- CompileLabRemoveLabelsNone
example : compileLab cfg (mkCfg none) callCode = none := by
  simp only [compileLab, mkCfg, hFindCall, hRemoveCall]
  rfl

-- CompileSkip
example : compile cfg lcfg compileSkipCode = loopResult := by
  simp only [compile, compileLab, mkCfg, lcfg, hFilter, hFind, hRemove, hProg, hSymbols,
    hShmem]
  rfl

-- CompileLabFilterSkip
example : compileLab cfg lcfg (filterSkip (width := 64) compileSkipCode) = loopResult := by
  simp only [compileLab, mkCfg, lcfg, hFilter, hFind, hRemove, hProg, hSymbols, hShmem]
  rfl

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target list_subset/not_skip/filter_skip/config/compile_lab/compile match all 21 oracle rows"
  pure true

end Flapjack.Test.LabToTargetCompileParity
