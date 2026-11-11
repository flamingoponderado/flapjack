module

public import Flapjack.Compiler.Backend.LabProps
public import Flapjack.Compiler.Backend.LabProps.Native
public import Flapjack.Compiler.Backend.LabToTarget.Native
public import Flapjack.Compiler.Backend.LabSem.State
public import Flapjack.Compiler.Backend.StackToLab.Native
public import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
public import Flapjack.Compiler.Backend.StackProps.ProgramValidity

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.LabProps.Native
public meta import Flapjack.Compiler.Backend.LabToTarget.Native
public meta import Flapjack.Compiler.Backend.StackToLab.Native
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Cake labProps `line_ok_pre` over a concrete `AsmConfigExact`

Regression for the concrete configuration instantiation in
`Flapjack/Compiler/Backend/LabProps/Native.lean` (`lineOkPreHOL`,
`secOkPreHOL`, `allEncOkPreHOL`) together with the tagged
`flattenLineOkPreHOL`/`compileAllEncOkPreHOL` ports. The fourteen guards below
mirror the direct HOL `EVAL` rows in
`scripts/hol-probes/lab_props_line_ok_pre_probe.out` at an 8-bit configuration
identical to the probe fixture. -/

namespace Flapjack.Test.LabPropsLineOkPreParity

open Flapjack
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def cfg8 : AsmConfigExact 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := [3]
  regCount := 8
  fpRegCount := 4
  twoRegArith := true
  validImm := fun _ _ => true
  addrOffset := (w8 0, w8 100)
  hwOffset := (w8 0, w8 100)
  byteOffset := (w8 0, w8 100)
  jumpOffset := (w8 0, w8 100)
  cjumpOffset := (w8 0, w8 100)
  locOffset := (w8 0, w8 100)

private abbrev L := LabLineHOL 8
private abbrev S := LabSectionHOL 8

/-- Kernel-checkable Bool view of the reviewed `lineOkPreHOL` Prop: the same
clause `lineOkPreHOL` states, read at this fixture's exact carriers. -/
private def lineOkB (line : L) : Bool :=
  match line with
  | .asm instruction _ _ => asmOkExact (width := 8) (cbwToAsmHOL (width := 8) instruction) cfg8
  | _ => true

private def secOkB (sec : S) : Bool := sec.lines.all lineOkB

private def allEncOkB (sections : List S) : Bool := sections.all secOkB

/-- The Bool harness states exactly the reviewed `lineOkPreHOL` clause. -/
private theorem lineOkB_iff (line : L) : lineOkB line = true ↔ lineOkPreHOL cfg8 line := by
  cases line with
  | label => simp [lineOkB, lineOkPreHOL]
  | asm => simp [lineOkB, lineOkPreHOL]
  | labAsm => simp [lineOkB, lineOkPreHOL]

/-- The section harness agrees with the reviewed `secOkPreHOL`. -/
private theorem secOkB_iff (sec : S) : secOkB sec = true ↔ secOkPreHOL cfg8 sec := by
  simp [secOkB, secOkPreHOL, List.all_eq_true, lineOkB_iff]

/-- The program harness agrees with the reviewed `allEncOkPreHOL`. -/
private theorem allEncOkB_iff (sections : List S) :
    allEncOkB sections = true ↔ allEncOkPreHOL cfg8 sections := by
  simp [allEncOkB, allEncOkPreHOL, List.all_eq_true, secOkB_iff]

private def asmSkipLine : L := .asm (.asmi (.inst (.skip : HolInst 8))) [] 0
private def asmCbwLine : L := .asm (.cbw 1 2) [] 0
private def labelLine : L := .label 0 1 0
private def labAsmHaltLine : L := .labAsm .halt (w8 0) [] 0
private def asmBadRegLine : L := .asm (.asmi (.inst (.const 9 (w8 0)))) [] 0

private def secOk : S := { sectionId := 0, lines := [asmSkipLine] }
private def secBad : S := { sectionId := 0, lines := [asmBadRegLine] }
private def secEmpty : S := { sectionId := 0, lines := [] }
private def secLabel : S := { sectionId := 0, lines := [labelLine] }
private def secOk2 : S := { sectionId := 1, lines := [asmSkipLine] }

example : lineOkPreHOL cfg8 asmSkipLine := by
  rw [← lineOkB_iff]
  decide
example : lineOkPreHOL cfg8 asmCbwLine := by
  rw [← lineOkB_iff]
  decide
example : lineOkPreHOL cfg8 labelLine := by
  rw [← lineOkB_iff]
  decide
example : lineOkPreHOL cfg8 labAsmHaltLine := by
  rw [← lineOkB_iff]
  decide
example : ¬ lineOkPreHOL cfg8 asmBadRegLine := by
  rw [← lineOkB_iff]
  decide
example : allEncOkPreHOL cfg8 [secOk] := by
  rw [← allEncOkB_iff]
  decide
example : ¬ allEncOkPreHOL cfg8 [secBad] := by
  rw [← allEncOkB_iff]
  decide
example : secOkPreHOL cfg8 secOk := by
  rw [← secOkB_iff]
  decide
example : ¬ secOkPreHOL cfg8 secBad := by
  rw [← secOkB_iff]
  decide
example : secOkPreHOL cfg8 secEmpty := by
  rw [← secOkB_iff]
  decide
example : allEncOkPreHOL cfg8 [secLabel, secOk2] := by
  rw [← allEncOkB_iff]
  decide
example : allEncOkPreHOL cfg8 ([] : List S) := by
  rw [← allEncOkB_iff]
  decide
example : (match cbwToAsmHOL (.cbw 1 2) with
  | .inst (.mem .store8 2 (.addr 1 (0 : BitVec 8))) => true
  | _ => false) := rfl
example : (match cbwToAsmHOL (.shareMem .load 4 (.addr 5 (0 : BitVec 8))) with
  | .inst (.mem .load 4 (.addr 5 (0 : BitVec 8))) => true
  | _ => false) := rfl

private def cbwRowOk (instruction : AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8)) : Bool :=
  match cbwToAsmHOL instruction with
  | .inst (.mem .store8 2 (.addr 1 (0 : BitVec 8))) => true
  | .inst (.mem .load 4 (.addr 5 (0 : BitVec 8))) => true
  | _ => false

/-- The emitted base-line reductions of `line_ok_pre` at the concrete config,
mirroring the direct HOL oracle rows. -/
example : lineOkPreHOL cfg8 (.asm (.asmi (.inst (.skip : HolInst 8))) [] 0 : L) := by
  rw [← lineOkB_iff]
  decide

example : ¬ lineOkPreHOL cfg8 (.asm (.asmi (.inst (.const 9 (w8 0)))) [] 0 : L) := by
  rw [← lineOkB_iff]
  decide

example : lineOkPreHOL cfg8 (.label 0 1 0 : L) := by
  rw [← lineOkB_iff]
  decide

/-- The `flattenHOL` clause for `inst` embeds the instruction unchanged. -/
example : ∀ line ∈ appListAppend
    (flattenHOL true (.inst (.skip : HolInst 8)) 0 0 [] []).1,
    lineOkPreHOL cfg8 line :=
  flattenLineOkPreHOL true (.inst (.skip : HolInst 8)) 0 0 [] [] _ _ _ cfg8
    (by decide) (by simp [stackAsmOkExact, asmInstOkExact, asmRegOkExact, cfg8]) rfl

/-- The `flattenHOL` clause for `raise` emits the `JumpReg` line, whose
validity is exactly `asmRegOkExact`. -/
example : ∀ line ∈ appListAppend
    (flattenHOL true (.raise 2) 0 0 [] []).1,
    lineOkPreHOL cfg8 line :=
  flattenLineOkPreHOL true (.raise 2) 0 0 [] [] _ _ _ cfg8
    (by decide) (by simp [stackAsmOkExact, cfg8]) rfl

/-- The emitted `JumpReg` line's `line_ok_pre` is exactly `asmRegOkExact`,
as in the legacy `lineOkPreConfig_flattenOps_jumpReg` row. -/
example : lineOkPreHOL cfg8 (.asm (.asmi (.jumpReg 3)) [] 0 : L) ↔
    asmRegOkExact 3 cfg8 = true := by
  rw [← lineOkB_iff]
  decide

example : asmInstOkExact (.skip : HolInst 8) cfg8 = true := by decide

example (h : stackAsmOkExact cfg8 (.raise 2 : HolProg 8)) :
    (2 < cfg8.regCount ∧ 2 ∉ cfg8.avoidRegs) := by
  simpa [stackAsmOkExact] using h

example : (stackAsmOkExact cfg8 (.seq (.tick : HolProg 8) (.skip : HolProg 8))) ↔
    (stackAsmOkExact cfg8 (.tick : HolProg 8) ∧ stackAsmOkExact cfg8 (.skip : HolProg 8)) := by
  simp [stackAsmOkExact]

example : (stackAsmOkExact cfg8 (.loop (.skip : HolProg 8))) ↔
    stackAsmOkExact cfg8 (.skip : HolProg 8) := by
  simp [stackAsmOkExact]

example : (stackAsmOkExact cfg8
      (.call (some ((.skip : HolProg 8), 7, 1, 0)) (.inl 2)
        (some ((.tick : HolProg 8), 3, 4)) : HolProg 8)) ↔
    (stackAsmOkExact cfg8 (.skip : HolProg 8) ∧
      stackAsmOkExact cfg8 (.tick : HolProg 8)) := by
  simp [stackAsmOkExact]

/-- The top-level flat `flatten_line_ok_pre` fires on a concrete program. -/
example : ∀ line ∈ appListAppend
    (flattenHOL true (.tick : HolProg 8) 0 0 [] []).1,
    lineOkPreHOL cfg8 line :=
  flattenLineOkPreHOL true (.tick : HolProg 8) 0 0 [] [] _ _ _ cfg8
    (by decide) (by simp [stackAsmOkExact]) rfl

/-- The HOL-exact `append`-form `flatten_line_ok_pre` over `flattenApp` fires. -/
example : ∀ line ∈ appListAppend
    (flattenHOL true (.halt 0 : HolProg 8) 0 0 [] []).1,
    lineOkPreHOL cfg8 line :=
  flattenLineOkPreHOL true (.halt 0 : HolProg 8) 0 0 [] [] _ _ _ cfg8
    (by decide) (by simp [stackAsmOkExact]) rfl

/-- The HOL-exact `compile_all_enc_ok_pre` over `progToSectionHOL` fires. -/
example : allEncOkPreHOL cfg8
    ([(0, (.tick : HolProg 8))].map progToSectionHOL) :=
  compileAllEncOkPreHOL cfg8 [(0, (.tick : HolProg 8))] (by decide)
    (by intro entry member; simp at member; subst member; simp [stackAsmOkExact])

def runChecks : IO Bool := do
  let guards : List Bool :=
    [ decide (lineOkB asmSkipLine = true)
    , decide (lineOkB asmCbwLine = true)
    , decide (lineOkB labelLine = true)
    , decide (lineOkB labAsmHaltLine = true)
    , decide (lineOkB asmBadRegLine = false)
    , decide (allEncOkB [secOk] = true)
    , decide (allEncOkB [secBad] = false)
    , decide (secOkB secOk = true)
    , decide (secOkB secBad = false)
    , decide (secOkB secEmpty = true)
    , decide (allEncOkB [secLabel, secOk2] = true)
    , decide (allEncOkB ([] : List S) = true)
    , cbwRowOk (.cbw 1 2)
    , cbwRowOk (.shareMem .load 4 (.addr 5 0))
    ]
  let ok := guards.all id
  if ok then
    IO.println "PASS labProps line_ok_pre/all_enc_ok_pre over AsmConfigExact: 14 rows"
  else
    IO.println "FAIL labProps line_ok_pre/all_enc_ok_pre over concrete AsmConfigExact"
  pure ok

end Flapjack.Test.LabPropsLineOkPreParity
