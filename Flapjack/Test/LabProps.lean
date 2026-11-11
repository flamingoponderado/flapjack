module

public import Flapjack.Compiler.Backend.LabProps
public import Flapjack.Compiler.Backend.LabProps.Native
public import Flapjack.Compiler.Backend.LabToTarget.Native
public import Flapjack.Compiler.Backend.LabSem.State

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.LabLang
public meta import Flapjack.Compiler.Backend.LabProps.Native
public meta import Flapjack.Compiler.Backend.LabToTarget.Native
@[expose] public section

namespace Flapjack.Test.LabProps

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

/-- Concrete assembler configuration mirroring the probe fixture: eight
registers, no avoided register, and unit-width offset bounds. -/
private def cfg : AsmConfigExact 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := []
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

private abbrev L := Flapjack.Compiler.Backend.LabSem.LabLineHOL 8
private abbrev S := Flapjack.Compiler.Backend.LabSem.LabSectionHOL 8

private def asmLine (instruction : AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8)) : L :=
  .asm instruction [] 99

private def labOnlySection : S :=
  { sectionId := 3
    lines := [.label 3 1 0, .labAsm .halt 0 [] 0] }

private def cbwSection : S :=
  { sectionId := 4
    lines := [asmLine (.cbw 1 2), .label 4 1 0] }

private def badRegLine : L :=
  .asm (.asmi (.inst (.mem .load 9 (.addr 2 (w8 0))))) [] 99

/-- Kernel-checkable Bool view of the reviewed `lineOkPreHOL` Prop: the same
clause `lineOkPreHOL` states, read at this fixture's exact carriers. -/
private def lineOkB (line : L) : Bool :=
  match line with
  | .asm instruction _ _ => asmOkExact (width := 8) (cbwToAsmHOL (width := 8) instruction) cfg
  | _ => true

private def secOkB (sec : S) : Bool := sec.lines.all lineOkB

private def allEncOkB (sections : List S) : Bool := sections.all secOkB

#guard (match cbwToAsmHOL (.asmi (.inst (.skip : HolInst 8))) with
  | .inst .skip => true
  | _ => false)
#guard (match cbwToAsmHOL (.cbw 1 2) with
  | .inst (.mem .store8 2 (.addr 1 (0 : BitVec 8))) => true
  | _ => false)
#guard (match cbwToAsmHOL (.shareMem .load 4 (.addr 5 (0 : BitVec 8))) with
  | .inst (.mem .load 4 (.addr 5 (0 : BitVec 8))) => true
  | _ => false)

#guard lineOkB (asmLine (.asmi (.inst .skip)))
#guard lineOkB (asmLine (.cbw 1 2))
#guard lineOkB (asmLine (.shareMem .load 4 (.addr 5 0)))
#guard !lineOkB badRegLine
#guard lineOkB (.label 1 2 3 : L)
#guard lineOkB (.labAsm .halt 0 [] 0 : L)

#guard secOkB labOnlySection
#guard secOkB cbwSection
#guard allEncOkB [labOnlySection, cbwSection]
#guard allEncOkB ([] : List S)
#guard !allEncOkB [cbwSection,
  { sectionId := 5, lines := [badRegLine] }]

end Flapjack.Test.LabProps
