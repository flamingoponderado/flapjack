import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
namespace Flapjack.Test.StackToLabFullEncodingParity
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm

example {width : Nat} [NeZero width]
    (tail : Bool) (program : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config program)
    (result : flattenHOL tail program sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreHOL tail program sectionId next conts breaks lines done nextAfter config zero valid result

example {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (programs : List (Nat × HolProg width))
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : ∀ entry ∈ programs, stackAsmOkExact config entry.2) :
    allEncOkPreHOL config (programs.map progToSectionHOL) :=
  compileAllEncOkPreHOL config programs zero valid

private def cfg : AsmConfigExact 8 where
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
  addrOffset := (0,100)
  hwOffset := (0,100)
  byteOffset := (0,100)
  jumpOffset := (0,100)
  cjumpOffset := (0,100)
  locOffset := (0,100)


-- Same-input original oracle group: all recursive constructors and native Cbw.
private def programs : List (Nat × HolProg 8) :=
  [(7, .seq (.codeBufferWrite 1 2) .tick),
   (8, .loop (.break 0)),
   (9, .ite .less 3 (.reg 4) .tick .skip),
   (10, .call (some (.tick, 3, 8, 9)) (.inr 4) (some (.tick, 10, 11)))]

example : allEncOkPreHOL cfg (programs.map progToSectionHOL) := by
  exact compileAllEncOkPreHOL cfg programs
    (by decide +kernel)
    (by simp [programs, stackAsmOkExact, cfg])

-- Every line, byte cache, length, and label matches full_compile_all_sections.
example : programs.map progToSectionHOL =
    [⟨7, [.asm (.cbw 1 2) [] 0, .label 7 1 0,
      .asm (.asmi (.inst .skip)) [] 0, .label 7 2 0]⟩,
     ⟨8, [.label 8 2 0, .labAsm (.jump (.lab 8 3)) 0 [] 0,
      .labAsm (.jump (.lab 8 2)) 0 [] 0, .label 8 3 0, .label 8 1 0]⟩,
     ⟨9, [.labAsm (.jumpCmp .notLess 3 (.reg 4) (.lab 9 2)) 0 [] 0,
      .asm (.asmi (.inst .skip)) [] 0, .label 9 2 0, .label 9 1 0]⟩,
     ⟨10, [.labAsm (.locValue 3 (.lab 8 9)) 0 [] 0,
      .asm (.asmi (.jumpReg 4)) [] 0, .label 8 9 0,
      .asm (.asmi (.inst .skip)) [] 0,
      .labAsm (.jump (.lab 10 13)) 0 [] 0, .label 10 11 0,
      .asm (.asmi (.inst .skip)) [] 0, .label 10 13 0, .label 10 1 0]⟩] := by
  simp [programs, progToSectionHOL, flattenHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab,
    appListAppend, appendAux, isSeqHOL, stackIsSkip, negateHOL, compileJumpHOL, findLabHOL]

end Flapjack.Test.StackToLabFullEncodingParity
