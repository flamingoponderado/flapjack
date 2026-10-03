import Flapjack.Compiler.Backend.LabToTarget.FfiEntryExclusion
namespace Flapjack.Test.LabToTargetFfiEntryExclusionParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Misc
example {width : Nat} [NeZero width]
    {state projection : Type} (a : Nat)
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))
    (pos : Nat) (dm : BitVec width → Prop) (t : AsmState width)
    (ms : state) (ffiNames : List HolFfiName) (labs : Spt (Spt Nat)) (i : Nat)
    (mc : MachineConfig width state projection)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (progToBytes code).length < 2^width ∧
    mmioPcsMinIndex mc.ffiNames = some i ∧
    mc.ffiNames.length = mc.ffiEntryPcs.length ∧
    allEncOk mc.target.config labs ffiNames 0 code ∧ encOk mc.target.config ∧
    (∀ index, index < i →
      ¬ mc.progAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      ¬ mc.sharedAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.haltPc ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.ccachePc ∧
      findIndex (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms)
        mc.ffiEntryPcs 0 = some index) ∧
    bytesInMemHOL (mc.target.getPc ms) (progToBytes code) t.mem mc.progAddresses dm ∧
    asmFetchAux pos code = some line ∧ a < (lineBytes line).length →
    mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pos 0 code)
      ∉ mc.ffiEntryPcs.take i := asmFetch_notFfiEntryPcs a line pos dm t ms ffiNames labs i mc code
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }

private def guest := HolFfiName.extCall (ofString "guest")
private def inst : LabLineHOL 8 := .asm (.asmi (.inst .skip)) [0,0] 2
private def code : LabProgHOL 8 := [⟨1,[inst,inst]⟩]
private def actualMc (mc : MachineConfig 8 Unit Unit) (base : BitVec 8) : MachineConfig 8 Unit Unit :=
  { mc with
    target := { mc.target with
      config := cfg 1 [0,0]
      getPc := fun _ => base }
    ffiNames := [guest]
    ffiEntryPcs := [-48+base]
    progAddresses := fun x => x = base ∨ x = base+1 ∨ x = base+2 ∨ x = base+3
    sharedAddresses := fun _ => False
    haltPc := 100
    ccachePc := 101 }
private theorem configOk : encOk (cfg (width := 8) 1 [0,0]) := by
 simp [encOk,offsetMonotonic,cfg]

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 255).target.getPc () + BitVec.ofNat 8 0 + BitVec.ofNat 8 (posVal 0 0 code)
   ∉ (actualMc mc 255).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 0 inst 0 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 255) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 255).target.getPc () + BitVec.ofNat 8 1 + BitVec.ofNat 8 (posVal 0 0 code)
   ∉ (actualMc mc 255).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 1 inst 0 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 255) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 255).target.getPc () + BitVec.ofNat 8 0 + BitVec.ofNat 8 (posVal 1 0 code)
   ∉ (actualMc mc 255).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 0 inst 1 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 255) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 255).target.getPc () + BitVec.ofNat 8 1 + BitVec.ofNat 8 (posVal 1 0 code)
   ∉ (actualMc mc 255).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 1 inst 1 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 255) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 254).target.getPc () + BitVec.ofNat 8 1 + BitVec.ofNat 8 (posVal 1 0 code)
   ∉ (actualMc mc 254).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 1 inst 1 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 254) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 7).target.getPc () + BitVec.ofNat 8 0 + BitVec.ofNat 8 (posVal 0 0 code)
   ∉ (actualMc mc 7).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 0 inst 0 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 7) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide

example (mc : MachineConfig 8 Unit Unit) (t : AsmState 8) :
 (actualMc mc 7).target.getPc () + BitVec.ofNat 8 1 + BitVec.ofNat 8 (posVal 1 0 code)
   ∉ (actualMc mc 7).ffiEntryPcs.take 1 := by
  apply asmFetch_notFfiEntryPcs 1 inst 1 (fun _ => False)
    ({t with mem := fun _ => 0}) () [] .ln 1 (actualMc mc 7) code
  refine ⟨by cbv, ?_, by cbv, by cbv, configOk, ?_, by cbv, by cbv, by cbv⟩
  · simpa [actualMc] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
  · intro index hi
    have hz : index = 0 := by omega
    subst index
    cbv <;> decide
example : ¬ 2 < (lineBytes inst).length := by cbv
example : asmFetchAux 2 code = none := by cbv
end Flapjack.Test.LabToTargetFfiEntryExclusionParity
