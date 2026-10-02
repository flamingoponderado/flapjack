import Flapjack.Compiler.Backend.LabToTarget.EndingLabels
namespace Flapjack.Test.LabToTargetUpdatePadEndingParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabProps

example {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos code, secEndsWithLabelNative sec := updLabLen_endsWithLabel pos code

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ padCode nop code, secEndsWithLabelNative sec := padCode_endsWithLabel nop code


private def labelCode {width : Nat} [NeZero width] : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) := [⟨1,[.label 1 7 2]⟩]
example : ∀ sec ∈ updLabLen (width := 8) 3 [], secEndsWithLabelNative sec := by simp [updLabLen]
example : ∀ sec ∈ padCode (width := 8) [] [], secEndsWithLabelNative sec := by simp [padCode]
example : ∀ sec ∈ updLabLen (width := 8) 3 [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.label 1 7 0]⟩], secEndsWithLabelNative sec := by
  apply updLabLen_endsWithLabel
  simp [secEndsWithLabelNative,isLabelHOL]
example : ∀ sec ∈ padCode (width := 8) [0] [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.label 1 7 1]⟩], secEndsWithLabelNative sec := by
  apply padCode_endsWithLabel
  simp [secEndsWithLabelNative,isLabelHOL]
example : ∀ sec ∈ padCode (width := 8) [] [⟨1,[.label 1 7 0]⟩], secEndsWithLabelNative sec := by
  apply padCode_endsWithLabel
  simp [secEndsWithLabelNative,isLabelHOL]
example : (¬∀ sec ∈ updLabLen (width := 8) 0 [⟨1,[.asm (.asmi (.inst .skip)) [] 0]⟩], secEndsWithLabelNative sec) ∧
    (¬∀ sec ∈ padCode (width := 8) [0] [⟨1,[.asm (.asmi (.inst .skip)) [] 0]⟩], secEndsWithLabelNative sec) := by
  simp [updLabLen,linesUpdLabLen,padCode,padSection,secEndsWithLabelNative,isLabelHOL]
example : ∀ sec ∈ updLabLen 3 (labelCode (width := 1)), secEndsWithLabelNative sec := by
  apply updLabLen_endsWithLabel
  simp [labelCode,secEndsWithLabelNative,isLabelHOL]
example : ∀ sec ∈ updLabLen 1208925819614629174706176 (labelCode (width := 80)), secEndsWithLabelNative sec := by
  apply updLabLen_endsWithLabel
  simp [labelCode,secEndsWithLabelNative,isLabelHOL]
end Flapjack.Test.LabToTargetUpdatePadEndingParity
