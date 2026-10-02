import Flapjack.Compiler.Backend.LabToTarget.PaddingLabels
namespace Flapjack.Test.LabToTargetPaddingCodeLabelsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabSem
example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) :
    (∀ sec ∈ code, secLabelOne sec) ∧
    (nop.length ≠ 1 → ∀ sec ∈ code, secLabelZero sec) ∧
    (∀ sec ∈ code, secLabelPrefixZero sec) ∧ allLabLenPosOk pos code →
    computeLabelsAlt pos (padCode nop code) acc = computeLabelsAlt pos code acc := padCode_computeLabels nop pos code acc

private def code {width : Nat} [NeZero width] : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]⟩]
private def zeroCode : List (Section (LabLineHOL 8)) :=
  [⟨1,[.asm (.asmi (.inst .skip)) [] 2,.label 1 7 0]⟩]
example : computeLabelsAlt (width := 8) 3 (padCode [] []) (sptInsert 42 (sptInsert 7 99 .ln) .ln) =
    sptInsert 42 (sptInsert 7 99 .ln) .ln := rfl
example : computeLabelsAlt 0 (padCode [0] (code (width := 8))) (sptInsert 42 (sptInsert 7 99 .ln) .ln) =
    computeLabelsAlt 0 (code (width := 8)) (sptInsert 42 (sptInsert 7 99 .ln) .ln) := by decide +kernel
example : computeLabelsAlt 0 (padCode [0,1] zeroCode) .ln = computeLabelsAlt 0 zeroCode .ln := by decide +kernel
example : computeLabelsAlt 0 (padCode [] zeroCode) .ln = computeLabelsAlt 0 zeroCode .ln := by decide +kernel
example : computeLabelsAlt (width := 8) 0 (padCode [0]
    [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]⟩,⟨2,[.label 2 9 0,.asm (.asmi (.inst .skip)) [] 1,.label 2 5 1]⟩]) .ln =
    computeLabelsAlt (width := 8) 0 [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]⟩,⟨2,[.label 2 9 0,.asm (.asmi (.inst .skip)) [] 1,.label 2 5 1]⟩] .ln := by decide +kernel
example : computeLabelsAlt (width := 8) 0 (padCode [0]
    [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]⟩,⟨1,[.asm (.asmi (.inst .skip)) [] 2,.label 1 9 0]⟩]) (sptInsert 1 (sptInsert 7 99 .ln) .ln) =
    computeLabelsAlt (width := 8) 0 [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]⟩,⟨1,[.asm (.asmi (.inst .skip)) [] 2,.label 1 9 0]⟩] (sptInsert 1 (sptInsert 7 99 .ln) .ln) := by decide +kernel
example : computeLabelsAlt (width := 8) 0 (padCode [0] [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 0 1]⟩]) .ln =
    computeLabelsAlt (width := 8) 0 [⟨1,[.asm (.asmi (.inst .skip)) [] 1,.label 1 0 1]⟩] .ln := by decide +kernel
example : (¬∀ sec ∈ ([⟨1,[.label 1 7 1]⟩] : List (Section (LabLineHOL 8))),secLabelPrefixZero sec) ∧
    computeLabelsAlt (width := 8) 1 (padCode [0] [⟨1,[.label 1 7 1]⟩]) .ln ≠
      computeLabelsAlt (width := 8) 1 [⟨1,[.label 1 7 1]⟩] .ln := by
  constructor
  · simp [secLabelPrefixZero,isLabelHOL,lineLen]
  · decide +kernel
example : ¬∀ sec ∈ (code (width := 8)),secLabelZero sec := by simp [code,secLabelZero,labelZero]
example : computeLabelsAlt 0 (padCode [0] (code (width := 1))) .ln = computeLabelsAlt 0 (code (width := 1)) .ln := by decide +kernel
example : computeLabelsAlt 1208925819614629174706176 (padCode [0] (code (width := 80))) (sptInsert 42 (sptInsert 7 1208925819614629174706177 .ln) .ln) =
    computeLabelsAlt 1208925819614629174706176 (code (width := 80)) (sptInsert 42 (sptInsert 7 1208925819614629174706177 .ln) .ln) := by decide +kernel
-- Genuine full theorem application: source guards derive the target map equality.
example (acc : Spt (Spt Nat)) :
    computeLabelsAlt 0 (padCode [0] (code (width := 8))) acc = computeLabelsAlt 0 (code (width := 8)) acc := by
  apply padCode_computeLabels
  simp [code,secLabelOne,labelOne,secLabelPrefixZero,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL]
end Flapjack.Test.LabToTargetPaddingCodeLabelsParity
