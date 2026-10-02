import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsLoop
namespace Flapjack.Test.LabToTargetRemoveLabelsLoopParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (code output : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (labs : Spt (Spt Nat)) :
    removeLabelsLoop clock c pos acc ffis code = some (output,labs) ∧
    (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
    (∀ sec ∈ code,secLabelsOk sec) ∧ (code.map Section.sectionId).Nodup ∧
    (∀ sec ∈ code,(extractLabels sec.lines).Nodup) ∧
    Disjoint (sptDomain acc) {n | n ∈ code.map Section.sectionId} ∧
    restrictNonzero (getLabels code) ⊆ getCodeLabels code ∪ labsDomain acc ∧
    allEncOkPreHOL c code ∧ allEncd0 c.encode code ∧ encOk c ∧ pos % 2 = 0 ∧
    (∀ sid lid,match labLookup sid lid acc with
      | none => True
      | some value => value % 2 = 0) →
    allEncOkPreHOL c output ∧ (∀ sec ∈ output,secLabelsOk sec) ∧
    allEncOk c labs ffis pos output ∧ codeSimilar code output ∧
    (hasOddInst output → c.codeAlignment = 0) ∧
    (∀ sid lid value,labLookup sid lid labs = some value → value % 2 = 0) ∧
    (∀ sid lid value,labLookup sid lid acc = some value → labLookup sid lid labs = some value) ∧
    (∀ sid lid pc,locToPc sid lid code = some pc →
      labLookup sid lid labs = some (posVal pc pos output)) := removeLabelsLoop_correct clock c pos acc ffis code output labs
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
example {width : Nat} [NeZero width] (clock pos : Nat) (c : AsmConfigExact width)
    (acc : Spt (Spt Nat)) (ffis : List HolFfiName) :
    removeLabelsLoop clock c pos acc ffis [] = some ([],acc) := by
  rw [removeLabelsLoop.eq_def]
  simp [computeLabelsAlt,encSecsAgain,updLabLen,padCode,allEncOkLight,zeroLabsAccExist,getZeroLabsAcc,sptToAList,sptFoldi]
example : removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln [] [] = some ([],.ln) := by cbv
example : removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln []
    [⟨1,[.labAsm .halt 99 [] 0,.label 1 7 0]⟩] = none := by cbv
example : (removeLabelsLoop 1 (cfg (width := 8) 0 [0]) 18 .ln []
    [⟨1,[.labAsm .halt 99 [] 0,.label 1 7 0]⟩]).map (fun r => labLookup 1 7 r.2) = some (some 20) := by cbv
example : (removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln []
    [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.label 1 7 0]⟩]).map (fun r => progToBytes r.1) = some [0,0] := by cbv
example : (removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln []
    [⟨1,[.label 1 7 0]⟩]).map (fun r => labLookup 1 7 r.2) = some (some 18) := by cbv
example : removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln []
    [⟨1,[.labAsm (.call (.lab 1 7)) 0 [0] 1,.label 1 7 0]⟩] = none := by cbv
example : removeLabelsLoop 0 (cfg (width := 1) 0 [0]) 1208925819614629174706176 .ln [] [] = some ([],.ln) := by cbv
example : removeLabelsLoop 0 (cfg (width := 80) 0 [0]) 1208925819614629174706176 .ln [] [] = some ([],.ln) := by cbv
private def actualCode : List (Section (LabLineHOL 8)) :=
  [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.label 1 7 0]⟩]
private def actualOutput : List (Section (LabLineHOL 8)) :=
  [⟨1,[.asm (.asmi (.inst .skip)) [0,0] 2,.label 1 7 0]⟩]
private def actualLabs := computeLabelsAlt 18 (updLabLen 18 actualCode) .ln
/-- Genuine consumer: obtain validity and the physical label position from the
complete theorem after discharging every original guard on an executed program. -/
example : allEncOk (cfg (width := 8) 0 [0]) actualLabs [] 18 actualOutput ∧
    labLookup 1 7 actualLabs = some (posVal 1 18 actualOutput) := by
  have hfull := removeLabelsLoop_correct 0 (cfg (width := 8) 0 [0]) 18 .ln []
    actualCode actualOutput actualLabs
  have hexec : removeLabelsLoop 0 (cfg (width := 8) 0 [0]) 18 .ln [] actualCode =
      some (actualOutput,actualLabs) := by cbv
  have hguards := hfull ⟨hexec,?_,?_,?_,?_,?_,?_,?_,?_,?_,by decide +kernel,?_⟩
  · exact ⟨hguards.2.2.1,hguards.2.2.2.2.2.2.2 1 7 1 (by decide +kernel)⟩
  · simp [actualCode,secEndsWithLabelNative,isLabelHOL]
  · simp [actualCode,secLabelsOk,secLabelOk]
  · decide +kernel
  · decide +kernel
  · apply Set.disjoint_left.mpr
    intro n hn _
    change (sptLookup n (Spt.ln : Spt (Spt Nat))).isSome = true at hn
    rw [sptLookup] at hn
    contradiction
  · intro label hl
    simp [actualCode,restrictNonzero,getLabels,secGetLabels,lineGetLabels] at hl
  · simp [actualCode,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL,asmOkExact,cfg]
    decide +kernel
  · simp [actualCode,allEncd0,secEncd0,lineEncd0,cfg]
  · simp [encOk,cfg,offsetMonotonic]
  · intro sid lid
    simp [labLookup,sptLookup]

end Flapjack.Test.LabToTargetRemoveLabelsLoopParity
