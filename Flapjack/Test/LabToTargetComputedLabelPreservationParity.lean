import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelPreservation
namespace Flapjack.Test.LabToTargetComputedLabelPreservationParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def encode8 : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [0,0]
  | .jump w => [w,99]
  | _ => [10,11]
private def labs : Spt (Spt Nat) := sptInsert 1 (sptInsert 5 20 .ln) .ln
private def input : List (LabLineHOL 8) :=
  [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,
   .labAsm (.jump (.lab 1 5)) 99 [] 2,.label 1 6 0]
private def output : List (LabLineHOL 8) :=
  [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,
   .labAsm (.jump (.lab 1 5)) 14 [14,99] 2,.label 1 6 0]
private def acc : List (Nat × Nat) := [(5,2^80),(5,11),(0,99)]
private def initial : Spt (Spt Nat) :=
  sptInsert 7 (sptInsert 3 (2^80+7) .ln) (sptInsert 1 (sptInsert 9 77 .ln) .ln)
private def code : List (Section (LabLineHOL 8)) :=
  [⟨1,input⟩,⟨1,[]⟩,⟨2,[.label 2 3 1]⟩]
private def result : List (Section (LabLineHOL 8)) :=
  [⟨1,output⟩,⟨1,[]⟩,⟨2,[.label 2 3 1]⟩]
example : encLinesAgainSimp labs [] 4 encode8 input = (output,true) ∧
    sectionLabels 4 input acc = (8,(6,8)::(5,4)::acc) ∧
    sectionLabels 4 output acc = (8,(6,8)::(5,4)::acc) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encLinesAgainSimp labs [] 4 encode8 [.labAsm (.jump (.lab 1 5)) 16 [1] 2] =
    ([.labAsm (.jump (.lab 1 5)) 16 [1] 2],true) ∧
    sectionLabels 4 ([.labAsm (.jump (.lab 1 5)) 16 [1] 2] : List (LabLineHOL 8)) acc = (6,acc) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encLinesAgainSimp labs [] 3 encode8 [] = ([],true) ∧
    sectionLabels 3 ([] : List (LabLineHOL 8)) acc = (3,acc) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : sectionLabels 4 ([.label 1 0 3,.label 1 5 1] : List (LabLineHOL 8)) acc =
    (8,(5,8)::acc) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encSecsAgain 4 labs [] encode8 code = (result,true) ∧
    computeLabelsAlt 4 result initial = computeLabelsAlt 4 code initial ∧
    computeLabelsAlt 4 code initial =
      sptInsert 2 (sptFromAList [(0,8),(3,9)])
        (sptInsert 1 (sptFromAList [(0,8)]) initial) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : 7 ∉ code.map (fun sec => sec.sectionId) ∧
    labLookup 7 3 (computeLabelsAlt 4 code initial) = some (2^80+7) ∧
    labLookup 7 3 initial = some (2^80+7) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : 13 ∉ code.map (fun sec => sec.sectionId) ∧
    labLookup 13 3 (computeLabelsAlt 4 code initial) = none ∧
    labLookup 13 3 initial = none := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : labLookup 1 9 initial = some 77 ∧
    labLookup 1 9 (computeLabelsAlt 4 code initial) = none := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encLinesAgainSimp labs [] 4 encode8
    [.labAsm (.jump (.lab 1 5)) 99 [] 0,.label 1 6 0] =
    ([.labAsm (.jump (.lab 1 5)) 16 [16,99] 2,.label 1 6 0],false) ∧
    sectionLabels 4 ([.labAsm (.jump (.lab 1 5)) 99 [] 0,.label 1 6 0] : List (LabLineHOL 8)) [] = (4,[(6,4)]) ∧
    sectionLabels 4 ([.labAsm (.jump (.lab 1 5)) 16 [16,99] 2,.label 1 6 0] : List (LabLineHOL 8)) [] = (6,[(6,6)]) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encLinesAgainSimp (.ln : Spt (Spt Nat)) [] 0 (fun _ : HolAsm 1 => [3,4])
    [.labAsm .halt 1 [] 2,.label 1 7 0] = ([.labAsm .halt 0 [3,4] 2,.label 1 7 0],true) ∧
    sectionLabels 0 ([.labAsm .halt 0 [3,4] 2,.label 1 7 0] : List (LabLineHOL 1)) [] = (2,[(7,2)]) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel
example : encLinesAgainSimp (.ln : Spt (Spt Nat)) [] (2^80+4) (fun _ : HolAsm 80 => [])
    [.label 1 7 0] = ([.label 1 7 0],true) ∧
    sectionLabels (2^80+4) ([.label 1 7 0] : List (LabLineHOL 80)) [(8,2^81)] =
    (2^80+4,[(7,2^80+4),(8,2^81)]) := by
  simp [encLinesAgainSimp,encSecsAgain,encLinesAgain,sectionLabels,computeLabelsAlt,
    getJumpOffset,getLabel,labInst,findPos,lookupAny,labLookup,labs,sptLookup,sptInsert,
    input,output,acc,code,result,encode8] <;> first | rfl | decide +kernel

example {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) (n1 n2 : Nat) :
    n1 ∉ code.map (fun sec => sec.sectionId) →
    labLookup n1 n2 (computeLabelsAlt pos code acc) = labLookup n1 n2 acc := labLookup_computeLabelsAlt_ignore pos code acc n1 n2

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) →
    sectionLabels pos lines acc = sectionLabels pos res acc := encLinesAgain_sectionLabels labs ffis pos enc lines res acc

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) :
    encSecsAgain pos labs ffis enc code = (res,true) →
    computeLabelsAlt pos res acc = computeLabelsAlt pos code acc := encSecsAgain_computeLabels pos labs ffis enc code res acc

def runChecks : IO Bool := do
  IO.println "PASS full computed-label encoding preservation (11 original observations, 3 full consumers)"
  pure true
end Flapjack.Test.LabToTargetComputedLabelPreservationParity
