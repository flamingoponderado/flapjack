import Flapjack.Compiler.Backend.LabToTarget.CodeNopEncoding
namespace Flapjack.Test.LabToTargetCodeNopEncodingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc1 : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [w]
  | .loc _ w => [w]
  | _ => [0]
private def enc2 : HolAsm 8 → List (BitVec 8)
  | .jump w => [w,w]
  | .jumpCmp _ _ _ w => [w,w]
  | .loc _ w => [w,w]
  | _ => [0,0]
private def code1 : List (Section (LabLineHOL 8)) := [⟨0,[]⟩,
  ⟨3,[.label 3 1 0,.labAsm (.jump (.lab 3 1)) 77 [251] 3,.label 3 2 1,.asm (.asmi (.inst .skip)) [0] 1]⟩,
  ⟨4,[.labAsm .halt 88 [230] 2,.labAsm (.call (.lab 3 1)) 99 [0] 3]⟩,⟨5,[]⟩]
private def code2 : List (Section (LabLineHOL 8)) := [⟨0,[]⟩,
  ⟨3,[.label 3 1 0,.labAsm (.jump (.lab 3 1)) 77 [251,251] 6]⟩,
  ⟨4,[.labAsm .halt 88 [229,229] 4,.labAsm (.call (.lab 3 1)) 99 [0,0] 6]⟩,⟨5,[]⟩]
private theorem guards1 : 0<([0] : List (BitVec 8)).length ∧ [0]=enc1 (.inst .skip) ∧
    (([0] : List (BitVec 8)).length≠1 → (∀ sec ∈ code1,secAligned 1 sec) ∧ (∀ sec ∈ code1,secLabelZero sec)) ∧
    (∀ sec ∈ code1,secLabelOne sec) ∧ allLengthLeq code1 ∧
    (∀ sec ∈ code1,secLabelPrefixZero sec) ∧ allEncd enc1 .ln [] 5 code1 := by
  refine ⟨by decide +kernel,rfl,by simp,?_,?_,?_,?_⟩
  · simp [code1,secLabelOne,labelOne]
  · simp [code1,allLengthLeq,secLengthLeq,lineLengthLeq]
  · simp [code1,secLabelPrefixZero,isLabelHOL,lineLen]
  · simp only [code1,allEncd,linesEncd,lineEncd,lineLen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    decide +kernel
private theorem guards2 : 0<([0,0] : List (BitVec 8)).length ∧ [0,0]=enc2 (.inst .skip) ∧
    (([0,0] : List (BitVec 8)).length≠1 → (∀ sec ∈ code2,secAligned 2 sec) ∧ (∀ sec ∈ code2,secLabelZero sec)) ∧
    (∀ sec ∈ code2,secLabelOne sec) ∧ allLengthLeq code2 ∧
    (∀ sec ∈ code2,secLabelPrefixZero sec) ∧ allEncd enc2 .ln [] 5 code2 := by
  refine ⟨by decide +kernel,rfl,?_,?_,?_,?_,?_⟩
  · intro _
    constructor
    · simp [code2,secAligned,lineAligned,lineLen,lineLength]
    · simp [code2,secLabelZero,labelZero]
  · simp [code2,secLabelOne,labelOne]
  · simp [code2,allLengthLeq,secLengthLeq,lineLengthLeq]
  · simp [code2,secLabelPrefixZero,isLabelHOL,lineLen]
  · simp only [code2,allEncd,linesEncd,lineEncd,lineLen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    decide +kernel
example : allEncWithNop enc1 .ln [] 5 (padCode [0] code1) := allEncWithNop_padCode enc1 .ln [] [0] code1 5 guards1
example : allEncWithNop enc2 .ln [] 5 (padCode [0,0] code2) := allEncWithNop_padCode enc2 .ln [] [0,0] code2 5 guards2
example : padCode [0] code1 = [⟨0,[]⟩,
    ⟨3,[.label 3 1 0,.labAsm (.jump (.lab 3 1)) 77 [251,0,0,0] 4,.label 3 2 0,.asm (.asmi (.inst .skip)) [0] 1]⟩,
    ⟨4,[.labAsm .halt 88 [230,0] 2,.labAsm (.call (.lab 3 1)) 99 [0,0,0] 3]⟩,⟨5,[]⟩] := rfl
example : padCode [0,0] code2 = [⟨0,[]⟩,
    ⟨3,[.label 3 1 0,.labAsm (.jump (.lab 3 1)) 77 [251,251,0,0,0,0] 6]⟩,
    ⟨4,[.labAsm .halt 88 [229,229,0,0] 4,.labAsm (.call (.lab 3 1)) 99 [0,0,0,0,0,0] 6]⟩,⟨5,[]⟩] := rfl
example : (padCode [0] code1).map (fun s => (s.lines.map lineLength).sum) = [0,5,5,0] := rfl
example : (padCode [0,0] code2).map (fun s => (s.lines.map lineLength).sum) = [0,6,10,0] := rfl
example : allEncWithNop enc2 .ln [] 17 (padCode [0,0] []) :=
  allEncWithNop_padCode enc2 .ln [] [0,0] [] 17 ⟨by decide +kernel,rfl,by simp,by simp,by simp [allLengthLeq],by simp,trivial⟩
example : allEncWithNop enc2 .ln [] 17 (padCode [0,0] [⟨7,[]⟩,⟨8,[]⟩]) := by
  apply allEncWithNop_padCode enc2 .ln [] [0,0] _ 17
  refine ⟨by decide +kernel,rfl,?_,?_,?_,?_,?_⟩
  · simp [secAligned,secLabelZero]
  · simp [secLabelOne]
  · simp [allLengthLeq,secLengthLeq]
  · simp [secLabelPrefixZero]
  · simp [allEncd,linesEncd]
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    0<nop.length ∧ nop=enc (.inst .skip) ∧
    (nop.length≠1 → (∀ sec ∈ code,secAligned nop.length sec) ∧ (∀ sec ∈ code,secLabelZero sec)) ∧
    (∀ sec ∈ code,secLabelOne sec) ∧ allLengthLeq code ∧ (∀ sec ∈ code,secLabelPrefixZero sec) ∧
    allEncd enc labs ffis pos code → allEncWithNop enc labs ffis pos (padCode nop code) :=
  allEncWithNop_padCode enc labs ffis nop code pos

def runChecks : IO Bool := do
  IO.println "PASS full code padding NOP invariant (10 original observations; single/multibyte full guards, later section offsets, stored tuples, empty sections/code)"
  pure true
end Flapjack.Test.LabToTargetCodeNopEncodingParity
