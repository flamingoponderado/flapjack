import Flapjack.Compiler.Backend.LabToTarget.PositionalEncoding
namespace Flapjack.Test.LabToTargetPositionalEncodingParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [7,w]
  | .loc _ w => [8,w]
  | .call w => [9,w]
  | .inst .skip => [42]
  | _ => []
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def ffis : List HolFfiName := [.extCall (.implode [97]),.extCall (.implode []),.extCall (.implode [])]
example : lineEncd enc labs ffis 5 (.label 7 8 999) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.asm (.asmi (.inst .skip)) [42] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : ¬lineEncd enc labs ffis 5 (.asm (.asmi (.inst .skip)) [42] 2) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineLengthLeq (.asm (.asmi (.inst .skip)) [42] 2 : LabLineHOL 8) := by
  simp only [lineLengthLeq]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm .halt 99 [235] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm .install 99 [219] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm (.callFFI (.implode [])) 99 [187] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs [] 5 (.labAsm (.callFFI (.implode [])) 99 [203] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm (.jump (.lab 3 4)) 99 [5] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 3 4)) 99 [7,5] 2) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm (.locValue 2 (.lab 3 4)) 99 [8,5] 2) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 5 (.labAsm (.call (.lab 3 4)) 99 [9,5] 2) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : ¬lineEncd enc labs ffis 4 (.labAsm (.jump (.lab 3 4)) 99 [5] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : ¬lineEncd enc labs ffis 5 (.labAsm (.jump (.lab 3 4)) 99 [5] 0) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc .ln ffis 5 (.labAsm (.jump (.lab 3 4)) 99 [251] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : lineEncd enc labs ffis 260 (.labAsm (.jump (.lab 3 4)) 99 [6] 1) := by
  simp only [lineEncd]
  all_goals decide +kernel
example : linesEncd enc labs ffis 4 [.label 3 0 1,.asm (.asmi (.inst .skip)) [42] 1,.labAsm (.jump (.lab 3 4)) 99 [4] 1] := by
  simp only [linesEncd,lineEncd,lineLen]
  all_goals decide +kernel
example : allEncd enc labs ffis 4 [⟨3,[.label 3 0 1,.asm (.asmi (.inst .skip)) [42] 1]⟩,⟨4,[.labAsm (.jump (.lab 3 4)) 99 [4] 1]⟩] := by
  simp only [allEncd,linesEncd,lineEncd]
  all_goals decide +kernel
example : ¬allEncd enc labs ffis 4 [⟨3,[.label 3 0 1,.asm (.asmi (.inst .skip)) [42] 1]⟩,⟨4,[.labAsm (.jump (.lab 3 4)) 99 [5] 1]⟩] := by
  simp only [allEncd,linesEncd,lineEncd]
  all_goals decide +kernel
example : encLinesAgainSimp labs ffis 0 enc
    [.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 1] =
    ([.labAsm (.jump (.lab 3 4)) 10 [10] 1,.label 3 0 1],true) := by
  simp [encLinesAgainSimp,labs,enc,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encSecsAgain 0 labs ffis enc
    [⟨3,[.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 1]⟩,⟨4,[.labAsm (.jump (.lab 3 4)) 0 [0] 1]⟩] =
    ([⟨3,[.labAsm (.jump (.lab 3 4)) 10 [10] 1,.label 3 0 1]⟩,⟨4,[.labAsm (.jump (.lab 3 4)) 8 [8] 1]⟩],true) := by
  simp [encSecsAgain,encLinesAgain,labs,enc,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncd enc labs ffis pos line → lineLengthLeq line := lineEncd_lengthLeq enc labs ffis pos line

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncd enc labs ffis pos ls → ∀ line ∈ ls, lineLengthLeq line := linesEncd_lengthLeq enc labs ffis pos ls

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncd enc labs ffis pos ls → allLengthLeq ls := allEncd_lengthLeq enc labs ffis pos ls

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) ∧
      (∀ line ∈ lines, labelOne line) ∧ (∀ line ∈ lines, lineEncd0 enc line) →
    linesEncd enc labs ffis pos res := encLinesAgainSimp_encd labs ffis pos enc lines res

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encSecsAgain pos labs ffis enc ls = (res,true) ∧
      (∀ sec ∈ ls, secLabelOne sec) ∧ (∀ sec ∈ ls, secEncd0 enc sec) →
    allEncd enc labs ffis pos res := encSecsAgain_encd pos labs ffis enc ls res

def runChecks : IO Bool := do
  IO.println "PASS full positional encoding/output/length group (21 original observations, 5 full consumers)"
  pure true
end Flapjack.Test.LabToTargetPositionalEncodingParity
