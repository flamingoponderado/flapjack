import Flapjack.Compiler.Backend.LabToTarget.LabelPositionEncoding
namespace Flapjack.Test.LabToTargetLabelPositionEncodingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8) := fun _ => [7,8]
private def grow : HolAsm 8 → List (BitVec 8) := fun _ => [7,8,9,10]
private def lines : List (LabLineHOL 8) := [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,
  .labAsm .halt 77 [9] 3,.label 1 4 0]
private def result : List (LabLineHOL 8) := [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,
  .labAsm .halt (getJumpOffset (regImmWidth := 8) .halt [] .ln 5) [7,8] 3,.label 1 4 0]
private def code : List (Section (LabLineHOL 8)) := [⟨7,lines⟩,⟨8,[.label 1 9 0]⟩,⟨9,[]⟩]
private def codeResult : List (Section (LabLineHOL 8)) := [⟨7,result⟩,⟨8,[.label 1 9 0]⟩,⟨9,[]⟩]
example : encLinesAgainSimp .ln [] 1 enc lines = (result,true) := rfl
example : labLenPosOk 1 lines ∧ labLenPosOk 1 result := by
  refine ⟨by simp [lines,labLenPosOk,lineLabLenPosOk,lineLen],?_⟩
  exact encLinesAgainSimp_posOk .ln [] 1 enc lines result ⟨rfl,by simp [lines,labLenPosOk,lineLabLenPosOk,lineLen]⟩
example : (encLinesAgainSimp .ln [] 1 grow lines).2 = false := rfl
example : ¬labLenPosOk 1 (encLinesAgainSimp .ln [] 1 grow lines).1 := by
  simp [encLinesAgainSimp,lines,grow,getJumpOffset,ffiOffset,labLenPosOk,lineLabLenPosOk,lineLen]
example : encLinesAgainSimp .ln [] 1 enc result = (result,true) := rfl
example : encLinesAgainSimp (width := 8) .ln [] 0 enc [.label 1 2 99] = ([.label 1 2 99],true) ∧
    ¬labLenPosOk (width := 8) 0 [.label 1 2 99] := ⟨rfl,by simp [labLenPosOk,lineLabLenPosOk]⟩
example : encSecsAgain 1 .ln [] enc code = (codeResult,true) := rfl
example : allLabLenPosOk 1 code ∧ allLabLenPosOk 1 codeResult := by
  have hp : allLabLenPosOk 1 code := by simp [code,lines,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,secLength]
  exact ⟨hp,encSecsAgain_posOk 1 .ln [] enc code codeResult ⟨rfl,hp⟩⟩
example : encLinesAgainSimp (width := 1) .ln [] 17 (fun _ => []) [] = ([],true) := rfl
example : encSecsAgain 17 .ln [] enc [⟨7,[]⟩,⟨8,[]⟩] = ([⟨7,[]⟩,⟨8,[]⟩],true) := rfl
example : encLinesAgainSimp (width := 80) .ln [] (2^80+1) (fun _ => [7,8])
    [.label 1 2 1,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 4 1] =
    ([.label 1 2 1,.labAsm .halt (getJumpOffset (regImmWidth := 80) .halt [] .ln (2^80+2)) [7,8] 3,.label 1 4 1],true) := rfl
example : labLenPosOk (width := 80) (2^80+1) (encLinesAgainSimp .ln [] (2^80+1) (fun _ => [7,8])
    [.label 1 2 1,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 4 1]).1 := by
  apply encLinesAgainSimp_posOk _ _ _ _ _ _
  exact ⟨rfl,by simp [labLenPosOk,lineLabLenPosOk,lineLen]⟩
example {width : Nat} [NeZero width] (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (enc : HolAsm width → List (BitVec 8)) (lines res : List (LabLineHOL width)) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) ∧ labLenPosOk pos lines →
      labLenPosOk pos res := encLinesAgainSimp_posOk labs ffis pos enc lines res
example {width : Nat} [NeZero width] (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (code res : List (Section (LabLineHOL width))) :
    encSecsAgain pos labs ffis enc code = (res,true) ∧ allLabLenPosOk pos code →
      allLabLenPosOk pos res := encSecsAgain_posOk pos labs ffis enc code res

def runChecks : IO Bool := do
  IO.println "PASS full repeated encoder parity preservation (12 original observations, full success guards, growth counterexample, arbitrary widths and full theorem consumers)"
  pure true
end Flapjack.Test.LabToTargetLabelPositionEncodingParity
