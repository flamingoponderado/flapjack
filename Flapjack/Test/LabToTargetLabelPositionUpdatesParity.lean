import Flapjack.Compiler.Backend.LabToTarget.LabelPositionUpdates
namespace Flapjack.Test.LabToTargetLabelPositionUpdatesParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) := [.label 1 2 97,.label 1 3 99,
  .asm (.asmi (.inst .skip)) [7] 3,.labAsm (.call (.lab 1 2)) 77 [8,9] 2,.label 1 4 7]
private def code : List (Section (LabLineHOL 8)) := [⟨7,lines⟩,
  ⟨8,[.label 1 9 99,.asm (.asmi (.inst .skip)) [] 1,.label 1 10 77]⟩,⟨9,[]⟩]
example : linesUpdLabLen 1 lines [] = ([.label 1 2 1,.label 1 3 0,
    .asm (.asmi (.inst .skip)) [7] 3,.labAsm (.call (.lab 1 2)) 77 [8,9] 2,.label 1 4 1],8) := rfl
example : labLenPosOk 1 (linesUpdLabLen 1 lines []).1 := linesUpdLabLen_posOk 1 lines
example : linesUpdLabLen 0 lines [] = ([.label 1 2 0,.label 1 3 0,
    .asm (.asmi (.inst .skip)) [7] 3,.labAsm (.call (.lab 1 2)) 77 [8,9] 2,.label 1 4 1],6) := rfl
example : labLenPosOk 0 (linesUpdLabLen 0 lines []).1 := linesUpdLabLen_posOk 0 lines
example : linesUpdLabLen (width := 8) 3 [.label 1 2 97,.label 1 3 99,.label 1 4 123] [] =
    ([.label 1 2 1,.label 1 3 0,.label 1 4 0],4) := rfl
example : (linesUpdLabLen (width := 8) 3 [.asm (.asmi (.inst .skip)) [] 99,.labAsm .halt 77 [7] 37] []).1 =
    [.asm (.asmi (.inst .skip)) [] 99,.labAsm .halt 77 [7] 37] := rfl
example : linesUpdLabLen (width := 1) 99 [] [] = ([],99) := rfl
example : updLabLen 1 code = [⟨7,[.label 1 2 1,.label 1 3 0,
    .asm (.asmi (.inst .skip)) [7] 3,.labAsm (.call (.lab 1 2)) 77 [8,9] 2,.label 1 4 1]⟩,
    ⟨8,[.label 1 9 0,.asm (.asmi (.inst .skip)) [] 1,.label 1 10 1]⟩,⟨9,[]⟩] := rfl
example : allLabLenPosOk 1 (updLabLen 1 code) := updLabLen_posOk 1 code
example : ¬allLabLenPosOk 1 code ∧ allLabLenPosOk 1 (updLabLen 1 code) := by
  refine ⟨?_,updLabLen_posOk 1 code⟩
  simp [code,lines,allLabLenPosOk,labLenPosOk,lineLabLenPosOk]
example : allLabLenPosOk (width := 8) 17 (updLabLen 17 []) := updLabLen_posOk 17 []
example : updLabLen (width := 8) 17 [⟨7,[]⟩,⟨8,[]⟩] = [⟨7,[]⟩,⟨8,[]⟩] ∧
    allLabLenPosOk (width := 8) 17 (updLabLen 17 [⟨7,[]⟩,⟨8,[]⟩]) := ⟨rfl,updLabLen_posOk 17 _⟩
example : linesUpdLabLen (width := 80) (2^80+1)
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 99,.label 1 2 97] [] =
    ([.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 99,.label 1 2 0],2^80+100) := rfl
example : labLenPosOk (width := 80) (2^80+1) (linesUpdLabLen (2^80+1)
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 99,.label 1 2 97] []).1 := linesUpdLabLen_posOk _ _
example {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labLenPosOk pos (linesUpdLabLen pos lines []).1 := linesUpdLabLen_posOk pos lines
example {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allLabLenPosOk pos (updLabLen pos code) := updLabLen_posOk pos code

def runChecks : IO Bool := do
  IO.println "PASS full label-update parity establishment (14 original observations, arbitrary bad inputs, actual returned positions/tuples, widths1/8/80 and full theorem consumers)"
  pure true
end Flapjack.Test.LabToTargetLabelPositionUpdatesParity
