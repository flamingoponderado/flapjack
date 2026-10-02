import Flapjack.Compiler.Backend.LabToTarget.LabelPositionPrefix
namespace Flapjack.Test.LabToTargetLabelPositionPrefixParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) := [.label 1 2 0,.label 1 3 0,
  .asm (.asmi (.inst .skip)) [] 3,.label 1 4 1]
example : labLenPosOk 4 lines ∧ labelPrefixZero lines := by
  have hp : labLenPosOk 4 lines := by simp [lines,labLenPosOk,lineLabLenPosOk,lineLen]
  exact ⟨hp,labLenPosOk_evenPrefixZero 4 lines ⟨rfl,hp⟩⟩
example : labLenPosOk (width := 8) 3 [.label 1 2 1] ∧ ¬labelPrefixZero (width := 8) [.label 1 2 1] := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL]
example : ¬labLenPosOk (width := 8) 4 [.label 1 2 1] ∧ ¬labelPrefixZero (width := 8) [.label 1 2 1] := by
  simp [labLenPosOk,lineLabLenPosOk,isLabelHOL,lineLen]
example : labLenPosOk (width := 1) 100 [] ∧ labelPrefixZero (width := 1) [] :=
  ⟨True.intro,labLenPosOk_evenPrefixZero 100 [] ⟨rfl,True.intro⟩⟩
example : labLenPosOk (width := 8) 0 [.asm (.asmi (.inst .skip)) [] 99,.label 1 2 1] ∧
    labelPrefixZero (width := 8) [.asm (.asmi (.inst .skip)) [] 99,.label 1 2 1] := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL]
example : labLenPosOk (width := 80) (2^80)
    [.label 1 2 0,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 3,.label 1 4 1] ∧
    labelPrefixZero (width := 80)
    [.label 1 2 0,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 3,.label 1 4 1] := by
  have hp : labLenPosOk (width := 80) (2^80)
      [.label 1 2 0,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7] 3,.label 1 4 1] := by
    simp [labLenPosOk,lineLabLenPosOk,lineLen]
  exact ⟨hp,labLenPosOk_evenPrefixZero _ _ ⟨by decide +kernel,hp⟩⟩
example {width : Nat} [NeZero width] (pos : Nat) (lines : List (LabLineHOL width)) :
    pos % 2 = 0 ∧ labLenPosOk pos lines → labelPrefixZero lines :=
  labLenPosOk_evenPrefixZero pos lines

def runChecks : IO Bool := do
  IO.println "PASS full even-position label parity to bounded prefix (6 original observations, both necessary guards, malformed nonlabel fields and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetLabelPositionPrefixParity
