import Flapjack.Compiler.Backend.LabToTarget.LabelPositionPadding
namespace Flapjack.Test.LabToTargetLabelPositionPaddingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def aux : List (LabLineHOL 8) := [.asm (.asmi (.inst .skip)) [9] 3]
private def lines : List (LabLineHOL 8) := [.label 1 2 1,.label 1 3 0,
  .labAsm .halt 77 [5,6] 3,.label 1 4 1]
private def result : List (LabLineHOL 8) := [.asm (.asmi (.inst .skip)) [9,0] 4,
  .label 1 2 0,.label 1 3 0,.labAsm .halt 77 [5,6,0,0] 4,.label 1 4 0]
private theorem guards : labLenPosOk (0+(aux.map lineLen).sum) lines ∧
    labLenPosOk 0 aux.reverse ∧ (∀ l ∈ aux,labelZero l) ∧
    ((match aux with | [] => True | x :: _ => isLabelHOL x = true) → labelPrefixZero lines) := by
  simp [aux,lines,labLenPosOk,lineLabLenPosOk,lineLen,labelZero,isLabelHOL]
example : labLenPosOk (0+(aux.map lineLen).sum) lines ∧ labLenPosOk 0 aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match aux with | [] => True | x :: _ => isLabelHOL x = true) → labelPrefixZero lines) := guards
example : padSection [0] lines aux = result := rfl
example : labLenPosOk 0 (padSection [0] lines aux) := padSection_posOk [0] lines aux 0 guards
example : padSection [] lines aux = [.asm (.asmi (.inst .skip)) [9] 4,
    .label 1 2 0,.label 1 3 0,.labAsm .halt 77 [5,6] 4,.label 1 4 0] ∧
    labLenPosOk 0 (padSection [] lines aux) := ⟨rfl,padSection_posOk [] lines aux 0 guards⟩
example : padSection [7,8] lines aux = [.asm (.asmi (.inst .skip)) [9,7,8] 4,
    .label 1 2 0,.label 1 3 0,.labAsm .halt 77 [5,6,7,7,8] 4,.label 1 4 0] ∧
    labLenPosOk 0 (padSection [7,8] lines aux) := ⟨rfl,padSection_posOk [7,8] lines aux 0 guards⟩
example : ((match ([] : List (LabLineHOL 8)) with | [] => True | x :: _ => isLabelHOL x = true) →
    labelPrefixZero (width := 8) [.label 1 2 0]) ∧
    labLenPosOk (width := 8) 0 (padSection [0] [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 1] []) := by
  refine ⟨by simp [isLabelHOL,lineLen],?_⟩
  apply padSection_posOk
  simp [labLenPosOk,lineLabLenPosOk,lineLen,labelZero,isLabelHOL]
example : labLenPosOk (width := 8) 0
    (padSection [0] [.label 1 3 0] [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 2]) := by
  apply padSection_posOk
  simp [labLenPosOk,lineLabLenPosOk,lineLen,labelZero,isLabelHOL]
example : labLenPosOk (width := 8) 1 [.label 1 2 1] ∧
    ¬labelPrefixZero (width := 8) [.label 1 2 1] ∧
    ¬labLenPosOk (width := 8) 1 (padSection [0] [.label 1 2 1] []) := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL,padSection,addNop]
example : labelPrefixZero (width := 8) [.label 1 2 0] ∧
    ¬labLenPosOk (width := 8) 1 [.label 1 2 0] ∧
    ¬labLenPosOk (width := 8) 1 (padSection [0] [.label 1 2 0] []) := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL,padSection]
example : (∀ l ∈ ([.label 1 2 0] : List (LabLineHOL 8)),labelZero l) ∧
    ¬labLenPosOk (width := 8) 1 ([.label 1 2 0] : List (LabLineHOL 8)).reverse ∧
    ¬labLenPosOk (width := 8) 1 (padSection [0] [] [.label 1 2 0]) := by
  simp [labLenPosOk,lineLabLenPosOk,labelZero,padSection]
example : padSection (width := 1) [0] [] [] = [] ∧ labLenPosOk (width := 1) 17 (padSection [0] [] []) :=
  ⟨rfl,padSection_posOk [0] [] [] 17 (by simp [labLenPosOk])⟩
example : padSection (width := 80) [7,8]
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 2 1] [] =
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7,8,7,7,8] 4,.label 1 2 0] ∧
    labLenPosOk (width := 80) (2^80) (padSection [7,8]
      [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 2 1] []) := by
  refine ⟨rfl,?_⟩
  apply padSection_posOk
  simp [labLenPosOk,lineLabLenPosOk,lineLen,isLabelHOL]
example {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines aux : List (LabLineHOL width)) (pos : Nat) :
    labLenPosOk (pos+(aux.map lineLen).sum) lines ∧ labLenPosOk pos aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match aux with | [] => True | x :: _ => isLabelHOL x = true) → labelPrefixZero lines) →
    labLenPosOk pos (padSection nop lines aux) := padSection_posOk nop lines aux pos

def runChecks : IO Bool := do
  IO.println "PASS full padding parity (12 original observations, all four original guards, literal null-or-head cases, arbitrary NOP bytes, complete tuples and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetLabelPositionPaddingParity
