import Flapjack.Compiler.Backend.LabToTarget.SectionLabelExtraction
namespace Flapjack.Test.LabToTargetSectionLabelExtractionParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets
private def aux : List (Nat × Nat) := [(0,999),(7,40),(7,80)]
private def lines : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,
  .label 9 0 4,.labAsm .halt 99 [] 2,.label 88 2 1]
private def labs : List (Nat × Nat) := [(2,16),(2,6),(0,999),(7,40),(7,80)]
example : sectionLabels 6 lines aux = (16,labs) := rfl
example : insert 0 {k | k ∈ labs.map Prod.fst} = insert 0 {k | k ∈ aux.map Prod.fst} ∪
    {k | ∃ l ∈ lines,k ∈ lineGetCodeLabels l} := sectionLabels_codeLabels 6 lines aux 16 labs rfl
example : (sectionLabels 6 lines aux).2 = [(2,16),(2,6),(0,999),(7,40),(7,80)] := rfl
example : sectionLabels (width := 8) 3 [.label 9 0 5,.label 8 4 2] [] = (10,[(4,10)]) := rfl
example : sectionLabels (width := 8) 3 [.label 9 0 5] [] = (8,[]) ∧
    ({k | k ∈ (sectionLabels (width := 8) 3 [.label 9 0 5] []).2.map Prod.fst} : Set Nat) ≠
      {k | ∃ l ∈ ([.label 9 0 5] : List (LabLineHOL 8)),k ∈ lineGetCodeLabels l} ∧
    insert 0 {k | k ∈ (sectionLabels (width := 8) 3 [.label 9 0 5] []).2.map Prod.fst} =
      insert 0 {k | ∃ l ∈ ([.label 9 0 5] : List (LabLineHOL 8)),k ∈ lineGetCodeLabels l} := by
  refine ⟨rfl,?_,?_⟩
  · intro h
    have h0 := congrArg (fun s : Set Nat => 0 ∈ s) h
    simp [sectionLabels,lineGetCodeLabels] at h0
  · ext k
    simp [sectionLabels,lineGetCodeLabels]
example : sectionLabels (width := 8) 34 [] aux = (34,aux) := rfl
example : sectionLabels (width := 8) 0 [.label 88 0 17] [(0,777)] = (17,[(0,777)]) := rfl
example : sectionLabels (width := 8) 11
    [.asm (.asmi (.inst .skip)) [1,2,3] 2,.labAsm .halt 99 [9] 7] [(8,999)] = (20,[(8,999)]) := rfl
private def opcodes : List (AsmWithLab HolCmp (HolRegImm 8) MlString) :=
  [.jump (.lab 3 4),.jumpCmp .equal 2 (.imm 1) (.lab 3 4),.locValue 2 (.lab 3 4),
   .call (.lab 99 88),.callFFI (.implode []),.install,.halt]
private def opcodeLines : List (LabLineHOL 8) := opcodes.map (fun a => .labAsm a 99 [] 1)
example : sectionLabels 13 opcodeLines aux = (20,aux) ∧
    ({k | ∃ l ∈ opcodeLines,k ∈ lineGetCodeLabels l} : Set Nat) = ∅ := by
  refine ⟨rfl,?_⟩
  ext k
  simp [opcodeLines,opcodes,lineGetCodeLabels]
example : sectionLabels (width := 1) 17 [] [] = (17,[]) := rfl
example : sectionLabels (width := 80) (2^80) [.label 999 0 1,.label 888 5 2] [(0,2^90)] =
    (2^80+3,[(5,2^80+3),(0,2^90)]) := rfl
example {width : Nat} [NeZero width] (pos : Nat) (lines : List (LabLineHOL width))
    (aux : List (Nat × Nat)) (newPos : Nat) (labs : List (Nat × Nat)) :
    sectionLabels pos lines aux = (newPos,labs) →
      insert 0 {k | k ∈ labs.map Prod.fst} = insert 0 {k | k ∈ aux.map Prod.fst} ∪
        {k | ∃ l ∈ lines,k ∈ lineGetCodeLabels l} := sectionLabels_codeLabels pos lines aux newPos labs

def runChecks : IO Bool := do
  IO.println "PASS full section label extraction: eleven original observations, duplicate/zero accumulators, both zero insertions, actual tuples and widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetSectionLabelExtractionParity
