import Flapjack.Compiler.Backend.LabToTarget.PrefixPaddingLength
namespace Flapjack.Test.LabToTargetPrefixPaddingLengthParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def xs : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 1]
private def aux : List (LabLineHOL 8) := [.label 1 8 17,.label 1 9 19]
private theorem guard (acc : List (LabLineHOL 8)) :
    ([0] : List (BitVec 8)).length = 1 ∧ (∀ l ∈ xs,labelOne l) ∧
    ((∀ l ∈ acc,isLabelHOL l = true) → labelPrefixZero xs) := by
  simp [xs,labelOne,isLabelHOL,lineLen]
example : ([0] : List (BitVec 8)).length = 1 ∧ (∀ l ∈ xs,labelOne l) ∧
    ((∀ l ∈ ([] : List (LabLineHOL 8)),isLabelHOL l = true) → labelPrefixZero xs) ∧
    ((padSection [0] xs []).map lineLen).sum = (xs.map lineLen).sum := by
  exact ⟨rfl,(guard []).2.1,(guard []).2.2,by simpa using lineLen_padSection_prefix [0] xs [] (guard [])⟩
example : (∀ l ∈ xs,labelOne l) ∧ ((∀ l ∈ aux,isLabelHOL l = true) → labelPrefixZero xs) ∧
    ((padSection [0] xs aux).map lineLen).sum = (xs.map lineLen).sum + 36 := by
  exact ⟨(guard aux).2.1,(guard aux).2.2,by simpa [aux,lineLen] using lineLen_padSection_prefix [0] xs aux (guard aux)⟩
example : padSection [0] xs aux = [.label 1 9 19,.label 1 8 17,.label 1 2 0,
    .asm (.asmi (.inst .skip)) [0,0,0,0] 4,.label 1 3 0] := rfl
example : ¬(∀ l ∈ ([.asm (.asmi (.inst .skip)) [] 3] : List (LabLineHOL 8)),isLabelHOL l = true) ∧
    ((padSection (width := 8) [0] [.label 1 2 1] [.asm (.asmi (.inst .skip)) [] 3]).map lineLen).sum = 4 := by
  exact ⟨by simp [isLabelHOL],rfl⟩
example : (∀ l ∈ ([.label 1 2 1] : List (LabLineHOL 8)),labelOne l) ∧
    ¬labelPrefixZero (width := 8) [.label 1 2 1] ∧
    ((padSection (width := 8) [0] [.label 1 2 1] []).map lineLen).sum ≠
      (([.label 1 2 1] : List (LabLineHOL 8)).map lineLen).sum := by
  simp [labelOne,isLabelHOL,lineLen,padSection,addNop]
example : ¬(∀ l ∈ ([.label 1 2 2] : List (LabLineHOL 8)),labelOne l) ∧
    ((padSection (width := 8) [0] [.label 1 2 2] [.asm (.asmi (.inst .skip)) [] 3]).map lineLen).sum ≠ 5 := by
  simp [labelOne,padSection,addNop,lineLen]
example : ((padSection (width := 1) [0] [] [.label 1 2 97]).map lineLen).sum = 97 := rfl
example : ((padSection (width := 80) [7]
    [.label 1 2 0,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 3 1] [.label 1 8 17]).map lineLen).sum = 21 := by
  have h := lineLen_padSection_prefix (width := 80) [7]
    [.label 1 2 0,.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 3 1] [.label 1 8 17]
    (by simp [labelOne,isLabelHOL,lineLen])
  simpa [lineLen] using h
example {width : Nat} [NeZero width] (nop : List (BitVec 8)) (xs aux : List (LabLineHOL width)) :
    nop.length = 1 ∧ (∀ l ∈ xs,labelOne l) ∧
    ((∀ l ∈ aux,isLabelHOL l = true) → labelPrefixZero xs) →
    ((padSection nop xs aux).map lineLen).sum = (xs.map lineLen).sum + (aux.map lineLen).sum :=
  lineLen_padSection_prefix nop xs aux

def runChecks : IO Bool := do
  IO.println "PASS full prefix-guarded padding annotation conservation (8 original observations, empty/all-label/nonlabel accumulators, both guard counterexamples and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetPrefixPaddingLengthParity
