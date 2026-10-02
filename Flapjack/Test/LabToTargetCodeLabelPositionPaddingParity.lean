import Flapjack.Compiler.Backend.LabToTarget.CodeLabelPositionPadding
namespace Flapjack.Test.LabToTargetCodeLabelPositionPaddingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def code : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 1]⟩,
   ⟨8,[.label 1 4 0,.labAsm .halt 77 [] 3,.label 1 5 1]⟩,⟨9,[]⟩]
private def zero : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [] 2,.label 1 3 0]⟩,
   ⟨8,[.label 1 4 0,.labAsm .halt 77 [] 2,.label 1 5 0]⟩,⟨9,[]⟩]
private theorem guards : allLabLenPosOk 0 code ∧
    (([0] : List (BitVec 8)).length ≠ 1 → ∀ s ∈ code,secLabelZero s) ∧
    (∀ s ∈ code,secLabelOne s) ∧ (∀ s ∈ code,secLabelPrefixZero s) := by
  simp [code,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,secLength,
    secLabelOne,labelOne,secLabelPrefixZero,isLabelHOL]
private theorem zeroGuards (nop : List (BitVec 8)) : allLabLenPosOk 0 zero ∧
    (nop.length ≠ 1 → ∀ s ∈ zero,secLabelZero s) ∧
    (∀ s ∈ zero,secLabelOne s) ∧ (∀ s ∈ zero,secLabelPrefixZero s) := by
  simp [zero,allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,secLength,
    secLabelZero,labelZero,secLabelOne,labelOne,secLabelPrefixZero,isLabelHOL]
example : allLabLenPosOk 0 code ∧
    (([0] : List (BitVec 8)).length ≠ 1 → ∀ s ∈ code,secLabelZero s) ∧
    (∀ s ∈ code,secLabelOne s) ∧ (∀ s ∈ code,secLabelPrefixZero s) := guards
example : padCode [0] code = [⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0,0,0] 4,.label 1 3 0]⟩,
    ⟨8,[.label 1 4 0,.labAsm .halt 77 [0,0,0,0] 4,.label 1 5 0]⟩,⟨9,[]⟩] := rfl
example : allLabLenPosOk 0 (padCode [0] code) := allLabLenPosOk_padCode [0] code 0 guards
example : (∀ s ∈ zero,secLabelZero s) ∧ allLabLenPosOk 0 zero ∧ padCode [] zero = zero ∧
    allLabLenPosOk 0 (padCode [] zero) := by
  exact ⟨(zeroGuards []).2.1 (by decide +kernel),(zeroGuards []).1,rfl,
    allLabLenPosOk_padCode [] zero 0 (zeroGuards [])⟩
example : padCode [7,8] zero = [⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [7,8] 2,.label 1 3 0]⟩,
    ⟨8,[.label 1 4 0,.labAsm .halt 77 [7,8] 2,.label 1 5 0]⟩,⟨9,[]⟩] ∧
    allLabLenPosOk 0 (padCode [7,8] zero) :=
  ⟨rfl,allLabLenPosOk_padCode [7,8] zero 0 (zeroGuards [7,8])⟩
example : allLabLenPosOk (width := 8) 1 [⟨7,[.label 1 2 1]⟩] ∧
    ¬(∀ s ∈ ([⟨7,[.label 1 2 1]⟩] : List (Section (LabLineHOL 8))),secLabelPrefixZero s) ∧
    ¬allLabLenPosOk (width := 8) 1 (padCode [0] [⟨7,[.label 1 2 1]⟩]) := by
  simp [allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,
    secLabelPrefixZero,isLabelHOL,padCode,padSection,addNop]
example : (∀ s ∈ ([⟨7,[.label 1 2 0]⟩] : List (Section (LabLineHOL 8))),secLabelPrefixZero s) ∧
    ¬allLabLenPosOk (width := 8) 1 [⟨7,[.label 1 2 0]⟩] ∧
    ¬allLabLenPosOk (width := 8) 1 (padCode [0] [⟨7,[.label 1 2 0]⟩]) := by
  simp [allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,
    secLabelPrefixZero,isLabelHOL,padCode,padSection]
example : allLabLenPosOk (width := 1) 17 (padCode [0] []) :=
  allLabLenPosOk_padCode [0] [] 17 (by simp [allLabLenPosOk])
example : padCode (width := 8) [0] [⟨7,[]⟩,⟨8,[]⟩] = [⟨7,[]⟩,⟨8,[]⟩] ∧
    allLabLenPosOk (width := 8) 17 (padCode [0] [⟨7,[]⟩,⟨8,[]⟩]) := by
  refine ⟨rfl,?_⟩
  apply allLabLenPosOk_padCode
  simp [allLabLenPosOk,labLenPosOk,secLabelOne,secLabelPrefixZero]
example : padCode (width := 80) [7]
    [⟨7,[.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 2 1]⟩,⟨8,[.label 1 3 0]⟩] =
    [⟨7,[.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [7,7,7,7] 4,.label 1 2 0]⟩,⟨8,[.label 1 3 0]⟩] ∧
    allLabLenPosOk (width := 80) (2^80) (padCode [7]
      [⟨7,[.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 3,.label 1 2 1]⟩,⟨8,[.label 1 3 0]⟩]) := by
  refine ⟨rfl,?_⟩
  apply allLabLenPosOk_padCode
  simp [allLabLenPosOk,labLenPosOk,lineLabLenPosOk,lineLen,secLength,
    secLabelOne,labelOne,secLabelPrefixZero,isLabelHOL]
example {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (code : List (Section (LabLineHOL width))) (pos : Nat) :
    allLabLenPosOk pos code ∧ (nop.length ≠ 1 → ∀ s ∈ code,secLabelZero s) ∧
    (∀ s ∈ code,secLabelOne s) ∧ (∀ s ∈ code,secLabelPrefixZero s) →
    allLabLenPosOk pos (padCode nop code) := allLabLenPosOk_padCode nop code pos

def runChecks : IO Bool := do
  IO.println "PASS full code padding parity (10 original observations, all four guards, actual section positions/full tuples, empty and multibyte NOPs and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetCodeLabelPositionPaddingParity
