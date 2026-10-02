import Flapjack.Compiler.Backend.LabToTarget.StrongEvenLabels
namespace Flapjack.Test.LabToTargetStrongEvenLabelsParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm
private def lines : List (LabLineHOL 8) :=
  [.asm (.asmi (.inst .skip)) [1,2,3] 1,.label 999 4 0,.labAsm .halt 99 [] 2,.label 9 0 0]
private def code : List (Section (LabLineHOL 8)) := [⟨7,lines⟩,⟨7,[.label 888 5 0]⟩]
example : evenLabels 3 code ∧ (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
    (∀ sec ∈ code,secLabelZero sec) ∧ evenLabelsStrong 3 code := by
  simp [code,lines,evenLabels,evenLabelsStrong,secEndsWithLabelNative,secLabelZero,labelZero,isLabelHOL,lineLen]
example : ¬evenLabels (width := 8) 3 [⟨7,[.label 99 4 0]⟩] ∧
    secEndsWithLabelNative (width := 8) ⟨7,[.label 99 4 0]⟩ ∧
    secLabelZero (width := 8) ⟨7,[.label 99 4 0]⟩ ∧
    ¬evenLabelsStrong (width := 8) 3 [⟨7,[.label 99 4 0]⟩] := by
  simp [evenLabels,evenLabelsStrong,secEndsWithLabelNative,secLabelZero,labelZero,isLabelHOL]
example : evenLabels (width := 8) 3 [⟨7,[]⟩] ∧
    ¬secEndsWithLabelNative (width := 8) ⟨7,[]⟩ ∧
    secLabelZero (width := 8) ⟨7,[]⟩ ∧ ¬evenLabelsStrong (width := 8) 3 [⟨7,[]⟩] := by
  simp [evenLabels,evenLabelsStrong,secEndsWithLabelNative,secLabelZero]
example : evenLabels (width := 8) 4 [⟨7,[.label 99 4 1]⟩] ∧
    secEndsWithLabelNative (width := 8) ⟨7,[.label 99 4 1]⟩ ∧
    ¬secLabelZero (width := 8) ⟨7,[.label 99 4 1]⟩ ∧
    ¬evenLabelsStrong (width := 8) 4 [⟨7,[.label 99 4 1]⟩] := by
  simp [evenLabels,evenLabelsStrong,secEndsWithLabelNative,secLabelZero,labelZero,isLabelHOL,lineLen]
example : evenLabelsStrong (width := 1) 17 [] := by simp [evenLabelsStrong]
example : evenLabelsStrong (width := 80) (2^80) [⟨9,[.label 999 5 0]⟩] := by
  simp [evenLabelsStrong,isLabelHOL,lineLen]
example {width : Nat} [NeZero width] (pos : Nat) (code : List (Section (LabLineHOL width))) :
    evenLabels pos code ∧ (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
    (∀ sec ∈ code,secLabelZero sec) → evenLabelsStrong pos code := evenLabels_ends_imp_strong pos code

def runChecks : IO Bool := do
  IO.println "PASS full weak-to-strong evenness: three original guards, independent counterexamples, section end, widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetStrongEvenLabelsParity
