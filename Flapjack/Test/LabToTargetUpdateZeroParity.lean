import Flapjack.Compiler.Backend.LabToTarget.UpdateZero
namespace Flapjack.Test.LabToTargetUpdateZeroParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) := [.label 1 2 999,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 2)) 77 [0,0] 2,.label 1 3 777]
private def out : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 2)) 77 [0,0] 2,.label 1 3 0]
example : linesUpdLabLen 2 lines [] = (out,6) := rfl
example : ∀ l ∈ lines, lineEncd0 (fun _ => [0,0]) l := by
  simp [lines,lineEncd0]
example : ∀ l ∈ out, labelZero l := by simp [out,labelZero]
example : (linesUpdLabLen 2 lines [.label 9 8 0]).1 = .label 9 8 0 :: out := rfl
example : updLabLen 2 [⟨1,lines⟩,⟨3,[.label 3 4 88]⟩] = [⟨1,out⟩,⟨3,[.label 3 4 0]⟩] := rfl
example : ¬(∀ l ∈ (linesUpdLabLen (width := 8) 1 [.label 1 2 77] []).1, labelZero l) := by simp [linesUpdLabLen,labelZero]
example : ¬(∀ l ∈ (linesUpdLabLen (width := 8) 0 [.asm (.asmi (.inst .skip)) [0] 1,.label 1 2 77] []).1, labelZero l) := by simp [linesUpdLabLen,labelZero]
example : ¬(∀ l ∈ (linesUpdLabLen 2 lines [.label 9 8 1]).1, labelZero l) := by simp [linesUpdLabLen,lines,labelZero]
example {w : Nat} [NeZero w] (c : AsmConfigExact w) :
    encOk {c with encode := fun _ => [0,0], codeAlignment := 1} := by simp [encOk,offsetMonotonic]
example {w : Nat} [NeZero w] (c : AsmConfigExact w) :
    encOk {c with encode := fun _ => [0], codeAlignment := 0} := by simp [encOk,offsetMonotonic]

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (pos : Nat) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encOk c ∧ enc = c.encode ∧ c.codeAlignment ≠ 0 ∧
      (∀ line ∈ lines, lineEncd0 enc line) ∧ pos % 2 = 0 ∧
      (∀ line ∈ aux, labelZero line) →
    ∀ line ∈ (linesUpdLabLen pos lines aux).1, labelZero line := linesUpdLabLen_encd0LabelZero c enc pos lines aux

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ enc = c.encode ∧ c.codeAlignment ≠ 0 ∧
      allEncd0 enc code ∧ pos % 2 = 0 ∧
      (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos code, secLabelZero sec := updLabLen_encd0LabelZero c enc pos code

def runChecks : IO Bool := do
  IO.println "PASS full encoded label-update zero establishment (8 original observations, 2 full consumers)"
  pure true
end Flapjack.Test.LabToTargetUpdateZeroParity
