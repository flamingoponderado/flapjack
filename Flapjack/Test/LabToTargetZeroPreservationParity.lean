import Flapjack.Compiler.Backend.LabToTarget.ZeroPreservation
namespace Flapjack.Test.LabToTargetZeroPreservationParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 77 [] 1]
private def res : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 0 [9,9,9] 3]
example : addNop (width := 8) [0] [.label 1 2 0,.asm (.asmi (.inst .skip)) [1] 2,.label 1 3 0] = [.label 1 2 0,.asm (.asmi (.inst .skip)) [1,0] 3,.label 1 3 0] := rfl
example : ¬(∀ l ∈ addNop (width := 8) [0] [.label 1 2 1], labelZero l) := by simp [addNop,labelZero]
example : padSection (width := 8) [0] [.label 1 2 999] [] = [.label 1 2 0] := rfl
example : padSection (width := 8) [0] [.label 1 2 1] [.asm (.asmi (.inst .skip)) [1] 2] = [.asm (.asmi (.inst .skip)) [1,0] 3,.label 1 2 0] := rfl
example : ¬(∀ l ∈ padSection (width := 8) [0] [] [.label 1 2 1], labelZero l) := by simp [padSection,labelZero]
example : ∀ sec ∈ padCode (width := 8) [0] [⟨1,[.label 1 2 999]⟩,⟨7,[]⟩], secLabelZero sec := everySecLabelZero_padCode _ _
example : encLinesAgainSimp .ln [] 0 (fun _ => [9,9,9]) lines = (res,false) := rfl
example : (∀ l ∈ lines, labelZero (width := 8) l) ∧ (∀ l ∈ res, labelZero (width := 8) l) := by simp [lines,res,labelZero]
example : encSecsAgain 0 .ln [] (fun _ => [9,9,9]) [⟨3,lines⟩,⟨7,[]⟩] = ([⟨3,res⟩,⟨7,[]⟩],false) := rfl

example {width : Nat} [NeZero width]
    (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (nop : List (BitVec 8)) :
    (∀ line ∈ addNop nop xs, labelZero line) ↔ (∀ line ∈ xs, labelZero line) := everyLabelZero_addNop xs nop

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ aux, labelZero line) → ∀ line ∈ padSection nop xs aux, labelZero line := everyLabelZero_padSection nop xs aux

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ sec ∈ padCode nop ls, secLabelZero sec := everySecLabelZero_padCode nop ls

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, labelZero line) →
    ∀ line ∈ res, labelZero line := encLinesAgainSimp_labelZero labs ffis pos enc ls res ok

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelZero sec) →
    ∀ sec ∈ res, secLabelZero sec := encSecsAgain_labelZero pos labs ffis enc lines res ok

def runChecks : IO Bool := do
  IO.println "PASS full zero-label padding/repeated-encoding preservation (9 original observations, 5 full consumers)"
  pure true
end Flapjack.Test.LabToTargetZeroPreservationParity
