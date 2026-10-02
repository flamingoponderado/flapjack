import Flapjack.Compiler.Backend.LabToTarget.Alignment
namespace Flapjack.Test.LabToTargetAlignmentParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def src : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 77 [1,2] 2]
private def dst : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 0 [9,9,9,9] 4]
example : lineAligned (width := 8) 2 (.label 3 4 0) := by simp [lineAligned,lineLen,lineLength]
example : ¬lineAligned (width := 8) 2 (.label 3 4 2) := by simp [lineAligned,lineLen,lineLength]
example : ¬lineAligned (width := 8) 4 (.asm (.asmi (.inst .skip)) [1,2] 4) := by simp [lineAligned,lineLen,lineLength]
example : ¬lineAligned (width := 8) 2 (.asm (.asmi (.inst .skip)) [1,2] 3) := by simp [lineAligned,lineLen,lineLength]
example : secAligned (width := 8) 0 ⟨1,[]⟩ := by simp [secAligned]
example : lineAligned (width := 8) 0 (.labAsm (.jump (.lab 1 2)) 77 [] 0) := by simp [lineAligned,lineLen,lineLength]
example : ¬lineAligned (width := 8) 0 (.asm (.asmi (.inst .skip)) [1,2] 2) := by simp [lineAligned,lineLen,lineLength]
example : encLinesAgainSimp .ln [] 0 (fun _ => [9,9,9,9]) src = (dst,false) := rfl
example : (∀ l ∈ src, lineAligned 2 l) ∧ (∀ l ∈ dst, lineAligned 2 l) := by simp [src,dst,lineAligned,lineLen,lineLength]
example : encSecsAgain 0 .ln [] (fun _ => [9,9,9,9]) [⟨3,src⟩,⟨7,[]⟩] = ([⟨3,dst⟩,⟨7,[]⟩],false) := rfl
example : encLinesAgainSimp (width := 8) .ln [] 0 (fun _ => []) [.labAsm (.jump (.lab 1 2)) 77 [] 0] = ([.labAsm (.jump (.lab 1 2)) 0 [] 0],true) := rfl

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (enc : HolAsm width → List (BitVec 8))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ enc = c.encode ∧ allEncd0 enc code ∧
      (∀ sec ∈ code, secLabelZero sec) →
    ∀ sec ∈ code, secAligned (enc (.inst .skip)).length sec := allEncd0_aligned c enc code

example {width : Nat} [NeZero width]
    (len : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    (∀ a, (enc a).length % len = 0) ∧
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, lineAligned len line) →
    ∀ line ∈ res, lineAligned len line := encLinesAgainSimp_aligned len labs ffis pos enc ls res ok

example {width : Nat} [NeZero width]
    (len pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    (∀ a, (enc a).length % len = 0) ∧
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secAligned len sec) →
    ∀ sec ∈ res, secAligned len sec := encSecsAgain_aligned len pos labs ffis enc lines res ok

example {width : Nat} [NeZero width] (m : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineAligned m line ↔ lineLen line % m = 0 ∧ lineLength line % m = 0 := Iff.rfl
example {width : Nat} [NeZero width] (m id : Nat) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secAligned m ⟨id,lines⟩ ↔ ∀ l ∈ lines, lineAligned m l := Iff.rfl

def runChecks : IO Bool := do
  IO.println "PASS full dual-length alignment laws (11 original observations, 5 full consumers)"
  pure true
end Flapjack.Test.LabToTargetAlignmentParity
