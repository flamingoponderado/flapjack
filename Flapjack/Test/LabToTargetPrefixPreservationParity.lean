import Flapjack.Compiler.Backend.LabToTarget.PrefixPreservation
namespace Flapjack.Test.LabToTargetPrefixPreservationParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def src : List (LabLineHOL 8) := [.label 1 2 99,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 88]
private def dst : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 1]
example : linesUpdLabLen 0 src [] = (dst,4) := rfl
example : labelPrefixZero dst := by simp [dst,isLabelHOL,lineLen]
example : linesUpdLabLen (width := 8) 1 [.label 1 2 99] [.asm (.asmi (.inst .skip)) [] 3] = ([.asm (.asmi (.inst .skip)) [] 3,.label 1 2 1],2) := rfl
example : labelPrefixZero (width := 8) [.asm (.asmi (.inst .skip)) [] 3,.label 1 2 1] := by simp [isLabelHOL]
example : ¬labelPrefixZero (width := 8) [.label 1 2 1] := by simp [isLabelHOL,lineLen]
example : ¬labelPrefixZero (width := 8) [.label 9 8 7,.label 1 2 0] := by simp [isLabelHOL,lineLen]
example : updLabLen 0 [⟨1,src⟩,⟨3,[.label 3 4 77]⟩] = [⟨1,dst⟩,⟨3,[.label 3 4 0]⟩] := rfl
example : ¬(∀ sec ∈ ([⟨1,[.asm (.asmi (.inst .skip)) [] 3]⟩,⟨3,[.label 3 4 1]⟩] : LabProgHOL 8), secLabelPrefixZero sec) := by simp [secLabelPrefixZero,isLabelHOL,lineLen]
private def encsrc : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 77 [] 2,.label 3 5 99]
private def encdst : List (LabLineHOL 8) := [.label 3 4 0,.labAsm (.jump (.lab 3 4)) 0 [9,9,9,9] 4,.label 3 5 99]
example : encLinesAgainSimp .ln [] 0 (fun _ => [9,9,9,9]) encsrc = (encdst,false) := rfl
example : labelPrefixZero encsrc ∧ labelPrefixZero encdst := by simp [encsrc,encdst,isLabelHOL,lineLen]
example : encSecsAgain 0 .ln [] (fun _ => [9,9,9,9]) [⟨3,encsrc⟩,⟨7,[]⟩] = ([⟨3,encdst⟩,⟨7,[]⟩],false) := rfl
example : labelPrefixZero (linesUpdLabLen (width := 8) 1 [.label 1 2 99] [.asm (.asmi (.inst .skip)) [] 3]).1 :=
  linesUpdLabLen_labelPrefixZero _ _ _ ⟨by simp [isLabelHOL],by simp [isLabelHOL]⟩

example {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ((∀ line ∈ acc, isLabelHOL line = true) → pos % 2 = 0) ∧ labelPrefixZero acc.reverse →
    labelPrefixZero (linesUpdLabLen pos ls acc).1 := linesUpdLabLen_labelPrefixZero pos ls acc

example {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pos % 2 = 0 ∧ (∀ sec ∈ ss, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos ss, secLabelPrefixZero sec := updLabLen_labelPrefixZero pos ss

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧ labelPrefixZero ls → labelPrefixZero res := encLinesAgainSimp_labelPrefixZero labs ffis pos enc ls res ok

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelPrefixZero sec) →
    ∀ sec ∈ res, secLabelPrefixZero sec := encSecsAgain_labelPrefixZero pos labs ffis enc lines res ok

def runChecks : IO Bool := do
  IO.println "PASS full prefix-zero update/encoding laws (11 original observations, 4 full consumers)"
  pure true
end Flapjack.Test.LabToTargetPrefixPreservationParity
