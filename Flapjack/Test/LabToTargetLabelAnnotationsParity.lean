import Flapjack.Compiler.Backend.LabToTarget.LabelAnnotations
namespace Flapjack.Test.LabToTargetLabelAnnotationsParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def bad : List (LabLineHOL 8) :=
  [.label 3 4 99,.asm (.asmi (.inst .skip)) [] 1,.label 3 5 77]
private def grow : HolAsm 8 → List (BitVec 8)
  | .jump w => if w = 0 then [0] else [1,1,1]
  | _ => [99,99]
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
example : labelOne (.label 8 9 0 : LabLineHOL 8) := by simp [labelOne]
example : labelOne (.label 8 9 1 : LabLineHOL 8) := by simp [labelOne]
example : ¬labelOne (.label 8 9 2 : LabLineHOL 8) := by simp [labelOne]
example : labelOne (.asm (.asmi (.inst .skip)) [] 999 : LabLineHOL 8) := trivial
example : labelOne (.labAsm (.jump (.lab 3 4)) 0 [] 999 : LabLineHOL 8) := trivial
example : secLabelOne (⟨3,[]⟩ : Section (LabLineHOL 8)) := by simp [secLabelOne]
example : ¬secLabelOne ⟨3,bad⟩ := by simp [secLabelOne,bad,labelOne]
example : linesUpdLabLen 0 bad [] =
  ([.label 3 4 0,.asm (.asmi (.inst .skip)) [] 1,.label 3 5 1],2) := rfl
example : linesUpdLabLen 1 bad [] =
  ([.label 3 4 1,.asm (.asmi (.inst .skip)) [] 1,.label 3 5 1],4) := rfl
example : ∀ sec ∈ updLabLen 1 [⟨3,bad⟩,⟨4,[.label 4 0 999]⟩], secLabelOne sec :=
  updLabLen_labelOne 1 _
example : ¬(∀ line ∈ (linesUpdLabLen 0 [] [.label 7 8 99] (width := 8)).1,
    labelOne line) := by simp [linesUpdLabLen,labelOne]
private theorem growFull : encLinesAgainSimp labs [] 0 grow
    [.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 1] =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3,.label 3 0 1],false) := by
  simp [encLinesAgainSimp,labs,grow,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgainSimp labs [] 0 grow
    [.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 1] =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3,.label 3 0 1],false) := growFull
example : encSecsAgain 0 labs [] grow
    [⟨3,[.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 1]⟩,⟨4,[.label 4 0 0]⟩] =
    ([⟨3,[.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3,.label 3 0 1]⟩,⟨4,[.label 4 0 0]⟩],false) := by
  simp only [encSecsAgain]
  rw [encLinesAgainSimp_eq]
  simp only [growFull,List.reverse_nil,List.nil_append,Bool.true_and]
  rw [encLinesAgainSimp_eq]
  simp [encLinesAgainSimp]

example {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ acc, labelOne line) →
      ∀ line ∈ (linesUpdLabLen pos ls acc).1, labelOne line := linesUpdLabLen_labelOne pos ls acc

example {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ sec ∈ updLabLen pos ss, secLabelOne sec := updLabLen_labelOne pos ss

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      (∀ line ∈ ls, labelOne line) →
    ∀ line ∈ res, labelOne line := encLinesAgainSimp_labelOne labs ffis pos enc ls res ok

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelOne sec) →
    ∀ sec ∈ res, secLabelOne sec := encSecsAgain_labelOne pos labs ffis enc lines res ok

def runChecks : IO Bool := do
  IO.println "PASS original full label_one establishment/preservation (17 kernel replays)"
  pure true
end Flapjack.Test.LabToTargetLabelAnnotationsParity
