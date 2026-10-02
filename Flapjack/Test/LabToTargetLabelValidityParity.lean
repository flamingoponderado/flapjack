import Flapjack.Compiler.Backend.LabToTarget.LabelValidity
import Flapjack.Compiler.Backend.LabProps.LabelSets
namespace Flapjack.Test.LabToTargetLabelValidityParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8) := fun _ => [0,1]
private def ls : List (LabLineHOL 8) :=
  [.label 1 1 1,.asm (.asmi (.inst .skip)) [10] 1,
   .labAsm (.jump (.lab 3 4)) 99 [11,12] 2,.label 1 3 0]
private def acc : List (LabLineHOL 8) := [.label 1 2 3,.asm (.asmi (.inst .skip)) [20] 1]
private def code : LabProgHOL 8 := [⟨1,ls⟩,⟨2,[]⟩]
private theorem lsValid : ∀ line ∈ ls, secLabelOk 1 line := by simp [ls,secLabelOk]
private theorem accValid : ∀ line ∈ acc, secLabelOk 1 line := by simp [acc,secLabelOk]
private theorem codeValid : ∀ sec ∈ code, secLabelsOk sec := by
  simp [code,secLabelsOk,ls,secLabelOk]
example : ∀ line ∈ ls, secLabelOk 1 line := lsValid
example : ∀ line ∈ acc, secLabelOk 1 line := accValid
example : ∀ sec ∈ encSecList enc code, secLabelsOk sec := encSecList_secLabelsOk enc code codeValid
example : ∀ line ∈ (encLinesAgain .ln [] 3 enc ls acc false).1, secLabelOk 1 line :=
  encLinesAgain_secLabelOk .ln [] 3 enc ls acc false _ _ 1 ⟨rfl,accValid,lsValid⟩
example : ∀ sec ∈ (encSecsAgain 3 .ln [] enc code).1, secLabelsOk sec :=
  encSecsAgain_secLabelsOk 3 .ln [] enc code _ _ ⟨rfl,codeValid⟩
example : ∀ line ∈ (linesUpdLabLen 3 ls acc).1, secLabelOk 1 line :=
  linesUpdLabLen_secLabelOk 3 ls acc 1 ⟨lsValid,accValid⟩
example : ∀ line ∈ (linesUpdLabLen 4 ls acc).1, secLabelOk 1 line :=
  linesUpdLabLen_secLabelOk 4 ls acc 1 ⟨lsValid,accValid⟩
example : ∀ sec ∈ updLabLen 3 code, secLabelsOk sec := updLabLen_secLabelsOk 3 code codeValid
example : ∀ line ∈ addNop [0,0] ls, secLabelOk 1 line := addNop_secLabelOk [0,0] ls 1 lsValid
example : ∀ line ∈ addNop [] ls, secLabelOk 1 line := addNop_secLabelOk [] ls 1 lsValid
example : ∀ line ∈ padSection [0,0] ls acc, secLabelOk 1 line :=
  padSection_secLabelOk [0,0] ls acc 1 ⟨lsValid,accValid⟩
example : ∀ sec ∈ padCode [0,0] code, secLabelsOk sec := padCode_secLabelsOk [0,0] code codeValid
example : (encLinesAgain .ln [] 3 enc ls acc false).2.2 = false := by decide +kernel
example : ¬secLabelsOk (width := 8) ⟨1,[encLine enc 0 (.label 2 0 3)]⟩ := by
  simp [secLabelsOk,secLabelOk,encLine]
example : ¬(∀ line ∈ padSection (width := 8) [0] [.label 2 0 3] [], secLabelOk 1 line) := by
  simp [padSection,addNop,secLabelOk]
example : extractLabels (linesUpdLabLen 3 ls acc).1 = [(1,2),(1,1),(1,3)] := rfl
example : extractLabels (encLinesAgain .ln [] 3 enc ls acc false).1 = [(1,2),(1,1),(1,3)] := rfl
example : extractLabels (padSection [0,0] ls acc) = [(1,2),(1,1),(1,3)] := rfl
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
      ∀ sec ∈ encSecList enc code, secLabelsOk sec := encSecList_secLabelsOk enc code
example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool) (k : Nat) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
      (∀ line ∈ acc, secLabelOk k line) ∧
      (∀ line ∈ lines, secLabelOk k line) →
    ∀ line ∈ res, secLabelOk k line := encLinesAgain_secLabelOk labs ffis pos enc lines acc ok res ok' k
example {width : Nat} [NeZero width]
    (pos : Nat) (labels : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labels ffis enc ls = (res,ok) ∧
      (∀ sec ∈ ls, secLabelsOk sec) →
    ∀ sec ∈ res, secLabelsOk sec := encSecsAgain_secLabelsOk pos labels ffis enc ls res ok
example {width : Nat} [NeZero width]
    (pos : Nat) (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ lines, secLabelOk k line) ∧
      (∀ line ∈ acc, secLabelOk k line) →
    ∀ line ∈ (linesUpdLabLen pos lines acc).1, secLabelOk k line := linesUpdLabLen_secLabelOk pos lines acc k
example {width : Nat} [NeZero width]
    (n : Nat) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ ls, secLabelsOk sec) →
      ∀ sec ∈ updLabLen n ls, secLabelsOk sec := updLabLen_secLabelsOk n ls
example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ aux, secLabelOk k line) →
      ∀ line ∈ addNop nop aux, secLabelOk k line := addNop_secLabelOk nop aux k
example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ xs, secLabelOk k line) ∧
      (∀ line ∈ acc, secLabelOk k line) →
    ∀ line ∈ padSection nop xs acc, secLabelOk k line := padSection_secLabelOk nop xs acc k
example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
      ∀ sec ∈ padCode nop code, secLabelsOk sec := padCode_secLabelsOk nop code
def runChecks : IO Bool := do
  IO.println "PASS full encoding/update/padding section-label validity (18 original observations, 8 generic consumers)"
  return true
end Flapjack.Test.LabToTargetLabelValidityParity
