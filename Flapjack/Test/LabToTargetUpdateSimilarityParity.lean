import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
namespace Flapjack.Test.LabToTargetUpdateSimilarityParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) :=
  [.label 3 4 99,.asm (.asmi (.inst .skip)) [12] 2,.labAsm (.jump (.lab 3 4)) 77 [] 5,.label 3 5 77]
private def acc : List (LabLineHOL 8) := [.label 9 8 91,.asm (.asmi (.inst .skip)) [] 77]
private def target : List (LabLineHOL 8) :=
  [.label 3 4 777,.asm (.asmi (.inst .skip)) [] 999,.labAsm (.jump (.lab 3 4)) 0 [99] 123,.label 3 5 999]
private def updated : List (LabLineHOL 8) :=
  [.label 3 4 0,.asm (.asmi (.inst .skip)) [12] 2,.labAsm (.jump (.lab 3 4)) 77 [] 5,.label 3 5 1]
private theorem relCons {α : Type} (r : α → α → Prop) (x y : α) (xs ys : List α) :
    LinesRel r (x::xs) (y::ys) ↔ r x y ∧ LinesRel r xs ys := by
  constructor
  · intro h; cases h with | cons hx ht => exact ⟨hx,ht⟩
  · rintro ⟨hx,ht⟩; exact .cons hx ht
private theorem relNilLeft {α : Type} (r : α → α → Prop) (ys : List α) :
    LinesRel r [] ys ↔ ys = [] := by
  cases ys with
  | nil => exact ⟨fun _ => rfl,fun _ => .nil⟩
  | cons => constructor <;> intro h <;> cases h
private theorem relNilRight {α : Type} (r : α → α → Prop) (xs : List α) :
    LinesRel r xs [] ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl,fun _ => .nil⟩
  | cons => constructor <;> intro h <;> cases h
example : linesUpdLabLen 3 [] acc = (acc.reverse,3) := rfl
example : linesUpdLabLen 0 lines [] = (updated,8) := rfl
example : linesUpdLabLen 1 lines [] =
    ([.label 3 4 1,.asm (.asmi (.inst .skip)) [12] 2,.labAsm (.jump (.lab 3 4)) 77 [] 5,.label 3 5 1],10) := rfl
example : linesUpdLabLen 0 lines acc = (acc.reverse ++ updated,8) := rfl
example : (linesUpdLabLen 0 lines acc).1 = acc.reverse ++ (linesUpdLabLen 0 lines []).1 :=
  linesUpdLabLen_aux lines acc 0
example : LinesRel lineSimilar (linesUpdLabLen 0 lines []).1 target ∧ LinesRel lineSimilar lines target := by
  simp [linesUpdLabLen,lines,target,lineSimilar,relCons,relNilLeft]
example : ¬LinesRel lineSimilar (linesUpdLabLen 0 lines []).1 [.label 3 8 0] ∧
    ¬LinesRel lineSimilar lines [.label 3 8 0] := by
  simp [linesUpdLabLen,lines,lineSimilar,relCons,relNilRight]
example : (linesUpdLabLen 0 lines []).1 ≠ lines ∧ LinesRel lineSimilar (linesUpdLabLen 0 lines []).1 lines := by
  simp [linesUpdLabLen,lines,lineSimilar,relCons,relNilLeft]
example : codeSimilar (updLabLen 0 [⟨3,lines⟩,⟨7,[]⟩]) [⟨3,target⟩,⟨7,[]⟩] ∧
    codeSimilar [⟨3,lines⟩,⟨7,[]⟩] [⟨3,target⟩,⟨7,[]⟩] := by
  simp [updLabLen,linesUpdLabLen,lines,target,codeSimilar,lineSimilar,relCons,relNilLeft]
example : ¬codeSimilar (updLabLen 0 [⟨3,lines⟩]) [⟨4,target⟩] ∧
    ¬codeSimilar [⟨3,lines⟩] [⟨4,target⟩] := by simp [updLabLen,codeSimilar]
example : ¬LinesRel (lineSimilar (width := 8)) (linesUpdLabLen 0 [.asm (.asmi (.inst .skip)) [] 2] []).1
      [.asm (.asmi (.jump 0)) [] 2] ∧
    ¬LinesRel (lineSimilar (width := 8)) [.asm (.asmi (.inst .skip)) [] 2] [.asm (.asmi (.jump 0)) [] 2] := by simp [linesUpdLabLen,lineSimilar,relCons]
example : LinesRel lineSimilar (linesUpdLabLen 0 lines acc).1 (acc.reverse ++ lines) :=
  linesUpdLabLen_similar 0 lines acc
example : updLabLen 0 ([] : LabProgHOL 8) = [] ∧ codeSimilar (updLabLen 0 ([] : LabProgHOL 8)) [] := by
  simp [updLabLen,codeSimilar]
example : updLabLen 0 [⟨3,lines⟩,⟨7,[]⟩] = [⟨3,updated⟩,⟨7,[]⟩] := rfl

example {width : Nat} [NeZero width]
    (l aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    (linesUpdLabLen pos l aux).1 = aux.reverse ++ (linesUpdLabLen pos l []).1 := linesUpdLabLen_aux l aux pos

example {width : Nat} [NeZero width]
    (l : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) (l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar (linesUpdLabLen pos l []).1 l1 ↔ LinesRel lineSimilar l l1 := linesRel_linesUpdLabLen l pos l1

example {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) (code1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar (updLabLen pos code) code1 ↔ codeSimilar code code1 := codeSimilar_updLabLen code pos code1

example {width : Nat} [NeZero width]
    (pos : Nat) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar (linesUpdLabLen pos lines aux).1 (aux.reverse ++ lines) := linesUpdLabLen_similar pos lines aux

def runChecks : IO Bool := do
  IO.println "PASS full label-update accumulator/similarity laws (14 original observations, 4 full consumers)"
  pure true
end Flapjack.Test.LabToTargetUpdateSimilarityParity
