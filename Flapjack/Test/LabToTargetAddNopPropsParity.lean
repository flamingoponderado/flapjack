import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
namespace Flapjack.Test.LabToTargetAddNopPropsParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def mixed : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [1] 2,.labAsm (.jump (.lab 1 2)) 77 [2] 3,.label 1 3 99]
example : addNop [9,8] mixed = [.label 1 2 0,.asm (.asmi (.inst .skip)) [1,9,8] 3,.labAsm (.jump (.lab 1 2)) 77 [2] 3,.label 1 3 99] := rfl
example : ((addNop [9,8] mixed).map lineLength).sum = (mixed.map lineLength).sum + 2 := rfl
example : ((addNop [9,8] mixed).map lineLen).sum = (mixed.map lineLen).sum + 1 := rfl
example : addNop [] mixed = [.label 1 2 0,.asm (.asmi (.inst .skip)) [1] 3,.labAsm (.jump (.lab 1 2)) 77 [2] 3,.label 1 3 99] := rfl
example : addNop (width := 8) [9,8] [.label 1 2 0,.label 1 3 99] = [.label 1 2 0,.label 1 3 99] := rfl
example : addNop (width := 8) [9,8] [] = [] := rfl
example : addNop (width := 8) [9,8] [.labAsm (.jump (.lab 1 2)) 77 [2] 3,.asm (.asmi (.inst .skip)) [1] 2] = [.labAsm (.jump (.lab 1 2)) 77 [2,9,8] 4,.asm (.asmi (.inst .skip)) [1] 2] := rfl
example : addNop (width := 8) [9] ([.label 1 2 0] ++ [.asm (.asmi (.inst .skip)) [1] 2]) = [.label 1 2 0,.asm (.asmi (.inst .skip)) [1,9] 3] := rfl
example : addNop (width := 8) [9] ([.asm (.asmi (.inst .skip)) [1] 2] ++ [.asm (.asmi (.inst .skip)) [2] 3]) = [.asm (.asmi (.inst .skip)) [1,9] 3,.asm (.asmi (.inst .skip)) [2] 3] := rfl
example : ¬(∀ l ∈ addNop [9] mixed, isLabelHOL l = true) ∧ (∃ l ∈ addNop [9] mixed, isLabelHOL l ≠ true) := by simp [addNop,mixed,isLabelHOL]
example : ((addNop (width := 8) [9,8] [.label 1 2 0]).map lineLength).sum ≠ ([.label 1 2 0].map (lineLength (width := 8))).sum + 2 := by decide

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLength).sum = (ls.map lineLength).sum + nop.length := lineLength_addNop_nonlabel nop ls

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLength).sum = (ls.map lineLength).sum := lineLength_addNop_labels nop ls

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLen).sum = (ls.map lineLen).sum + 1 := lineLen_addNop_nonlabel nop ls

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLen).sum = (ls.map lineLen).sum := lineLen_addNop_labels nop ls

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    addNop nop (l1 ++ l2) = if l1.all isLabelHOL then l1 ++ addNop nop l2 else addNop nop l1 ++ l2 := addNop_append nop l1 l2

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∃ line ∈ addNop nop acc, isLabelHOL line ≠ true) ↔
    (∃ line ∈ acc, isLabelHOL line ≠ true) := existsNotLabel_addNop nop acc

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ addNop nop acc, isLabelHOL line = true) ↔
    (∀ line ∈ acc, isLabelHOL line = true) := everyIsLabel_addNop nop acc

def runChecks : IO Bool := do
  IO.println "PASS full add-NOP dual-length/append/classifier laws (11 original observations, 7 full consumers)"
  pure true
end Flapjack.Test.LabToTargetAddNopPropsParity
