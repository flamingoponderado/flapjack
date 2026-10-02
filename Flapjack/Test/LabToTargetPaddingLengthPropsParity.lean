import Flapjack.Compiler.Backend.LabToTarget.PaddingLengthProps
namespace Flapjack.Test.LabToTargetPaddingLengthPropsParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example : ((padSection (width := 8) [9] [.label 1 2 1,.asm (.asmi (.inst .skip)) [2] 3] [.asm (.asmi (.inst .skip)) [1] 1]).map lineLength).sum = 5 := rfl
example : ((padSection (width := 8) [9] [.label 1 2 1,.asm (.asmi (.inst .skip)) [2] 3] [.asm (.asmi (.inst .skip)) [1] 1]).map lineLen).sum = 5 := rfl
example : ((padSection (width := 8) [] [.label 1 2 0,.asm (.asmi (.inst .skip)) [2] 3] [.label 1 3 99]).map lineLen).sum = 102 := rfl
example : (padSection (width := 8) [9,8] [.label 1 2 0,.labAsm (.jump (.lab 1 2)) 77 [2] 3] [.asm (.asmi (.inst .skip)) [1] 1]).map lineLength = [1,0,3] := rfl
example : ((padSection (width := 8) [9] [.label 1 2 0,.asm (.asmi (.inst .skip)) [2] 3,.label 1 3 1] [.label 1 4 0]).map lineLength).sum = 4 := rfl
example : ((padSection (width := 8) [9] [.label 1 2 1] [.label 1 4 0]).map lineLength).sum ≠ 1 := by decide
example : ((padSection (width := 8) [9,8] [.label 1 2 1] [.asm (.asmi (.inst .skip)) [1] 1]).map lineLength).sum ≠ 2 := by decide
example : (padSection (width := 8) [9] [.asm (.asmi (.inst .skip)) [1,2] 1] []).map lineLength ≠ [1] := by decide

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      ¬(∀ line ∈ acc, isLabelHOL line = true) →
    ((padSection nop ls acc).map lineLen).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := lineLen_padSection_nonlabel nop ls acc

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, labelZero line) →
    ((padSection nop ls acc).map lineLen).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := lineLen_padSection_zero nop ls acc

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      (∀ line ∈ ls, lineLengthLeq line) ∧ ¬(∀ line ∈ acc, isLabelHOL line = true) ∧
      (acc.map lineLength).sum = (acc.map lineLen).sum →
    ((padSection nop ls acc).map lineLength).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := lineLength_padSection_nonlabel nop ls acc

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      (∀ line ∈ ls, lineLengthLeq line) ∧
      (acc.map lineLength).sum = (acc.map lineLen).sum ∧
      (∀ line ∈ acc, isLabelHOL line = true) ∧ labelPrefixZero ls →
    ((padSection nop ls acc).map lineLength).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := lineLength_padSection_labels nop ls acc

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    0 < nop.length ∧ (∀ line ∈ ls, labelZero line) ∧
      acc.map lineLength = acc.map lineLen ∧ (∀ line ∈ ls, lineLengthLeq line) →
    (padSection nop ls acc).map lineLength = (acc.reverse ++ ls).map lineLen := lineLength_padSection_zero nop ls acc

def runChecks : IO Bool := do
  IO.println "PASS full guarded padding lengths (8 original observations, 5 full consumers)"
  pure true
end Flapjack.Test.LabToTargetPaddingLengthPropsParity
