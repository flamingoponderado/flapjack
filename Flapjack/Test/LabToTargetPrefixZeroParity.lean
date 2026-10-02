import Flapjack.Compiler.Backend.LabToTarget.PrefixZero
namespace Flapjack.Test.LabToTargetPrefixZeroParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example : labelPrefixZero ([] : List (LabLineHOL 8)) := labelPrefixZero_nil
example : labelPrefixZero (width := 8) [.label 1 2 0,.label 1 3 0] := by simp [isLabelHOL,lineLen]
example : ¬labelPrefixZero (width := 8) [.label 1 2 0,.label 1 3 7,.asm (.asmi (.inst .skip)) [] 0] := by simp [isLabelHOL,lineLen]
example : labelPrefixZero (width := 8) [.asm (.asmi (.inst .skip)) [] 0,.label 1 2 99] := by simp [isLabelHOL]
example : labelPrefixZero (width := 8) [.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 99] := by simp [isLabelHOL,lineLen]
example : labelPrefixZero (width := 8) [.labAsm (.jump (.lab 1 2)) 77 [] 3,.label 1 2 99] := by simp [isLabelHOL]
example : labelPrefixZero (width := 8) ([.label 1 2 0] ++ [.label 1 3 0]) := by simp [isLabelHOL,lineLen]
example : ¬labelPrefixZero (width := 8) ([.label 1 2 0] ++ [.label 1 3 7]) := by simp [isLabelHOL,lineLen]
example : labelPrefixZero (width := 8) ([.label 1 2 0,.asm (.asmi (.inst .skip)) [] 3] ++ [.label 1 3 7]) := by simp [isLabelHOL,lineLen]
example : ¬labelPrefixZero (width := 8) ([] ++ [.label 1 3 7]) := by simp [isLabelHOL,lineLen]

example {width : Nat} [NeZero width]
    (l1 l2 len : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (b : List (BitVec 8)) (c : Nat)
    (d : AsmWithLab HolCmp (HolRegImm width) MlString) (e : BitVec width)
    (f : List (BitVec 8)) (g : Nat) :
    (labelPrefixZero (.label l1 l2 len :: ls) ↔ len = 0 ∧ labelPrefixZero ls) ∧
    (labelPrefixZero (.asm a b c :: ls) ↔ True) ∧
    (labelPrefixZero (.labAsm d e f g :: ls) ↔ True) := labelPrefixZero_cons l1 l2 len ls a b c d e f g

example {width : Nat} [NeZero width]
    (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero l1 ∧ labelPrefixZero l2 → labelPrefixZero (l1 ++ l2) := labelPrefixZero_append l1 l2

example {width : Nat} [NeZero width]
    (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero l1 ∧ (∃ line ∈ l1, isLabelHOL line ≠ true) →
    labelPrefixZero (l1 ++ l2) := labelPrefixZero_append_nonlabel l1 l2

example {width : Nat} [NeZero width] (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero ls ↔ ∀ n, ∀ hn : n < ls.length,
      (∀ m, ∀ hm : m ≤ n, isLabelHOL (ls[m]'(Nat.lt_of_le_of_lt hm hn)) = true) →
      ∀ m, ∀ hm : m ≤ n, lineLen (ls[m]'(Nat.lt_of_le_of_lt hm hn)) = 0 := Iff.rfl
example {width : Nat} [NeZero width] (id : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secLabelPrefixZero ⟨id,ls⟩ ↔ labelPrefixZero ls := Iff.rfl

def runChecks : IO Bool := do
  IO.println "PASS full bounded prefix-zero constructor/append laws (10 original observations, 5 full consumers)"
  pure true
end Flapjack.Test.LabToTargetPrefixZeroParity
