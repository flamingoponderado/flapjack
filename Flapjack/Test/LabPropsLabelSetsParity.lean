import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.LabProps.LabelSets
namespace Flapjack.Test.LabPropsLabelSetsParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Basis.Pure.MlString
private def lines : List (LabLineHOL 8) :=
  [.label 99 7 5, .labAsm (.jump (.lab 3 4)) 123 [] 0,
   .labAsm (.call (.lab 8 9)) 0 [] 0, .label 10 7 0]
private def code : LabProgHOL 8 := [⟨10,lines⟩,⟨20,[]⟩]
example : extractLabels ([] : List (LabLineHOL 8)) = [] := rfl
example : extractLabels lines = [(99,7),(10,7)] := rfl
example : (3,4) ∈ labsOf (width := 8) (.jump (.lab 3 4)) := by simp [labsOf]
example : (3,4) ∈ labsOf (width := 8) (.locValue 2 (.lab 3 4)) := by simp [labsOf]
example : (3,4) ∈ labsOf (width := 8) (.jumpCmp .equal 2 (.imm 1) (.lab 3 4)) := by simp [labsOf]
example : labsOf (width := 8) (.call (.lab 8 9)) = ∅ := rfl
example : labsOf (width := 8) (.callFFI (.implode [97])) = ∅ := rfl
example : labsOf (width := 8) .install = ∅ := rfl
example : labsOf (width := 8) .halt = ∅ := rfl
example : lineGetLabels (width := 8) (.label 99 7 5) = ∅ := rfl
example : (3,4) ∈ getLabels code := by simp [getLabels, secGetLabels, lineGetLabels, labsOf, code, lines]
example : (8,9) ∉ getLabels code := by simp [getLabels, secGetLabels, lineGetLabels, labsOf, code, lines]
example : (10,7) ∈ getCodeLabels code := by simp [getCodeLabels, secGetCodeLabels, lineGetCodeLabels, code, lines]
example : (10,0) ∈ getCodeLabels code := by simp [getCodeLabels, secGetCodeLabels, lineGetCodeLabels, code, lines]
example : (20,0) ∈ getCodeLabels code := by simp [getCodeLabels, secGetCodeLabels, lineGetCodeLabels, code, lines]
example : (99,7) ∉ getCodeLabels code := by simp [getCodeLabels, secGetCodeLabels, lineGetCodeLabels, code, lines]
example : getLabels ([] : LabProgHOL 8) = ∅ := by ext pair; simp [getLabels]
example : getCodeLabels ([] : LabProgHOL 8) = ∅ := getCodeLabels_nil
example {width : Nat} [NeZero width] (A B : List (LabLineHOL width)) :
    extractLabels (A ++ B) = extractLabels A ++ extractLabels B := extractLabels_append A B
example {width : Nat} [NeZero width] (x : Section (LabLineHOL width)) (xs : LabProgHOL width) :
    getLabels (x :: xs) = secGetLabels x ∪ getLabels xs := getLabels_cons x xs
example {width : Nat} [NeZero width] : getCodeLabels ([] : LabProgHOL width) = ∅ := getCodeLabels_nil
example {width : Nat} [NeZero width] (s : Section (LabLineHOL width)) (secs : LabProgHOL width) :
    getCodeLabels (s :: secs) = secGetCodeLabels s ∪ getCodeLabels secs := getCodeLabels_cons s secs

def runChecks : IO Bool := do
  IO.println "PASS original LabProps label sets (18 observations, 4 full generic consumers)"
  return true
end Flapjack.Test.LabPropsLabelSetsParity
