import Flapjack.Compiler.Backend.StackProps.LabelSafety
import Mathlib.Data.Set.Insert

namespace Flapjack.Test.StackPropsLabelSafetyParity
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

-- empty
example : (stackGoodCodeLabels ([] : List (Nat × HolProg 64)) (∅ : Set Nat) ↔ True) ∧
    (stackGoodHandlerLabels ([] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero]

-- self_zero
example : (stackGoodCodeLabels ([(7, .locValue 0 7 0)] : List (Nat × HolProg 64)) ∅ ↔ True) ∧
    (stackGoodHandlerLabels ([(7, .locValue 0 7 0)] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- self_one
example : (stackGoodCodeLabels ([(7, .rawCall 7)] : List (Nat × HolProg 64)) ∅ ↔ True) ∧
    (stackGoodHandlerLabels ([(7, .rawCall 7)] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- missing_zero
example : (stackGoodCodeLabels ([(7, .jumpLower 0 1 9)] : List (Nat × HolProg 64)) ∅ ↔ False) ∧
    (stackGoodHandlerLabels ([(7, .jumpLower 0 1 9)] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- external_zero
example : (stackGoodCodeLabels ([(7, .jumpLower 0 1 9)] : List (Nat × HolProg 64)) {9} ↔ True) ∧
    (stackGoodHandlerLabels ([(7, .jumpLower 0 1 9)] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- external_one
example : (stackGoodCodeLabels ([(7, .rawCall 9)] : List (Nat × HolProg 64)) {9} ↔ True) ∧
    (stackGoodHandlerLabels ([(7, .rawCall 9)] : List (Nat × HolProg 64)) ↔ False) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- missing_one
example : (stackGoodCodeLabels ([(7, .rawCall 9)] : List (Nat × HolProg 64)) ∅ ↔ False) ∧
    (stackGoodHandlerLabels ([(7, .rawCall 9)] : List (Nat × HolProg 64)) ↔ False) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- higher_entry
example : (stackGoodCodeLabels ([(7, .locValue 0 7 2)] : List (Nat × HolProg 64)) Set.univ ↔ False) ∧
    (stackGoodHandlerLabels ([(7, .locValue 0 7 2)] : List (Nat × HolProg 64)) ↔ False) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels,
    stackGetHandlerLabels, Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- owned_handler
example : (stackGoodCodeLabels ([(7, .seq (.locValue 0 7 2) (.call (some (.skip, 0, 0, 0)) (.inr 0) (some (.skip, 7, 2))))] : List (Nat × HolProg 64)) ∅ ↔ True) ∧
    (stackGoodHandlerLabels ([(7, .seq (.locValue 0 7 2) (.call (some (.skip, 0, 0, 0)) (.inr 0) (some (.skip, 7, 2))))] : List (Nat × HolProg 64)) ↔ True) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels, stackGetHandlerLabels,
    Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

-- foreign_handler
example : (stackGoodCodeLabels ([(7, .seq (.locValue 0 7 2) (.call (some (.skip, 0, 0, 0)) (.inr 0) (some (.skip, 8, 2))))] : List (Nat × HolProg 64)) ∅ ↔ False) ∧
    (stackGoodHandlerLabels ([(7, .seq (.locValue 0 7 2) (.call (some (.skip, 0, 0, 0)) (.inr 0) (some (.skip, 8, 2))))] : List (Nat × HolProg 64)) ↔ False) := by
  simp [stackGoodCodeLabels, stackGoodHandlerLabels, getCodeLabels, stackGetHandlerLabels,
    Flapjack.Compiler.Backend.BackendProps.restrictNonzero, Set.subset_def]

def runChecks : IO Bool := do
  IO.println "PASS original whole-program stack label safety (10 kernel rows)"
  return true
end Flapjack.Test.StackPropsLabelSafetyParity
