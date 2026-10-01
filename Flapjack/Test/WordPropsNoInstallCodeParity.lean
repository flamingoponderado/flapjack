import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode
namespace Flapjack.Test.WordPropsNoInstallCodeParity
open Flapjack Flapjack.WordProps
-- nic_empty_1
example : (sptLookup 0 (.ln : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_leaf_zero_1
example : (sptLookup 0 (.ls (999,.skip) : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (999,true) := by rfl

-- nic_leaf_missing_1
example : (sptLookup 7 (.ls (999,.skip) : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_bad_leaf_1
example : (sptLookup 0 (.ls (7,.install 0 1 2 3 (.ln,.ln)) : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (7,false) := by rfl

-- nic_malformed_empty_1
example : (sptLookup 3 (.bn .ln .ln : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_malformed_value_1
example : (sptLookup 0 (.bs .ln (17,.skip) .ln : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (17,true) := by rfl

-- nic_nested_left_1
example : (sptLookup 2 (.bn (.ls (8,.tick)) (.ls (9,.install 0 1 2 3 (.ln,.ln))) : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (8,true) := by rfl

-- nic_nested_right_1
example : (sptLookup 1 (.bn (.ls (8,.tick)) (.ls (9,.install 0 1 2 3 (.ln,.ln))) : Spt (Nat × WordLangProgHOL (BitVec 1)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (9,false) := by rfl

-- nic_empty_80
example : (sptLookup 0 (.ln : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_leaf_zero_80
example : (sptLookup 0 (.ls (999,.skip) : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (999,true) := by rfl

-- nic_leaf_missing_80
example : (sptLookup 7 (.ls (999,.skip) : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_bad_leaf_80
example : (sptLookup 0 (.ls (7,.install 0 1 2 3 (.ln,.ln)) : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (7,false) := by rfl

-- nic_malformed_empty_80
example : (sptLookup 3 (.bn .ln .ln : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = none := by rfl

-- nic_malformed_value_80
example : (sptLookup 0 (.bs .ln (17,.skip) .ln : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (17,true) := by rfl

-- nic_nested_left_80
example : (sptLookup 2 (.bn (.ls (8,.tick)) (.ls (9,.install 0 1 2 3 (.ln,.ln))) : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (8,true) := by rfl

-- nic_nested_right_80
example : (sptLookup 1 (.bn (.ls (8,.tick)) (.ls (9,.install 0 1 2 3 (.ln,.ln))) : Spt (Nat × WordLangProgHOL (BitVec 80)))).map
    (fun row => (row.1,noInstallSubprogsHOL row.2)) = some (9,false) := by rfl

-- Empty maps discharge the quantified convention without premises.
example {width : Nat} [NeZero width] :
    noInstallCode (.ln : Spt (Nat × WordLangProgHOL (BitVec width))) := by
  intro key count program h
  cases h

-- Malformed source BS trees are retained, with no well-formedness guard.
example {width : Nat} [NeZero width] (count : Nat) :
    noInstallCode (.bs .ln (count,.skip) .ln : Spt (Nat × WordLangProgHOL (BitVec width))) := by
  intro key n program h
  by_cases hk : key = 0
  · simp [sptLookup,hk] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  · simp [sptLookup,hk] at h

-- An actual forbidden value refutes the full convention.
example {width : Nat} [NeZero width] (count : Nat) :
    ¬ noInstallCode (.ls (count,.install 0 1 2 3 (.ln,.ln)) :
      Spt (Nat × WordLangProgHOL (BitVec width))) := by
  intro h
  have failure := h 0 count (.install 0 1 2 3 (.ln,.ln)) rfl
  cases failure
end Flapjack.Test.WordPropsNoInstallCodeParity
