import Flapjack.Pancake.WordConvs.LabelSafety

/-! Same-input original source predicate regressions, not cross-language
 equivalence. Infinite external sets and duplicate program keys remain allowed. -/
namespace Flapjack.Test.WordConvsLabelSafetyParity
open Flapjack

macro "source_label_safety_replay" : tactic => `(tactic|
  (simp only [goodCodeLabelsHOL, List.map_cons, List.map_nil, List.mem_cons,
     List.mem_nil_iff, or_false, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
     Set.ofPred_false, Set.sUnion_union, Set.sUnion_singleton, Set.sUnion_empty]
   simp +decide [goodHandlersHOL, getCodeLabelsHOL, Set.subset_def]))

-- wcs_empty
example : goodCodeLabelsHOL ([] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ True := by
  source_label_safety_replay

-- wcs_skip
example : goodCodeLabelsHOL ([(7,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ True := by
  source_label_safety_replay

-- wcs_self
example : goodCodeLabelsHOL ([(7,0,.locValue 0 7)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ True := by
  source_label_safety_replay

-- wcs_missing
example : goodCodeLabelsHOL ([(7,0,.locValue 0 8)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ False := by
  source_label_safety_replay

-- wcs_external
example : goodCodeLabelsHOL ([(7,0,.locValue 0 8)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) {8} ↔ True := by
  source_label_safety_replay

-- wcs_univ
example : goodCodeLabelsHOL ([(7,0,.locValue 99 999)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) Set.univ ↔ True := by
  source_label_safety_replay

-- wcs_duplicates
example : goodCodeLabelsHOL ([(7,0,.locValue 0 7),(7,99,.locValue 99 7)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ True := by
  source_label_safety_replay

-- wcs_cross
example : goodCodeLabelsHOL ([(7,0,.locValue 0 8),(8,0,.locValue 0 7)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ True := by
  source_label_safety_replay

-- wcs_owned
example : goodCodeLabelsHOL ([(7,0,.call (some ([],(.ln,.ln),.skip,11,12)) (some 7) [] (some (0,.locValue 0 8,7,5)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) {8} ↔ True := by
  source_label_safety_replay

-- wcs_wrong_owner
example : goodCodeLabelsHOL ([(7,0,.call (some ([],(.ln,.ln),.skip,11,12)) (some 7) [] (some (0,.locValue 0 8,9,5)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) {8} ↔ False := by
  source_label_safety_replay

-- wcs_tail_foreign
example : goodCodeLabelsHOL ([(7,0,.call (none) (some 7) [] (some (0,.locValue 0 8,999,5)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) {8} ↔ True := by
  source_label_safety_replay

-- wcs_tail_missing
example : goodCodeLabelsHOL ([(7,0,.call (none) (some 7) [] (some (0,.locValue 0 8,999,5)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) ∅ ↔ False := by
  source_label_safety_replay

-- wcs_nested
example : goodCodeLabelsHOL ([(7,0,.mustTerminate (.seq (.loop .ln (.locValue 0 7) .ln) (.locValue 0 8)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) {8} ↔ True := by
  source_label_safety_replay

-- wcs_width_one
example : goodCodeLabelsHOL ([(7,0,.locValue 99 8)] : List (Nat × Nat × WordLangProgHOL (BitVec 1))) {8} ↔ True := by
  source_label_safety_replay

-- Arbitrary external sets: coverage is exactly the original membership condition.
example {width : Nat} [NeZero width] (owner arguments referenced : Nat) (external : Set Nat) :
    goodCodeLabelsHOL ([(owner,arguments,.locValue 99 referenced)] : List (Nat × Nat × WordLangProgHOL (BitVec width))) external ↔
      referenced = owner ∨ referenced ∈ external := by
  source_label_safety_replay

-- Same-input fresh original observations retain independent second carriers.
example : goodCodeLabelsHOL ([(7,true,.locValue 0 8)] : List (Nat × Bool × WordLangProgHOL (BitVec 64))) {8} ↔ True := by
  source_label_safety_replay
example : goodCodeLabelsHOL ([(7,(),.locValue 0 8)] : List (Nat × Unit × WordLangProgHOL (BitVec 64))) ∅ ↔ False := by
  source_label_safety_replay
example : goodCodeLabelsHOL ([(7,[true,false],.locValue 99 7),(7,[],.skip)] : List (Nat × List Bool × WordLangProgHOL (BitVec 1))) ∅ ↔ True := by
  source_label_safety_replay
example : goodCodeLabelsHOL ([(7,none,.locValue 99 8)] : List (Nat × Option Bool × WordLangProgHOL (BitVec 16))) Set.univ ↔ True := by
  source_label_safety_replay

-- The exact original independent carrier is quantified, rather than a
-- representative value or a source-absent conversion requirement.
example {width : Nat} [NeZero width] {α : Type} (field : α)
    (owner referenced : Nat) (external : Set Nat) :
    goodCodeLabelsHOL ([(owner,field,.locValue 99 referenced)] : List (Nat × α × WordLangProgHOL (BitVec width))) external ↔
      referenced = owner ∨ referenced ∈ external := by
  source_label_safety_replay

end Flapjack.Test.WordConvsLabelSafetyParity
