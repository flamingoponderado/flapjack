import Flapjack.Pancake.WordConvs.CodeLabels
import Mathlib.Data.Set.Insert

/-! Same-input kernel replay of the twelve original complete label sets in
scripts/hol-probes/wordconvs_code_labels_probe.out. -/
namespace Flapjack.Test.WordConvsCodeLabelsParity
open Flapjack

-- wl_skip
example : getCodeLabelsHOL (.skip : WordLangProgHOL (BitVec 64)) =
    (∅ : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_location
example : getCodeLabelsHOL (.locValue 2 9 : WordLangProgHOL (BitVec 64)) =
    ({9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_direct_tail
example : getCodeLabelsHOL (.call none (some 8) [] none : WordLangProgHOL (BitVec 64)) =
    ({8} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_indirect_tail
example : getCodeLabelsHOL (.call none none [] none : WordLangProgHOL (BitVec 64)) =
    (∅ : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_tail_handler
example : getCodeLabelsHOL (.call none none [] (some (1,.locValue 2 9,7,5)) : WordLangProgHOL (BitVec 64)) =
    ({9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_both_bodies
example : getCodeLabelsHOL (.call (some ([],(.ln,.ln),.locValue 2 3,4,5)) (some 8) [] (some (1,.locValue 2 9,7,5)) : WordLangProgHOL (BitVec 64)) =
    ({8,3,9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL, or_assoc, or_left_comm, or_comm]

-- wl_metadata_omitted
example : getCodeLabelsHOL (.call (some ([],(.ln,.ln),.skip,4,5)) none [] (some (1,.skip,7,6)) : WordLangProgHOL (BitVec 64)) =
    (∅ : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_return_only
example : getCodeLabelsHOL (.call (some ([],(.ln,.ln),.locValue 2 3,4,5)) none [] none : WordLangProgHOL (BitVec 64)) =
    ({3} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_duplicate
example : getCodeLabelsHOL (.seq (.locValue 2 9) (.locValue 3 9) : WordLangProgHOL (BitVec 64)) =
    ({9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_if
example : getCodeLabelsHOL (.ite .equal 0 (.reg 1) (.locValue 2 3) (.locValue 2 9) : WordLangProgHOL (BitVec 64)) =
    ({3,9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL, or_comm]

-- wl_loop
example : getCodeLabelsHOL (.loop .ln (.locValue 2 9) .ln : WordLangProgHOL (BitVec 64)) =
    ({9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

-- wl_must
example : getCodeLabelsHOL (.mustTerminate (.locValue 2 9) : WordLangProgHOL (BitVec 64)) =
    ({9} : Set Nat) := by
  ext label
  simp [getCodeLabelsHOL]

end Flapjack.Test.WordConvsCodeLabelsParity
