import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.StackProps.CodeLabels

/-! Same-input kernel replay of complete sets observed from original
StackProps in scripts/hol-probes/stackprops_code_labels_probe.out.
Finite regressions do not establish cross-language equivalence. -/
namespace Flapjack.Test.StackPropsCodeLabelsParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

-- sl_skip
example :
    (getCodeLabels (.skip : HolProg 64),
      stackGetHandlerLabels 7 (.skip : HolProg 64)) =
        ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_jump
example :
    (getCodeLabels (.jumpLower 1 2 9 : HolProg 64),
      stackGetHandlerLabels 7 (.jumpLower 1 2 9 : HolProg 64)) =
        (({(9,0)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_raw
example :
    (getCodeLabels (.rawCall 9 : HolProg 64),
      stackGetHandlerLabels 7 (.rawCall 9 : HolProg 64)) =
        (({(9,1)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_location
example :
    (getCodeLabels (.locValue 2 9 4 : HolProg 64),
      stackGetHandlerLabels 7 (.locValue 2 9 4 : HolProg 64)) =
        (({(9,4)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_store_none
example :
    (getCodeLabels (.storeConsts 1 2 none : HolProg 64),
      stackGetHandlerLabels 7 (.storeConsts 1 2 none : HolProg 64)) =
        ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_store_some
example :
    (getCodeLabels (.storeConsts 1 2 (some 9) : HolProg 64),
      stackGetHandlerLabels 7 (.storeConsts 1 2 (some 9) : HolProg 64)) =
        (({(9,0)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_direct_tail
example :
    (getCodeLabels (.call none (.inl 8) none : HolProg 64),
      stackGetHandlerLabels 7 (.call none (.inl 8) none : HolProg 64)) =
        (({(8,0)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_indirect_tail_handler
example :
    (getCodeLabels (.call none (.inr 8) (some (.locValue 2 9 4,7,5)) : HolProg 64),
      stackGetHandlerLabels 7 (.call none (.inr 8) (some (.locValue 2 9 4,7,5)) : HolProg 64)) =
        (({(9,4)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_direct_tail_handler
example :
    (getCodeLabels (.call none (.inl 8) (some (.locValue 2 9 4,7,5)) : HolProg 64),
      stackGetHandlerLabels 7 (.call none (.inl 8) (some (.locValue 2 9 4,7,5)) : HolProg 64)) =
        (({(8,0),(9,4)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels, or_comm]

-- sl_return_owner
example :
    (getCodeLabels (.call (some (.locValue 2 3 6,4,5,6)) (.inl 8) (some (.rawCall 9,7,5)) : HolProg 64),
      stackGetHandlerLabels 7 (.call (some (.locValue 2 3 6,4,5,6)) (.inl 8) (some (.rawCall 9,7,5)) : HolProg 64)) =
        (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- sl_return_other_owner
example :
    (getCodeLabels (.call (some (.locValue 2 3 6,4,5,6)) (.inr 8) (some (.rawCall 9,6,5)) : HolProg 64),
      stackGetHandlerLabels 7 (.call (some (.locValue 2 3 6,4,5,6)) (.inr 8) (some (.rawCall 9,6,5)) : HolProg 64)) =
        (({(3,6),(9,1)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels, or_comm]

-- sl_return_no_handler
example :
    (getCodeLabels (.call (some (.locValue 2 3 6,4,5,6)) (.inr 8) none : HolProg 64),
      stackGetHandlerLabels 7 (.call (some (.locValue 2 3 6,4,5,6)) (.inr 8) none : HolProg 64)) =
        (({(3,6)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_sequence_duplicate
example :
    (getCodeLabels (.seq (.rawCall 9) (.rawCall 9) : HolProg 64),
      stackGetHandlerLabels 7 (.seq (.rawCall 9) (.rawCall 9) : HolProg 64)) =
        (({(9,1)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels]

-- sl_if_loop
example :
    (getCodeLabels (.ite .equal 0 (.reg 1) (.loop (.rawCall 9)) (.locValue 2 9 4) : HolProg 64),
      stackGetHandlerLabels 7 (.ite .equal 0 (.reg 1) (.loop (.rawCall 9)) (.locValue 2 9 4) : HolProg 64)) =
        (({(9,1),(9,4)} : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels, or_comm]

-- sl_nested_handlers
example :
    (getCodeLabels (.call (some (.call (some (.skip,1,2,3)) (.inr 0) (some (.skip,7,2)),4,5,6)) (.inr 0) (some (.call (some (.skip,1,2,3)) (.inr 0) (some (.skip,7,3)),6,5)) : HolProg 64),
      stackGetHandlerLabels 7 (.call (some (.call (some (.skip,1,2,3)) (.inr 0) (some (.skip,7,2)),4,5,6)) (.inr 0) (some (.call (some (.skip,1,2,3)) (.inr 0) (some (.skip,7,3)),6,5)) : HolProg 64)) =
        ((∅ : Set (Nat × Nat)), ({(7,2),(7,3)} : Set (Nat × Nat))) := by
  apply Prod.ext <;> ext label <;>
    simp [getCodeLabels, stackGetHandlerLabels, or_comm]

end Flapjack.Test.StackPropsCodeLabelsParity
