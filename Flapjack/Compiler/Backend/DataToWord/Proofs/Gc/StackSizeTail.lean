module

public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Mathlib.Tactic

@[expose] public section

/-! Stack accounting for the data-to-word pop-environment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Removing the top frame preserves its saved local-size bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "option_le_tl"
  (words_as_type_indexed_bitvec)]
theorem optionLe_tail {width : Nat} [NeZero width]
    (opt : Option Nat) (ws vs : List (Nat × WordLocW width))
    (handler : Option (Nat × Nat × Nat)) (ys : List (WordSemStackFrame width))
    (s t : Option Nat)
    (bound : optionLe (wordSemOptionAdd
      (wordSemStackSize (.stackFrame opt ws vs handler :: ys)) s) t) :
    optionLe (wordSemOptionAdd (wordSemStackSize ys) opt) t := by
  cases handler <;> cases hsize : wordSemStackSize ys <;> cases opt <;> cases s <;> cases t <;>
    simp_all [wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, optionLe] <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
