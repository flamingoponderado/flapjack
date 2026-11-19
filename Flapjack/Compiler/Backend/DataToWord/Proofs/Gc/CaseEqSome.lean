module

public import Flapjack.HolRef
@[expose] public section

/-! Option-case equality used by the data-to-word correctness proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- An option case returns SOME exactly when its selected branch does. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "case_EQ_SOME_IFF"]
theorem optionCase_eq_some {α β : Type} (p : Option β) (g : β → Option α) (y : α) :
    (match p with | none => none | some x => g x) = some y ↔
      ∃ x, p = some x ∧ g x = some y := by
  cases p <;> simp
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
