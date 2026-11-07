import Flapjack.Compiler.Backend.Semantics.DataSem.Space

/-! Space-accounting prerequisites for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack

/-- Successful data-language space accounting preserves both the code tree and
the compiler oracle. A typed replay of the original confirms the independent
state parameters and the same premise and equalities. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "do_space_code_const"]
theorem doSpace_code_const {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : DataSem.State C F) (run : DataSem.doSpace op values state = some next) :
    next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  unfold DataSem.doSpace at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    exact ⟨rfl, rfl⟩
  · dsimp only at run
    split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨rfl, rfl⟩
    · unfold DataSem.consumeSpace at run
      split at run
      · contradiction
      · simp only [Option.some.injEq] at run
        subst next
        exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
