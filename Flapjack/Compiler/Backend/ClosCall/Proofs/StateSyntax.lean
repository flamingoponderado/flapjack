module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain

@[expose] public section

/-! Syntax properties of the direct-call compiler's accumulated code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_syntax_def"]
def stateSyntax (f : Exp → Prop) (g : State) : Prop :=
  ∀ entry ∈ g.2, f entry.2.2

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_syntax_insert_each"]
theorem stateSyntax_insertEach (f : Exp → Prop) (k loc : Nat) (g : State) :
    stateSyntax f (insertEachSource loc k g) ↔ stateSyntax f g := by
  simp only [stateSyntax, insertEach_snd]

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "state_syntax_code_list"]
theorem stateSyntax_codeList (f : Exp → Prop) (n : Nat) (xs : List (Nat × Exp)) (g : State) :
    stateSyntax f (codeListSource n xs g) ↔ stateSyntax f g ∧ ∀ e ∈ xs.map Prod.snd, f e := by
  induction xs generalizing n g with
  | nil => simp [codeListSource, stateSyntax]
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    cases g with
    | mk tree entries =>
      rw [codeListSource, ih]
      simp [stateSyntax, and_assoc, and_left_comm, and_comm]

end Flapjack.Compiler.Backend.ClosCall
