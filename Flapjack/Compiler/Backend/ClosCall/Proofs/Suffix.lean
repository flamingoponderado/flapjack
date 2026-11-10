module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList

@[expose] public section

/-! Preservation of previously generated direct-call code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- Generating auxiliary code retains the previous code as a suffix. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_list_IS_SUFFIX"]
theorem codeListSource_suffix {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) : state.2 <:+ (codeListSource loc fns state).2 := by
  induction fns generalizing loc state with
  | nil => simp [codeListSource]
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    obtain ⟨known, code⟩ := state
    change code <:+ (codeListSource (loc + 2) rest
      (known, (loc + 1, arity, body) :: code)).2
    exact (List.suffix_cons (loc + 1, arity, body) code).trans
      (ih (loc + 2) (known, (loc + 1, arity, body) :: code))

end Flapjack.Compiler.Backend.ClosCall
