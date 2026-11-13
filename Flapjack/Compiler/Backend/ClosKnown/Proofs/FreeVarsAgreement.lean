module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.FreeVars
public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect

@[expose] public section

/-! Free-variable agreement for the known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- The computed variable-set tree contains exactly the free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv_alt"]
theorem fvAlt (n : Nat) (xs : List Exp) :
    freeVars n xs ↔ DbVars.hasVar n (freeHOL xs).2 = true := by
  exact (ClosCall.freeThm xs n).2

/-- The singleton free-variable predicate has the same computed membership. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fv1_alt"]
theorem fv1Alt (n : Nat) (x : Exp) :
    freeVar n x ↔ DbVars.hasVar n (freeHOL [x]).2 = true :=
  fvAlt n [x]

end Flapjack.Compiler.Backend.ClosKnown
