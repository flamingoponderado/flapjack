module

public import Flapjack.HolRef

@[expose] public section

/-! Natural-order fact used by the flat elimination application proof. -/
namespace Flapjack.Compiler.Backend.FlatElim

@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "not_LE_LESS_IMP"]
theorem not_ge_implies_lt (x y : Nat) (notGe : ¬ x ≥ y) : x < y :=
  Nat.lt_of_not_ge notGe

end Flapjack.Compiler.Backend.FlatElim
