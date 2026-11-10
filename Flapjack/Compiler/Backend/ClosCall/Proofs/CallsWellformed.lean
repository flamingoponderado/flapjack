module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateGrowth
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

@[expose] public section

/-! Well-formedness preservation by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- Direct-call conversion preserves the source one-sided code invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_wfg'"]
theorem calls_weaklyWellFormed (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g) ∧ everyFnLocationSome xs ∧ weaklyWellFormed g0) :
    weaklyWellFormed g := by
  have bounds := calls_codeSubset xs g0 ys g h.1
  intro label member
  rcases bounds.2.2 member with new | old
  · exact new
  · exact bounds.1 (h.2.2 old)

end Flapjack.Compiler.Backend.ClosCall
