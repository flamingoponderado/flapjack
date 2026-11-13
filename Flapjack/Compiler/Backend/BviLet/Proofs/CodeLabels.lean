module

public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels
public import Flapjack.Compiler.Backend.BviLet.Helpers

@[expose] public section

/-! Code-label preservation for BVI let propagation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs

/-- Deleting a propagated variable preserves its code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "dest_var_code_labels"]
theorem deleteVar_codeLabels (x : Bvi.Exp) :
    BviProps.getCodeLabels (deleteVar x) = BviProps.getCodeLabels x := by
  cases x <;> simp [deleteVar, BviProps.getCodeLabels, BviProps.getCodeLabelsList,
    ClosLang.assignGetCodeLabel]

end Flapjack.Compiler.Backend.BviLet.Proofs
