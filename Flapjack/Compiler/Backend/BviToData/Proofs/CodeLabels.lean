module

public import Flapjack.Compiler.Backend.BviToData.Assign
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels

@[expose] public section

/-! Code labels introduced by BVI-to-data compilation. -/
namespace Flapjack.Compiler.Backend.BviToData

/-- Lowering an operation preserves the set of labels it references. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_code_labels_iAssign"]
theorem getCodeLabels_iAssign (a : Nat) (b : ClosLang.Op) (c d e : List Nat) :
    DataSem.getCodeLabels (iAssign a b c d e) = ClosLang.assignGetCodeLabel b := by
  cases b <;> simp only [iAssign] <;> split <;> try split <;> try split <;>
    simp_all [DataSem.getCodeLabels, ClosLang.assignGetCodeLabel]
  all_goals simp [DataSem.getCodeLabels, ClosLang.assignGetCodeLabel]

end Flapjack.Compiler.Backend.BviToData
