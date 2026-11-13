module

public import Flapjack.Compiler.Backend.BvlToBvi.Analysis
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels
public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels

@[expose] public section

/-! Code-label facts for the BVL-to-BVI conversion. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Decomposing a source let does not introduce code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "destLet_code_labels"]
theorem destLet_codeLabels (x : Bvl.Exp) (y : List Bvl.Exp) (z : Bvl.Exp)
    (decomposed : destLet x = (y, z)) :
    (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ y})) ∪ BvlProps.getCodeLabels z ⊆
      BvlProps.getCodeLabels x := by
  rw [← BvlProps.getCodeLabelsList_eq]
  cases x <;> simp only [destLet, Prod.mk.injEq] at decomposed <;>
    rcases decomposed with ⟨rfl, rfl⟩ <;>
    simp [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList]

/-- Compiling an integer introduces no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_int_code_labels"]
theorem compileInt_codeLabels (i : Int) : BviProps.getCodeLabels (compileInt i) = ∅ := by
  unfold compileInt
  split <;> simp [BviProps.getCodeLabels, BviProps.getCodeLabelsList, ClosLang.assignGetCodeLabel]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
