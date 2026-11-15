module

public import Flapjack.Compiler.Backend.BvlToBvi.Analysis
public import Flapjack.Compiler.Backend.BvlToBvi.Stubs
import all Flapjack.Compiler.Backend.BvlToBvi.CompileOp
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

/-- Compiling an operation uses operand labels, translated operation labels, and stub labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_op_code_labels"]
theorem compileOp_codeLabels (op : ClosLang.Op) (c : List Bvi.Exp) (x y : Nat) :
    BviProps.getCodeLabels (compileOp op c) ⊆
      (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ c})) ∪
      ((fun n => bvlNumStubs + n * bvlToBviNamespaces) '' ClosLang.assignGetCodeLabel op) ∪
      {n | n ∈ (stubs x y).map Prod.fst} := by
  rw [← BviProps.getCodeLabelsList_eq]
  intro label member
  cases op
  all_goals try (cases ‹ClosLang.IntOp›)
  all_goals try (cases ‹ClosLang.BlockOp›)
  all_goals try (cases ‹ClosLang.GlobOp›)
  all_goals try (cases ‹ClosLang.MemOp›)
  all_goals try (cases ‹Bool›)
  all_goals simp_all [compileOp, argsOrZero, listLength, zero,
    BviProps.getCodeLabels, BviProps.getCodeLabelsList, ClosLang.assignGetCodeLabel, stubs,
    Nat.mul_comm]
  all_goals repeat' first | split at member | split at *
  all_goals try simp_all [compileInt_codeLabels, BviProps.getCodeLabelsList_eq,
    BviProps.getCodeLabels, ClosLang.assignGetCodeLabel]
  all_goals aesop

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
