module

public import Flapjack.Compiler.Backend.BviToData.Assign
public import Flapjack.Compiler.Backend.BviToData.CompileSource
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels
public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels

@[expose] public section

/-! Code labels introduced by BVI-to-data compilation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Lowering an operation preserves the set of labels it references. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_code_labels_iAssign"]
theorem getCodeLabels_iAssign (a : Nat) (b : ClosLang.Op) (c d e : List Nat) :
    DataSem.getCodeLabels (iAssign a b c d e) = ClosLang.assignGetCodeLabel b := by
  cases b <;> simp only [iAssign] <;> split <;> try split <;> try split <;>
    simp_all [DataSem.getCodeLabels, ClosLang.assignGetCodeLabel]
  all_goals simp [DataSem.getCodeLabels, ClosLang.assignGetCodeLabel]

/-- Compiling expressions introduces no code labels absent from the source. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_code_labels_compile"]
theorem getCodeLabels_compile (n : Nat) (env : List Nat) (tail : Bool)
    (live : List Nat) (xs : List Bvi.Exp) :
    DataSem.getCodeLabels (compileSource n env tail live xs).1 ⊆
      ⋃₀ (BviProps.getCodeLabels '' {e | e ∈ xs}) := by
  rw [← BviProps.getCodeLabelsList_eq]
  have ticksEq (count : Nat) (program : DataLang.Prog) :
      DataSem.getCodeLabels (DataLang.mkTicks count program) = DataSem.getCodeLabels program := by
    induction count with
    | zero => rfl
    | succ count ih => simpa [DataLang.mkTicks, DataSem.getCodeLabels] using ih
  fun_induction compileSource n env tail live xs <;>
    simp_all [DataSem.getCodeLabels, BviProps.getCodeLabels, BviProps.getCodeLabelsList,
      Set.subset_def] <;> try aesop (config := { warnOnNonterminal := false })
  all_goals try simp_all [DataSem.getCodeLabels, getCodeLabels_iAssign]
  all_goals aesop

end Flapjack.Compiler.Backend.BviToData
