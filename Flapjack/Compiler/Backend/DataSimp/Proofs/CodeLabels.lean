module

public import Flapjack.Compiler.Backend.DataSimp
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Code-label preservation by DATA sequencing simplification. -/
namespace Flapjack.Compiler.Backend.DataSimp

/-- Simplification introduces no label absent from its input or continuation. -/
@[hol "cakeml/compiler/backend/proofs/data_simpProofScript.sml" "get_code_labels_simp"]
theorem getCodeLabels_simp (x y : DataLang.Prog) :
    DataSem.getCodeLabels (simp x y) ⊆ DataSem.getCodeLabels x ∪ DataSem.getCodeLabels y := by
  fun_induction simp x y <;>
    simp_all [pSeq, DataSem.getCodeLabels, Set.subset_def] <;>
    try aesop (config := { warnOnNonterminal := false })
  all_goals try simp_all [DataSem.getCodeLabels]
  all_goals try aesop (config := { warnOnNonterminal := false })
  all_goals
    rcases ih1 x a with hp | hq
    · exact Or.inl (Or.inl hp)
    · rcases ih2 x hq with hq | hc
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hc

end Flapjack.Compiler.Backend.DataSimp
