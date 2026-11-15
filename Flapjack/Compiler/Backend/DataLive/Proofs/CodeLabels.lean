module

public import Flapjack.Compiler.Backend.DataLive
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Code-label preservation by DATA liveness compilation. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack

/-- Liveness compilation introduces no code label. -/
@[hol "cakeml/compiler/backend/proofs/data_liveProofScript.sml" "get_code_labels_compile"]
theorem getCodeLabels_compile (program : DataLang.Prog) (live : NumSet) :
    DataSem.getCodeLabels (compile program live).1 ⊆ DataSem.getCodeLabels program := by
  fun_induction compile program live <;>
    simp_all [DataSem.getCodeLabels, Set.subset_def] <;>
    try aesop (config := { warnOnNonterminal := false })

end Flapjack.Compiler.Backend.DataLive
