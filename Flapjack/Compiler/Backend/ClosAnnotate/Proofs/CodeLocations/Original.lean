import Flapjack.Compiler.Backend.ClosAnnotate.Original

/-! Label preservation for the original closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- Original annotation preserves the labels of a program. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "MAP_FST_compile"]
theorem mapFst_compile {α : Type} (program : List (α × Nat × Exp)) :
    (compileSource program).map Prod.fst = program.map Prod.fst := by
  simp [compileSource, List.map_map]

end Flapjack.Compiler.Backend.ClosAnnotate
