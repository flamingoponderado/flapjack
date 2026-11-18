module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! The total cut-locals operation used by data-to-word GC proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Cut the locals when possible; otherwise replace them with the empty tree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_locals_def"]
noncomputable def cutLocals {C F : Type} (names : NumSet) (state : DataSem.State C F) : DataSem.State C F :=
  match DataSem.cutEnv names state.locals with
  | some env => { state with locals := env }
  | none => { state with locals := .ln }

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
