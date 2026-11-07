import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals

/-! Finite regression observations captured from the original HOL analysis. -/
namespace Flapjack.Test.FlatElimValueGlobals
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.FlatElim
open Flapjack.Basis.Pure.MlString

private def closure : FlatSem.Value :=
  .closure ⟨[]⟩ (ofString "x") (.app .none (.globalVarLookup 3) [])

#guard sptLookup 3 (findValueGlobals closure) == some ()
#guard sptLookup 3 (findValueGlobals (.conv none [closure])) == some ()
#guard sptLookup 4 (findValueGlobals closure) == none
#guard valueHasEval (.closure ⟨[]⟩ (ofString "x") (.app .none (.src .eval) []))
#guard !valueHasEval closure

end Flapjack.Test.FlatElimValueGlobals
