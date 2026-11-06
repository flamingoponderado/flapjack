import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkRelation

/-! Thunk forcing for the flat pattern compiler. The evaluator and proof-side
relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)
open Flapjack.Basis.Pure.MlString (ofString)

/-- The generated call for forcing a thunk is unchanged by compilation. -/
theorem compile_forceBody (cfg : Config) :
    (compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).2.2 =
      FlatSem.appUnit (.varLocal .none (ofString "f")) := by
  simp [FlatSem.appUnit, compileExp, compileExps]

/-- The environments constructed for forcing related thunks are related at
every name bound. -/
theorem forceBody_envRel (n : Nat) (value value' : FlatSem.Value) (related : ValueRel value value') :
    EnvRel n ⟨[(ofString "f", value)]⟩ ⟨[(ofString "f", value')]⟩ := by
  apply (envRel_iff_lookup _ _ _).2
  apply aLookupRel_cons
  · intro _
    exact related
  · exact aLookupRel_empty _ _

end Flapjack.Compiler.Backend.FlatPattern
