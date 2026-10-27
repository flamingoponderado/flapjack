import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.FlatSem.Thunk
import Flapjack.SemanticPrimitivesHOL.Thunk

/-! Thunk simulation over the factored source-to-flat value and state relations.
Full HOL correspondence of those relations remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- Flapjack-specific relation between source and flat thunk inspection results. -/
inductive DestThunkRel (genv : GlobalEnv) : SemanticPrimitivesHOL.DestThunkResult →
    FlatSem.DestThunkResult → Prop where
  | badRef : DestThunkRel genv .badRef .badRef
  | notThunk : DestThunkRel genv .notThunk .notThunk
  | isThunk (mode) {source flat} (related : ValueRel genv source flat) :
      DestThunkRel genv (.isThunk mode source) (.isThunk mode flat)

/-- Related singleton values have related thunk inspection results. This is
infrastructure over the factored state and value relations. -/
theorem destThunk_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (valueRel : ValueRel genv source flat) :
    DestThunkRel genv (SemanticPrimitivesHOL.destThunk [source] sourceState.refs)
      (FlatSem.destThunk [flat] flatState.refs) := by
  cases valueRel <;> try (exact .notThunk)
  case location n flag =>
    have lookupRel := stateRel_lookup genv sourceState flatState stateRel n
    cases hsrc : storeLookup n sourceState.refs with
    | none =>
      cases hflat : storeLookup (n + 1) flatState.refs with
      | none => simpa [SemanticPrimitivesHOL.destThunk, FlatSem.destThunk, hsrc, hflat] using DestThunkRel.badRef (genv := genv)
      | some value => simp [LookupRel, hsrc, hflat] at lookupRel
    | some sourceValue =>
      cases hflat : storeLookup (n + 1) flatState.refs with
      | none => simp [LookupRel, hsrc, hflat] at lookupRel
      | some flatValue =>
        simp only [LookupRel, hsrc, hflat] at lookupRel
        cases lookupRel with
        | refv valueRel =>
          simpa [SemanticPrimitivesHOL.destThunk, FlatSem.destThunk, hsrc, hflat] using DestThunkRel.notThunk (genv := genv)
        | w8array bytes =>
          simpa [SemanticPrimitivesHOL.destThunk, FlatSem.destThunk, hsrc, hflat] using DestThunkRel.notThunk (genv := genv)
        | varray valuesRel =>
          simpa [SemanticPrimitivesHOL.destThunk, FlatSem.destThunk, hsrc, hflat] using DestThunkRel.notThunk (genv := genv)
        | thunk mode valueRel =>
          cases flag <;> simp [SemanticPrimitivesHOL.destThunk, FlatSem.destThunk, hsrc, hflat]
          · exact .isThunk mode valueRel
          · exact .badRef

/-- Related values agree on whether an evaluated-thunk update is invalid.
This is infrastructure over the factored state and value relations. -/
theorem badThunkUpdate_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (mode : AstHOL.ThunkMode)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (valueRel : ValueRel genv source flat) :
    SemanticPrimitivesHOL.badThunkUpdate mode source sourceState.refs =
      FlatSem.badThunkUpdate mode flat flatState.refs := by
  have related := destThunk_related genv sourceState flatState stateRel source flat valueRel
  cases mode with
  | notEvaluated => rfl
  | evaluated =>
    simp only [SemanticPrimitivesHOL.badThunkUpdate, FlatSem.badThunkUpdate, if_true]
    generalize hs : SemanticPrimitivesHOL.destThunk [source] sourceState.refs = sourceResult at related ⊢
    generalize hf : FlatSem.destThunk [flat] flatState.refs = flatResult at related ⊢
    cases related <;> rfl

end Flapjack.Compiler.Backend.SourceToFlat
