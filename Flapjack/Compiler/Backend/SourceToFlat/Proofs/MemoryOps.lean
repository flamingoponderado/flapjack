import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreUpdate
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory
import Flapjack.SemanticPrimitivesHOL.Apply

/-! Reference and array simulation over the factored source-to-flat relations.
The complete primitive-application theorem remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- Flapjack list infrastructure: replication preserves a pointwise relation. -/
theorem forall₂_replicate {α β : Type} {R : α → β → Prop} (n : Nat) (x : α) (y : β)
    (related : R x y) : List.Forall₂ R (List.replicate n x) (List.replicate n y) := by
  induction n with
  | zero => exact .nil
  | succ n ih => simpa only [List.replicate_succ] using List.Forall₂.cons related ih

/-- Reference allocation produces related locations and states, preserving the
reserved flat store entry. This is Flapjack infrastructure over the factored
relations and the partial primitive dispatchers. -/
theorem opref_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (source : SemanticPrimitivesHOL.Value)
    (flat : FlatSem.Value) (valueRel : ValueRel genv source flat) :
    let sourceAlloc := storeAlloc (.refv source) sourceState.refs
    let flatAlloc := storeAlloc (.refv flat) flatState.refs
    doAppBasic (sourceState.refs, sourceState.ffi) .opref [source] =
      some (some ((sourceAlloc.1, sourceState.ffi), .val (.loc true sourceAlloc.2))) ∧
    FlatSem.doAppMemory flatState .opref [flat] =
      some (some ({ flatState with refs := flatAlloc.1 }, .val (.loc true flatAlloc.2))) ∧
    ValueRel genv (.loc true sourceAlloc.2) (.loc true flatAlloc.2) ∧
    StateRel genv { sourceState with refs := sourceAlloc.1 } { flatState with refs := flatAlloc.1 } ∧
    flatAlloc.1.take 1 = flatState.refs.take 1 := by
  have ⟨nextRel, offset, reserved⟩ := stateRel_storeAlloc genv sourceState flatState statesRel
    (.refv source) (.refv flat) (.refv valueRel)
  dsimp only
  refine ⟨rfl, rfl, ?_, nextRel, reserved⟩
  rw [offset]
  exact .location genv _ true

/-- Successful reference assignment is simulated at the one-slot-shifted
flat address. This is Flapjack infrastructure over the factored relations and
the partial primitive dispatchers. -/
theorem opassign_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (flag : Bool) (n : Nat)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) (valueRel : ValueRel genv source flat)
    (sourceRefs : Store SemanticPrimitivesHOL.Value)
    (assigned : storeAssign n (.refv source) sourceState.refs = some sourceRefs) :
    ∃ flatRefs,
      doAppBasic (sourceState.refs, sourceState.ffi) .opassign [.loc flag n, source] =
        some (some ((sourceRefs, sourceState.ffi), .val (.conv none []))) ∧
      FlatSem.doAppMemory flatState .opassign [.loc flag (n + 1), flat] =
        some (some ({ flatState with refs := flatRefs }, .val FlatSem.unitValue)) ∧
      ValueRel genv (.conv none []) FlatSem.unitValue ∧
      StateRel genv { sourceState with refs := sourceRefs } { flatState with refs := flatRefs } ∧
      flatRefs.take 1 = flatState.refs.take 1 := by
  obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ :=
    stateRel_storeAssign genv sourceState flatState statesRel n (.refv source) (.refv flat)
      (.refv valueRel) sourceRefs assigned
  refine ⟨flatRefs, ?_, ?_, ?_, nextRel, reserved⟩
  · simp [doAppBasic, assigned]
  · simp [FlatSem.doAppMemory, flatAssigned]
  · exact .tuple genv [] [] (.nil genv)

/-- Nonnegative array allocation preserves the value relation, the one-slot
address offset, the state relation, and the reserved flat entry. This is
Flapjack infrastructure over the factored relations and partial dispatchers. -/
theorem aalloc_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (size : Int) (nonnegative : 0 ≤ size)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) (valueRel : ValueRel genv source flat) :
    let sourceAlloc := storeAlloc (.varray (List.replicate size.toNat source)) sourceState.refs
    let flatAlloc := storeAlloc (.varray (List.replicate size.toNat flat)) flatState.refs
    doAppBasic (sourceState.refs, sourceState.ffi) .aalloc [.litv (.intLit size), source] =
      some (some ((sourceAlloc.1, sourceState.ffi), .val (.loc true sourceAlloc.2))) ∧
    FlatSem.doAppMemory flatState .aalloc [.litv (.intLit size), flat] =
      some (some ({ flatState with refs := flatAlloc.1 }, .val (.loc true flatAlloc.2))) ∧
    ValueRel genv (.loc true sourceAlloc.2) (.loc true flatAlloc.2) ∧
    StateRel genv { sourceState with refs := sourceAlloc.1 } { flatState with refs := flatAlloc.1 } ∧
    flatAlloc.1.take 1 = flatState.refs.take 1 := by
  have ⟨nextRel, offset, reserved⟩ := stateRel_storeAlloc genv sourceState flatState statesRel
    (.varray (List.replicate size.toNat source)) (.varray (List.replicate size.toNat flat))
    (.varray (forall₂_replicate size.toNat source flat valueRel))
  dsimp only
  have notNegative : ¬size < 0 := Int.not_lt.mpr nonnegative
  refine ⟨?_, ?_, ?_, nextRel, reserved⟩
  · simp [doAppBasic, notNegative]
  · simp [FlatSem.doAppMemory, notNegative]
  · rw [offset]
    exact .location genv _ true

end Flapjack.Compiler.Backend.SourceToFlat
