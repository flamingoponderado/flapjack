import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreUpdate
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
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

/-- Byte-array allocation simulates the source allocation and preserves the
reserved flat store entry. This uses the factored, unreviewed relations. -/
theorem aw8alloc_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (size : Int) (nonnegative : 0 ≤ size)
    (value : BitVec 8) :
    let sourceAlloc := storeAlloc (.w8array (List.replicate size.toNat value)) sourceState.refs
    let flatAlloc := storeAlloc (.w8array (List.replicate size.toNat value)) flatState.refs
    doAppBasic (sourceState.refs, sourceState.ffi) .aw8alloc [.litv (.intLit size), .litv (.word8 value)] =
      some (some ((sourceAlloc.1, sourceState.ffi), .val (.loc true sourceAlloc.2))) ∧
    FlatSem.doAppMemory flatState .aw8alloc [.litv (.intLit size), .litv (.word8 value)] =
      some (some ({ flatState with refs := flatAlloc.1 }, .val (.loc true flatAlloc.2))) ∧
    ValueRel genv (.loc true sourceAlloc.2) (.loc true flatAlloc.2) ∧
    StateRel genv { sourceState with refs := sourceAlloc.1 } { flatState with refs := flatAlloc.1 } ∧
    flatAlloc.1.take 1 = flatState.refs.take 1 := by
  have ⟨nextRel, offset, reserved⟩ := stateRel_storeAlloc genv sourceState flatState statesRel
    (.w8array (List.replicate size.toNat value)) (.w8array (List.replicate size.toNat value))
    (.w8array (List.replicate size.toNat value))
  dsimp only
  have notNegative : ¬size < 0 := Int.not_lt.mpr nonnegative
  refine ⟨?_, ?_, ?_, nextRel, reserved⟩
  · simp [doAppBasic, notNegative]
  · simp [FlatSem.doAppMemory, notNegative]
  · rw [offset]
    exact .location genv _ true

/-- Fixed array allocation preserves related elements and states. This is
Flapjack infrastructure over the partial primitive dispatchers. -/
theorem aallocFixed_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState)
    (source : List SemanticPrimitivesHOL.Value) (flat : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) source flat) :
    let sourceAlloc := storeAlloc (.varray source) sourceState.refs
    let flatAlloc := storeAlloc (.varray flat) flatState.refs
    doAppBasic (sourceState.refs, sourceState.ffi) .aallocFixed source =
      some (some ((sourceAlloc.1, sourceState.ffi), .val (.loc true sourceAlloc.2))) ∧
    FlatSem.doAppMemory flatState .aallocFixed flat =
      some (some ({ flatState with refs := flatAlloc.1 }, .val (.loc true flatAlloc.2))) ∧
    ValueRel genv (.loc true sourceAlloc.2) (.loc true flatAlloc.2) ∧
    StateRel genv { sourceState with refs := sourceAlloc.1 } { flatState with refs := flatAlloc.1 } ∧
    flatAlloc.1.take 1 = flatState.refs.take 1 := by
  have ⟨nextRel, offset, reserved⟩ := stateRel_storeAlloc genv sourceState flatState statesRel
    (.varray source) (.varray flat) (.varray valuesRel)
  dsimp only
  refine ⟨rfl, rfl, ?_, nextRel, reserved⟩
  rw [offset]
  exact .location genv _ true

/-- Byte-array length returns the same literal from related states. This is
Flapjack infrastructure over the partial primitive dispatchers. -/
theorem aw8length_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes)) :
    doAppBasic (sourceState.refs, sourceState.ffi) .aw8length [.loc flag n] =
      some (some ((sourceState.refs, sourceState.ffi), .val (.litv (.intLit bytes.length)))) ∧
    FlatSem.doAppMemory flatState .aw8length [.loc flag (n + 1)] =
      some (some (flatState, .val (.litv (.intLit bytes.length)))) ∧
    ValueRel genv (.litv (.intLit bytes.length)) (.litv (.intLit bytes.length)) := by
  have flatLookup := stateRel_byteArray_lookup genv sourceState flatState statesRel n bytes lookup
  exact ⟨by simp [doAppBasic, lookup], by simp [FlatSem.doAppMemory, flatLookup],
    .literal genv _⟩

/-- A valid byte-array subscript returns the same byte in the source and flat
states. This covers both checked and unchecked source operations. -/
theorem aw8sub_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (nonnegative : 0 ≤ index) (byte : BitVec 8)
    (element : bytes[index.toNat]? = some byte) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8subUnsafe else .aw8sub
    doAppBasic (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)] =
      some (some ((sourceState.refs, sourceState.ffi), .val (.litv (.word8 byte)))) ∧
    FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] =
      some (some (flatState, .val (.litv (.word8 byte)))) ∧
    ValueRel genv (.litv (.word8 byte)) (.litv (.word8 byte)) := by
  have flatLookup := stateRel_byteArray_lookup genv sourceState flatState statesRel n bytes lookup
  have notNegative : ¬index < 0 := Int.not_lt.mpr nonnegative
  cases unsafeOp <;>
    simp [doAppBasic, FlatSem.doAppMemory, SemanticPrimitivesHOL.readIndexed,
      FlatSem.readIndexed, lookup, flatLookup, notNegative, element, ValueRel.literal genv (.word8 byte)]

/-- For an invalid byte-array subscript, both dispatchers raise related
subscript exceptions in checked mode and fail in unchecked mode. -/
theorem aw8sub_outOfBounds {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (outOfBounds : index < 0 ∨ bytes[index.toNat]? = none) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8subUnsafe else .aw8sub
    doAppBasic (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)] =
      some (if unsafeOp then none else some ((sourceState.refs, sourceState.ffi), .err (.raise subExnV))) ∧
    FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] =
      some (if unsafeOp then none else some (flatState, .err (.raise FlatSem.subscriptExnV))) ∧
    ValueRel genv subExnV FlatSem.subscriptExnV := by
  have flatLookup := stateRel_byteArray_lookup genv sourceState flatState statesRel n bytes lookup
  have exceptionRel := (exceptionValues_related genv ok).2.2.2
  rcases outOfBounds with negative | absent <;> cases unsafeOp <;>
    simp [doAppBasic, FlatSem.doAppMemory, SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed,
      SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, *]

/-- A valid byte-array update is simulated at the shifted flat address,
preserving related states and the reserved flat store entry. This covers both
checked and unchecked operations over the factored state relation. -/
theorem aw8update_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (nonnegative : 0 ≤ index) (inBounds : index.toNat < bytes.length)
    (byte : BitVec 8) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8updateUnsafe else .aw8update
    let sourceRefs := sourceState.refs.set n (.w8array (bytes.set index.toNat byte))
    ∃ flatRefs,
      doAppBasic (sourceState.refs, sourceState.ffi) op
        [.loc flag n, .litv (.intLit index), .litv (.word8 byte)] =
          some (some ((sourceRefs, sourceState.ffi), .val (.conv none []))) ∧
      FlatSem.doAppMemory flatState op
        [.loc flag (n + 1), .litv (.intLit index), .litv (.word8 byte)] =
          some (some ({ flatState with refs := flatRefs }, .val FlatSem.unitValue)) ∧
      ValueRel genv (.conv none []) FlatSem.unitValue ∧
      StateRel genv { sourceState with refs := sourceRefs } { flatState with refs := flatRefs } ∧
      flatRefs.take 1 = flatState.refs.take 1 := by
  have flatLookup := stateRel_byteArray_lookup genv sourceState flatState statesRel n bytes lookup
  have assigned : storeAssign n (.w8array (bytes.set index.toNat byte)) sourceState.refs =
      some (sourceState.refs.set n (.w8array (bytes.set index.toNat byte))) := by
    have lookup' : sourceState.refs[n]? = some (.w8array bytes) := lookup
    simp [storeAssign, lookup', storeValueSameType]
  obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ := stateRel_storeAssign genv sourceState flatState statesRel n
    (.w8array (bytes.set index.toNat byte)) (.w8array (bytes.set index.toNat byte))
    (.w8array (bytes.set index.toNat byte)) _ assigned
  have notNegative : ¬index < 0 := Int.not_lt.mpr nonnegative
  have notTooLarge : ¬bytes.length ≤ index.toNat := Nat.not_le.mpr inBounds
  refine ⟨flatRefs, ?_, ?_, .tuple genv [] [] (.nil genv), nextRel, reserved⟩
  · cases unsafeOp <;> simp [doAppBasic, SemanticPrimitivesHOL.updateIndexed, lookup,
      notNegative, notTooLarge, assigned]
  · cases unsafeOp <;> simp [FlatSem.doAppMemory, FlatSem.updateIndexed, flatLookup,
      notNegative, notTooLarge, flatAssigned]

/-- Invalid byte-array updates leave the states unchanged and produce related
exceptions in checked mode or failure in unchecked mode. -/
theorem aw8update_outOfBounds {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (outOfBounds : index < 0 ∨ bytes.length ≤ index.toNat)
    (byte : BitVec 8) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8updateUnsafe else .aw8update
    doAppBasic (sourceState.refs, sourceState.ffi) op
      [.loc flag n, .litv (.intLit index), .litv (.word8 byte)] =
        some (if unsafeOp then none else some ((sourceState.refs, sourceState.ffi), .err (.raise subExnV))) ∧
    FlatSem.doAppMemory flatState op
      [.loc flag (n + 1), .litv (.intLit index), .litv (.word8 byte)] =
        some (if unsafeOp then none else some (flatState, .err (.raise FlatSem.subscriptExnV))) ∧
    ValueRel genv subExnV FlatSem.subscriptExnV := by
  have flatLookup := stateRel_byteArray_lookup genv sourceState flatState statesRel n bytes lookup
  have exceptionRel := (exceptionValues_related genv ok).2.2.2
  rcases outOfBounds with negative | tooLarge <;> cases unsafeOp <;>
    simp [doAppBasic, FlatSem.doAppMemory, SemanticPrimitivesHOL.updateIndexed, FlatSem.updateIndexed,
      SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, *]

/-- A valid value-array update preserves related elements, states and the
reserved flat store entry in checked and unchecked modes. -/
theorem aupdate_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value)
    (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (nonnegative : 0 ≤ index) (inBounds : index.toNat < values.length)
    (value : SemanticPrimitivesHOL.Value) (flatValue : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aupdateUnsafe else .aupdate
    let sourceRefs := sourceState.refs.set n (.varray (values.set index.toNat value))
    ∃ flatRefs,
      doAppBasic (sourceState.refs, sourceState.ffi) op
        [.loc flag n, .litv (.intLit index), value] =
          some (some ((sourceRefs, sourceState.ffi), .val (.conv none []))) ∧
      FlatSem.doAppMemory flatState op
        [.loc flag (n + 1), .litv (.intLit index), flatValue] =
          some (some ({ flatState with refs := flatRefs }, .val FlatSem.unitValue)) ∧
      ValueRel genv (.conv none []) FlatSem.unitValue ∧
      StateRel genv { sourceState with refs := sourceRefs } { flatState with refs := flatRefs } ∧
      flatRefs.take 1 = flatState.refs.take 1 := by
  obtain ⟨flatValues, flatLookup, valuesRel⟩ :=
    stateRel_array_lookup genv sourceState flatState statesRel n values lookup
  have assigned : storeAssign n (.varray (values.set index.toNat value)) sourceState.refs =
      some (sourceState.refs.set n (.varray (values.set index.toNat value))) := by
    have lookup' : sourceState.refs[n]? = some (.varray values) := lookup
    simp [storeAssign, lookup', storeValueSameType]
  obtain ⟨flatRefs, flatAssigned, reserved, nextRel⟩ := stateRel_storeAssign genv sourceState flatState statesRel n
    (.varray (values.set index.toNat value)) (.varray (flatValues.set index.toNat flatValue))
    (.varray (forall₂_set valuesRel index.toNat value flatValue valueRel)) _ assigned
  have notNegative : ¬index < 0 := Int.not_lt.mpr nonnegative
  have notTooLarge : ¬values.length ≤ index.toNat := Nat.not_le.mpr inBounds
  have flatNotTooLarge : ¬flatValues.length ≤ index.toNat := by
    simpa [← valuesRel.length_eq] using notTooLarge
  refine ⟨flatRefs, ?_, ?_, .tuple genv [] [] (.nil genv), nextRel, reserved⟩
  · cases unsafeOp <;> simp [doAppBasic, SemanticPrimitivesHOL.updateIndexed, lookup,
      notNegative, notTooLarge, assigned]
  · cases unsafeOp <;> simp [FlatSem.doAppMemory, FlatSem.updateIndexed, flatLookup,
      notNegative, flatNotTooLarge, flatAssigned]

/-- Invalid value-array updates leave the states unchanged and produce related
exceptions in checked mode or failure in unchecked mode. -/
theorem aupdate_outOfBounds {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value)
    (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (outOfBounds : index < 0 ∨ values.length ≤ index.toNat)
    (value : SemanticPrimitivesHOL.Value) (flatValue : FlatSem.Value) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aupdateUnsafe else .aupdate
    doAppBasic (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index), value] =
      some (if unsafeOp then none else some ((sourceState.refs, sourceState.ffi), .err (.raise subExnV))) ∧
    FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index), flatValue] =
      some (if unsafeOp then none else some (flatState, .err (.raise FlatSem.subscriptExnV))) ∧
    ValueRel genv subExnV FlatSem.subscriptExnV := by
  obtain ⟨flatValues, flatLookup, valuesRel⟩ :=
    stateRel_array_lookup genv sourceState flatState statesRel n values lookup
  have exceptionRel := (exceptionValues_related genv ok).2.2.2
  rcases outOfBounds with negative | tooLarge
  · cases unsafeOp <;>
      simp [doAppBasic, FlatSem.doAppMemory, SemanticPrimitivesHOL.updateIndexed, FlatSem.updateIndexed,
        SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, *]
  · have flatTooLarge : flatValues.length ≤ index.toNat := by simpa [← valuesRel.length_eq] using tooLarge
    cases unsafeOp <;>
      simp [doAppBasic, FlatSem.doAppMemory, SemanticPrimitivesHOL.updateIndexed, FlatSem.updateIndexed,
        SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, *]

end Flapjack.Compiler.Backend.SourceToFlat
