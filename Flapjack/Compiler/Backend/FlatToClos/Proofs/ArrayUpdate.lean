import Flapjack.Compiler.Backend.FlatToClos.Proofs.ArrayRead

/-! Array-update prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Replacing corresponding elements preserves a list relation. -/
theorem valueList_set_related {source : List FlatSem.Value} {target : List ClosSem.Value}
    (related : List.Forall₂ ValueRel source target) (index : Nat) (bound : index < source.length)
    (value : FlatSem.Value) (targetValue : ClosSem.Value) (valueRel : ValueRel value targetValue) :
    List.Forall₂ ValueRel (source.set index value) (target.set index targetValue) := by
  induction related generalizing index with
  | nil => simp at bound
  | cons item tail ih =>
    cases index with
    | zero => simpa using List.Forall₂.cons valueRel tail
    | succ index =>
      apply List.Forall₂.cons item
      apply ih
      simpa using bound

/-- Replacing an existing value array with a related one preserves the store relation. -/
theorem storeRel_setArray (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (pointer : Nat)
    (old new : List FlatSem.Value) (targetNew : List ClosSem.Value)
    (stores : StoreRel refs targetRefs) (found : refs[pointer]? = some (.varray old))
    (related : List.Forall₂ ValueRel new targetNew) :
    StoreRel (refs.set pointer (.varray new)) (targetRefs.updateEq (pointer, .valueArray targetNew)) := by
  have bound : pointer < refs.length := (List.getElem?_eq_some_iff.mp found).choose
  intro key
  by_cases same : pointer = key
  · subst key
    simp [bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, related]
  · have previous := stores key
    simpa [List.getElem?_set, same, Ne.symm same, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL] using previous

/-- Replacing an existing byte array with the same bytes preserves the store relation. -/
theorem storeRel_setByteArray (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (pointer : Nat)
    (old new : List (BitVec 8)) (stores : StoreRel refs targetRefs)
    (found : refs[pointer]? = some (.w8array old)) :
    StoreRel (refs.set pointer (.w8array new)) (targetRefs.updateEq (pointer, .byteArray new)) := by
  have bound : pointer < refs.length := (List.getElem?_eq_some_iff.mp found).choose
  intro key
  by_cases same : pointer = key
  · subst key
    simp [bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL]
  · have previous := stores key
    simpa [List.getElem?_set, same, Ne.symm same, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL] using previous

/-- A valid update of a value-array element preserves related states and
returns unit on both sides, for checked and unchecked source primitives. -/
theorem arrayUpdate_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int)
    (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (found : source.refs[pointer]? = some (.varray items))
    (nonnegative : ¬index < 0) (bound : index.toNat < items.length) (valueRel : ValueRel value targetValue) :
    ∃ targetNext,
      FlatSem.doAppMemory source .aupdate [.loc flag pointer, .litv (.intLit index), value] =
        some (some ({ source with refs := source.refs.set pointer (.varray (items.set index.toNat value)) }, .val FlatSem.unitValue)) ∧
      FlatSem.doAppMemory source .aupdateUnsafe [.loc flag pointer, .litv (.intLit index), value] =
        some (some ({ source with refs := source.refs.set pointer (.varray (items.set index.toNat value)) }, .val FlatSem.unitValue)) ∧
      ClosSem.applyMemory .update [.refPtr flag pointer, .number index, targetValue] target =
        some (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set pointer (.varray (items.set index.toNat value)) } targetNext := by
  obtain ⟨targetItems, targetFound, related⟩ := lookup_array states found
  have sameLength := related.length_eq
  have targetBound : index.toNat < targetItems.length := by omega
  have notBound : ¬items.length ≤ index.toNat := by omega
  have newRelated := valueList_set_related related index.toNat bound value targetValue valueRel
  have newStores := storeRel_setArray source.refs target.refs pointer items _ _ states.2.2.2.1 found newRelated
  refine ⟨{ target with refs := target.refs.updateEq (pointer, .valueArray (targetItems.set index.toNat targetValue)) }, ?_, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, storeLookup, found, nonnegative, notBound,
      storeAssign, storeValueSameType]
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, storeLookup, found, nonnegative, notBound,
      storeAssign, storeValueSameType]
  · simp [ClosSem.applyMemory, targetFound, nonnegative, targetBound]
  · rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
    exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩

/-- A valid byte-array update writes the same byte in both stores and
returns unit for checked and unchecked source primitives. -/
theorem byteArrayUpdate_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (states : StateRel source target) (found : source.refs[pointer]? = some (.w8array bytes))
    (nonnegative : ¬index < 0) (bound : index.toNat < bytes.length) :
    ∃ targetNext,
      FlatSem.doAppMemory source .aw8update [.loc flag pointer, .litv (.intLit index), .litv (.word8 byte)] =
        some (some ({ source with refs := source.refs.set pointer (.w8array (bytes.set index.toNat byte)) }, .val FlatSem.unitValue)) ∧
      FlatSem.doAppMemory source .aw8updateUnsafe [.loc flag pointer, .litv (.intLit index), .litv (.word8 byte)] =
        some (some ({ source with refs := source.refs.set pointer (.w8array (bytes.set index.toNat byte)) }, .val FlatSem.unitValue)) ∧
      ClosSem.applyMemory .updateByte [.refPtr flag pointer, .number index, .number byte.toNat] target =
        some (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set pointer (.w8array (bytes.set index.toNat byte)) } targetNext := by
  have targetFound := lookup_byteArray states found
  have notBound : ¬bytes.length ≤ index.toNat := by omega
  have newStores := storeRel_setByteArray source.refs target.refs pointer bytes (bytes.set index.toNat byte) states.2.2.2.1 found
  refine ⟨{ target with refs := target.refs.updateEq (pointer, .byteArray (bytes.set index.toNat byte)) }, ?_, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, storeLookup, found, nonnegative, notBound,
      storeAssign, storeValueSameType]
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, storeLookup, found, nonnegative, notBound,
      storeAssign, storeValueSameType]
  · simp [ClosSem.applyMemory, targetFound, nonnegative, notBound, ClosSem.intToByte_toNat]
  · rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
    exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩

/-- Invalid checked value-array writes raise Subscript; unchecked writes
report a type error at the primitive boundary. -/
theorem arrayUpdate_outOfBounds {C F : Type} (source : FlatSem.State C F)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int) (value : FlatSem.Value)
    (found : source.refs[pointer]? = some (.varray items))
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    FlatSem.doAppMemory source .aupdate [.loc flag pointer, .litv (.intLit index), value] =
      some (some (source, .err (.raise FlatSem.subscriptExnV))) ∧
    FlatSem.doAppMemory source .aupdateUnsafe [.loc flag pointer, .litv (.intLit index), value] = some none := by
  rcases bad with negative | bound
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative]
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, bound]

/-- Invalid checked byte-array writes raise Subscript; unchecked writes
report a type error at the primitive boundary. -/
theorem byteArrayUpdate_outOfBounds {C F : Type} (source : FlatSem.State C F)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (found : source.refs[pointer]? = some (.w8array bytes))
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    FlatSem.doAppMemory source .aw8update [.loc flag pointer, .litv (.intLit index), .litv (.word8 byte)] =
      some (some (source, .err (.raise FlatSem.subscriptExnV))) ∧
    FlatSem.doAppMemory source .aw8updateUnsafe [.loc flag pointer, .litv (.intLit index), .litv (.word8 byte)] = some none := by
  rcases bad with negative | bound
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative]
  · simp [FlatSem.doAppMemory, FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, bound]

end Flapjack.Compiler.Backend.FlatToClos
