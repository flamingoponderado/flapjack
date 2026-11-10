module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ArrayRead
public import Flapjack.Misc.List

@[expose] public section

/-! Array-update prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

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
  have newRelated := Flapjack.forall₂_set ValueRel _ _ value targetValue index.toNat ⟨valueRel, related⟩
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

/-- The emitted checked byte write updates the target array for a valid index. -/
theorem evaluate_checkedByteUpdate_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (found : state.refs.lookup pointer = some (.byteArray bytes))
    (nonnegative : ¬index < 0) (bound : index.toNat < bytes.length) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
        (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number byte.toNat :: .number index :: .refPtr flag pointer :: env) state =
      (.val [ClosSem.unitValue], { state with refs := state.refs.updateEq (pointer, .byteArray (bytes.set index.toNat byte)) }) := by
  have valid : 0 ≤ index ∧ index < (bytes.length : Int) := by omega
  have notBound : ¬bytes.length ≤ index.toNat := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.intToByte_toNat, ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag,
    found, valid, nonnegative, notBound]

/-- The emitted checked byte write raises Subscript outside bounds. -/
theorem evaluate_checkedByteUpdate_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (found : state.refs.lookup pointer = some (.byteArray bytes))
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
        (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number byte.toNat :: .number index :: .refPtr flag pointer :: env) state =
        (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (bytes.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, found, invalid]

/-- The checked byte write's emitted body simulates the flat primitive at
every index and preserves the state relation. -/
theorem checkedByteUpdate_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (states : StateRel source target) (found : source.refs[pointer]? = some (.w8array bytes)) :
    let flat := FlatSem.applyResult source (.src .aw8update)
      [.loc flag pointer, .litv (.intLit index), .litv (.word8 byte)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
        (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number byte.toNat :: .number index :: .refPtr flag pointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have targetFound := lookup_byteArray states found
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedByteUpdate_outOfBounds target trace env pointer flag bytes index byte targetFound (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative, body, states,
      EvalResultRel.raise exception]
  · by_cases bound : index.toNat < bytes.length
    · have targetBody := evaluate_checkedByteUpdate_inBounds target trace env pointer flag bytes index byte targetFound negative bound
      have notBound : ¬bytes.length ≤ index.toNat := by omega
      have newStores := storeRel_setByteArray source.refs target.refs pointer bytes (bytes.set index.toNat byte) states.2.2.2.1 found
      have newStates : StateRel { source with refs := source.refs.set pointer (.w8array (bytes.set index.toNat byte)) }
          { target with refs := target.refs.updateEq (pointer, .byteArray (bytes.set index.toNat byte)) } := by
        rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
        exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.updateIndexed, storeLookup, found, negative, notBound, storeAssign, storeValueSameType,
        targetBody, newStates]
      exact .value (.cons (.tuple .nil) .nil)
    · have bad : bytes.length ≤ index.toNat := by omega
      have body := evaluate_checkedByteUpdate_outOfBounds target trace env pointer flag bytes index byte targetFound (Or.inr bad)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative, bad, body, states,
        EvalResultRel.raise exception]

/-- The emitted checked value-array write updates the target for a valid index. -/
theorem evaluate_checkedArrayUpdate_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (items : List ClosSem.Value) (index : Int) (value : ClosSem.Value)
    (found : state.refs.lookup pointer = some (.valueArray items))
    (nonnegative : ¬index < 0) (bound : index.toNat < items.length) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
        (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (value :: .number index :: .refPtr flag pointer :: env) state =
      (.val [ClosSem.unitValue], { state with refs := state.refs.updateEq (pointer, .valueArray (items.set index.toNat value)) }) := by
  have valid : 0 ≤ index ∧ index < (items.length : Int) := by omega
  have notBound : ¬items.length ≤ index.toNat := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, found, valid, nonnegative, notBound]

/-- The emitted checked value-array write raises Subscript outside bounds. -/
theorem evaluate_checkedArrayUpdate_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (items : List ClosSem.Value) (index : Int) (value : ClosSem.Value)
    (found : state.refs.lookup pointer = some (.valueArray items))
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
        (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (value :: .number index :: .refPtr flag pointer :: env) state =
        (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (items.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, found, invalid]

/-- The checked value-array write's emitted body simulates the flat
operation at every index and preserves the state relation. -/
theorem checkedArrayUpdate_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int)
    (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (found : source.refs[pointer]? = some (.varray items))
    (valueRel : ValueRel value targetValue) :
    let flat := FlatSem.applyResult source (.src .aupdate) [.loc flag pointer, .litv (.intLit index), value]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
        (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (targetValue :: .number index :: .refPtr flag pointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  obtain ⟨targetItems, targetFound, related⟩ := lookup_array states found
  have sameLength := related.length_eq
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedArrayUpdate_outOfBounds target trace env pointer flag targetItems index targetValue targetFound (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative, body, states,
      EvalResultRel.raise exception]
  · by_cases bound : index.toNat < items.length
    · have targetBound : index.toNat < targetItems.length := by omega
      have targetBody := evaluate_checkedArrayUpdate_inBounds target trace env pointer flag targetItems index targetValue targetFound negative targetBound
      have notBound : ¬items.length ≤ index.toNat := by omega
      have newRelated := Flapjack.forall₂_set ValueRel _ _ value targetValue index.toNat ⟨valueRel, related⟩
      have newStores := storeRel_setArray source.refs target.refs pointer items _ _ states.2.2.2.1 found newRelated
      have newStates : StateRel { source with refs := source.refs.set pointer (.varray (items.set index.toNat value)) }
          { target with refs := target.refs.updateEq (pointer, .valueArray (targetItems.set index.toNat targetValue)) } := by
        rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
        exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.updateIndexed, storeLookup, found, negative, notBound, storeAssign, storeValueSameType,
        targetBody, newStates]
      exact .value (.cons (.tuple .nil) .nil)
    · have bad : items.length ≤ index.toNat := by omega
      have targetBad : targetItems.length ≤ index.toNat := by omega
      have body := evaluate_checkedArrayUpdate_outOfBounds target trace env pointer flag targetItems index targetValue targetFound (Or.inr targetBad)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.updateIndexed, FlatSem.boundsFailure, storeLookup, found, negative, bad, body, states,
        EvalResultRel.raise exception]


end Flapjack.Compiler.Backend.FlatToClos
