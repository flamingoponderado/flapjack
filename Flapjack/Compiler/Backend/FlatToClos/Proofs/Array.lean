module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
public import Flapjack.Misc.RichList

@[expose] public section

/-! Array-store prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Appending a source value array and installing related closure values
preserves the store relation. -/
theorem storeRel_allocArray (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (values : List FlatSem.Value) (targetValues : List ClosSem.Value)
    (stores : StoreRel refs targetRefs) (related : List.Forall₂ ValueRel values targetValues) :
    StoreRel (refs ++ [.varray values])
      (targetRefs.updateEq (refs.length, .valueArray targetValues)) := by
  intro index
  have original := stores index
  by_cases same : index = refs.length
  · subst index
    simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, related]
  · have different : refs.length ≠ index := Ne.symm same
    by_cases bound : index < refs.length
    · simpa [List.getElem?_append, bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, same, different] using original
    · have past : refs.length + 1 ≤ index := by omega
      have originalNone : refs[index]? = none := List.getElem?_eq_none (by omega)
      have originalFree : targetRefs.lookup index = none := by simpa [originalNone] using original
      simpa [List.getElem?_append, bound, past, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL,
        same, different] using originalFree

/-- Allocate related arrays in related states. -/
theorem stateRel_allocArray {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (values : List FlatSem.Value) (targetValues : List ClosSem.Value)
    (states : StateRel source target) (related : List.Forall₂ ValueRel values targetValues) :
    StateRel { source with refs := source.refs ++ [.varray values] }
      { target with refs := target.refs.updateEq (source.refs.length, .valueArray targetValues) } := by
  rcases states with ⟨maxApp, ffi, clock, stores, globals, globalsRel, install⟩
  exact ⟨maxApp, ffi, clock, storeRel_allocArray source.refs target.refs values targetValues stores related,
    globals, globalsRel, install⟩

/-- Appending a byte array preserves the store relation at every index. -/
theorem storeRel_allocByteArray (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (bytes : List (BitVec 8)) (stores : StoreRel refs targetRefs) :
    StoreRel (refs ++ [.w8array bytes])
      (targetRefs.updateEq (refs.length, .byteArray bytes)) := by
  intro index
  have original := stores index
  by_cases same : index = refs.length
  · subst index
    simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL]
  · have different : refs.length ≠ index := Ne.symm same
    by_cases bound : index < refs.length
    · simpa [List.getElem?_append, bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, same, different] using original
    · have past : refs.length + 1 ≤ index := by omega
      have originalNone : refs[index]? = none := List.getElem?_eq_none (by omega)
      have originalFree : targetRefs.lookup index = none := by simpa [originalNone] using original
      simpa [List.getElem?_append, bound, past, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL,
        same, different] using originalFree

/-- Allocate the same byte array in related states. -/
theorem stateRel_allocByteArray {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (bytes : List (BitVec 8)) (states : StateRel source target) :
    StateRel { source with refs := source.refs ++ [.w8array bytes] }
      { target with refs := target.refs.updateEq (source.refs.length, .byteArray bytes) } := by
  rcases states with ⟨maxApp, ffi, clock, stores, globals, globalsRel, install⟩
  exact ⟨maxApp, ffi, clock, storeRel_allocByteArray source.refs target.refs bytes stores,
    globals, globalsRel, install⟩

/-- The sized-array check raises the source Subscript exception for a
negative size, without changing either store. -/
theorem allocArray_negative {C F : Type} (source : FlatSem.State C F)
    (size : Int) (value : FlatSem.Value) (negative : size < 0) :
    FlatSem.doAppMemory source .aalloc [.litv (.intLit size), value] =
      some (some (source, .err (.raise FlatSem.subscriptExnV))) ∧
    ValueRel FlatSem.subscriptExnV (.block 3 []) := by
  simp [FlatSem.doAppMemory, FlatSem.boundsFailure, negative]
  exact ValueRel.con .nil

/-- Evaluate the body emitted for sized-array allocation after its two
arguments have been bound. -/
theorem evaluate_allocArray_body_negative {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (size : Int) (value : ClosSem.Value)
    (negative : size < 0) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])]
      (value :: .number size :: env) state = (.err (.raise (.block 3 [])), state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
    ClosSem.doIntApp, ClosSem.boolValue, ClosSem.asBool, ClosSem.applyBlock,
    BackendCommon.trueTag, negative]

/-- A nonnegative size reaches the allocation operation in the emitted
closure-language check. -/
theorem evaluate_allocArray_body_nonnegative {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (size : Int) (value : ClosSem.Value)
    (nonnegative : ¬size < 0) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])]
      (value :: .number size :: env) state =
      (.val [.refPtr true (ClosSem.leastUnusedRef state.refs)],
        { state with refs := state.refs.updateEq (ClosSem.leastUnusedRef state.refs, .valueArray (List.replicate size.toNat value)) }) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
    ClosSem.doIntApp, ClosSem.boolValue, ClosSem.asBool, ClosSem.applyMemory,
    BackendCommon.falseTag, nonnegative]

/-- For a related value and integer size, the emitted check and the flat
operation produce related outcomes, including the negative-size exception. -/
theorem allocArray_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (size : Int) (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue) :
    let flat := FlatSem.applyResult source (.src .aalloc) [.litv (.intLit size), value]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])]
      (targetValue :: .number size :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  by_cases negative : size < 0
  · simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.boundsFailure, negative, evaluate_allocArray_body_negative target trace env size targetValue negative,
      states, EvalResultRel.raise (allocArray_negative source size value negative).2]
  · have index := stateRel_least source target states
    have updated := stateRel_allocArray source target (List.replicate size.toNat value)
      (List.replicate size.toNat targetValue) states ((Flapjack.forall₂_replicate_iff ValueRel _ value targetValue).mpr (fun _ => related))
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      storeAlloc, negative, evaluate_allocArray_body_nonnegative target trace env size targetValue negative,
      index, updated, EvalResultRel.value (.cons (ValueRel.loc true source.refs.length) .nil)]

/-- The emitted byte-array bounds check agrees with the flat operation for
integer sizes and byte operands, including negative-size exceptions. -/
theorem allocByteArray_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (size : Int) (byte : BitVec 8) (states : StateRel source target) :
    let flat := FlatSem.applyResult source (.src .aw8alloc) [.litv (.intLit size), .litv (.word8 byte)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.op trace (.memOp (.refByte false)) [.var trace 0, .var trace 1])]
      (.number byte.toNat :: .number size :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  by_cases negative : size < 0
  · have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.boundsFailure, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.boolValue, ClosSem.asBool, ClosSem.applyBlock, BackendCommon.trueTag,
      negative, states, EvalResultRel.raise exception]
  · have index := stateRel_least source target states
    have updated := stateRel_allocByteArray source target (List.replicate size.toNat byte) states
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc,
      ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp,
      ClosSem.boolValue, ClosSem.asBool, ClosSem.applyMemory, ClosSem.intToByte_toNat,
      BackendCommon.falseTag, negative, index, updated,
      EvalResultRel.value (.cons (ValueRel.loc true source.refs.length) .nil)]

end Flapjack.Compiler.Backend.FlatToClos
