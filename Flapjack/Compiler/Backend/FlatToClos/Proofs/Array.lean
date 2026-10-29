import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

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

/-- Fixed-array allocation preserves the ordering and relation of every
element after evaluating its argument list. -/
theorem evaluate_allocFixed {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : EvalSim env names values source target args.reverse) :
    EvalSim env names values source target [.app trace (.src .aallocFixed) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have index := leastUnusedRef_eq_length next.refs nextTarget.refs states.2.2.2.1
        have updated := stateRel_allocArray next nextTarget sourceArgs.reverse targetArgs.reverse states
          (List.rel_reverse related)
        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
          storeAlloc, ClosSem.doApp, ClosSem.applyMemory, index, updated,
          EvalResultRel.value (.cons (ValueRel.loc true next.refs.length) .nil)]

/-- Repeated related values form related arrays of the same length. -/
theorem replicate_values_related (count : Nat) (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (related : ValueRel value targetValue) :
    List.Forall₂ ValueRel (List.replicate count value) (List.replicate count targetValue) := by
  induction count with
  | zero => exact .nil
  | succ count ih => exact .cons related ih

/-- A nonnegative sized-array allocation installs related repeated values at
the same fresh index. -/
theorem allocArray_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (size : Int) (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue) (nonnegative : ¬size < 0) :
    ∃ targetNext,
      FlatSem.doAppMemory source .aalloc [.litv (.intLit size), value] =
        some (some ({ source with refs := source.refs ++ [.varray (List.replicate size.toNat value)] },
          .val (.loc true source.refs.length))) ∧
      ClosSem.applyMemory .refArray [.number size, targetValue] target =
        some (.refPtr true source.refs.length, targetNext) ∧
      StateRel { source with refs := source.refs ++ [.varray (List.replicate size.toNat value)] } targetNext := by
  have index := leastUnusedRef_eq_length source.refs target.refs states.2.2.2.1
  let targetNext := { target with refs := target.refs.updateEq (source.refs.length, .valueArray (List.replicate size.toNat targetValue)) }
  refine ⟨targetNext, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppMemory, nonnegative, storeAlloc]
  · simp [ClosSem.applyMemory, nonnegative, index, targetNext]
  · exact stateRel_allocArray source target _ _ states (replicate_values_related _ _ _ related)

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
  · have index := leastUnusedRef_eq_length source.refs target.refs states.2.2.2.1
    have updated := stateRel_allocArray source target (List.replicate size.toNat value)
      (List.replicate size.toNat targetValue) states (replicate_values_related _ _ _ related)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      storeAlloc, negative, evaluate_allocArray_body_nonnegative target trace env size targetValue negative,
      index, updated, EvalResultRel.value (.cons (ValueRel.loc true source.refs.length) .nil)]

end Flapjack.Compiler.Backend.FlatToClos
