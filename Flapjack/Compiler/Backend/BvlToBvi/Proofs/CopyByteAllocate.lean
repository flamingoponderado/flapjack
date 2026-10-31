import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileUnsupported

/-! Allocating byte-copy lowering in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.SemanticPrimitivesHOL (copyArray)

/-- Copying a valid slice into a fresh array of exactly the slice length gives
the same bytes as the source allocating-copy operation. -/
theorem copyArray_freshDestination {α : Type} (source : List α) (offset length : Int)
    (fill : α) (copied : List α) (run : copyArray (source, offset) length none = some copied) :
    0 ≤ length ∧
      copyArray (source, offset) length (some (List.replicate length.toNat fill, 0)) = some copied := by
  simp only [copyArray] at run ⊢
  split at run
  · contradiction
  · rename_i valid
    simp only [Option.some.injEq] at run
    subst copied
    have nonnegative : 0 ≤ length := by omega
    refine ⟨nonnegative, ?_⟩
    have absEq : length.natAbs = length.toNat := by
      have h1 := Int.natAbs_of_nonneg nonnegative
      have h2 := Int.toNat_of_nonneg nonnegative
      omega
    simp [valid, absEq]

/-- Evaluating a list of individually state-preserving expressions collects
all values without changing state. -/
theorem evaluate_readOnly {C F : Type} (expressions : List Bvi.Exp) (values : List BvlSem.Value)
    (env : List BvlSem.Value) (state : BviSem.BviState C F)
    (runs : List.Forall₂ (fun expression value => BviSem.evaluate [expression] env state = (.val [value], state))
      expressions values) : BviSem.evaluate expressions env state = (.val values, state) := by
  induction runs with
  | nil => simp [BviSem.evaluate]
  | cons head tail ih =>
    change BviSem.evaluateTuple (_ :: _, env, state) = _
    rw [BviSem.evaluateCons]
    simp [BviSem.evaluateTuple, head, ih, Flapjack.holHd]

/-- Replacing the same finite-map entry twice keeps only the last value. -/
theorem updateEq_overwrite {α β : Type} [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (first second : β) :
    (map.updateEq (key, first)).updateEq (key, second) = map.updateEq (key, second) := by
  cases map
  simp only [HolFiniteMapExact.updateEq]
  congr 1
  funext index
  simp [FUPDATE_HOL]
  split <;> simp_all

/-- Allocating a fresh byte array and copying into it implements a successful
source allocating copy. This is the generated body after operand evaluation;
it remains untagged pending BVI dispatcher and evaluator review. -/
theorem evaluate_copyByteAllocate_body {C F : Type}
    (state : BviSem.BviState C F) (src : Nat) (srcFlag sourceFlag : Bool)
    (sourceBytes copied : List (BitVec 8)) (offset length : Int) (env : List BvlSem.Value)
    (srcLookup : state.refs.lookup src = some (.byteArray sourceFlag sourceBytes))
    (copy : copyArray (sourceBytes, offset) length none = some copied) :
    BviSem.evaluate
      [.let [.op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .var 0]]
        (.let [.op (.memOp (.copyByte false)) [.op (.intOp (.const 0)) [], .var 0, .var 1, .var 2, .var 3]] (.var 1))]
      (.number length :: .number offset :: .refPtr srcFlag src :: env) state =
      (.val [.refPtr true (BvlSem.leastUnusedRef state.refs)],
        { state with refs := state.refs.updateEq (BvlSem.leastUnusedRef state.refs, .byteArray true copied) }) := by
  obtain ⟨nonnegative, copyFresh⟩ := copyArray_freshDestination sourceBytes offset length (0 : BitVec 8) copied copy
  let ptr := BvlSem.leastUnusedRef state.refs
  let initial : List (BitVec 8) := List.replicate length.toNat 0
  let allocated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .byteArray true initial) }
  let input : List BvlSem.Value := .number length :: .number offset :: .refPtr srcFlag src :: env
  let zero : Bvi.Exp := .op (.intOp (.const 0)) []
  have fresh : state.refs.lookup ptr = none := BvlSem.leastUnusedRef_unused state.refs
  have different : src ≠ ptr := by
    intro equal
    rw [equal, fresh] at srcLookup
    contradiction
  have allocArgs : BviSem.evaluate [zero, .var 0] input state = (.val [.number 0, .number length], state) := by
    apply evaluate_pair
    · simp [zero, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
        BviSem.doAppAux, BackendCommon.smallEnoughInt]
    · simp [input, BviSem.evaluate]
  have notNegative : ¬ length < 0 := by omega
  have allocRun : BviSem.evaluate [.op (.memOp (.refByte true)) [zero, .var 0]] input state =
      (.val [.refPtr true ptr], allocated) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ClosSem.intToByte,
      ptr, initial, allocated, notNegative]
  let input2 := .refPtr true ptr :: input
  have copyArgs : BviSem.evaluate [zero, .var 0, .var 1, .var 2, .var 3] input2 allocated =
      (.val [.number 0, .refPtr true ptr, .number length, .number offset, .refPtr srcFlag src], allocated) := by
    apply evaluate_readOnly
    constructor
    · simp [zero, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
        BviSem.doAppAux, BackendCommon.smallEnoughInt]
    simp [input2, input, BviSem.evaluate]
  have allocatedSrc : allocated.refs.lookup src = some (.byteArray sourceFlag sourceBytes) := by
    simpa [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using srcLookup
  have allocatedDst : allocated.refs.lookup ptr = some (.byteArray true initial) := by
    simp [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have copyRun : BviSem.evaluate [.op (.memOp (.copyByte false)) [zero, .var 0, .var 1, .var 2, .var 3]] input2 allocated =
      (.val [BvlSem.unitValue], { state with refs := state.refs.updateEq (ptr, .byteArray true copied) }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, copyArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, allocated, FUPDATE_HOL, different, srcLookup, initial, updateEq_overwrite]
    have freshCopy : copyArray (sourceBytes, offset) length
        (some (List.replicate length.toNat (0#8), 0)) = some copied := by
      simpa using copyFresh
    rw [freshCopy]
    rfl
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocRun]
  change BviSem.evaluate [.let [.op (.memOp (.copyByte false)) [zero, .var 0, .var 1, .var 2, .var 3]] (.var 1)] input2 allocated = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, copyRun]
  simp [BviSem.evaluate, input2, input, ptr]

/-- A successful allocating byte copy has the original three-operand shape. -/
theorem copyByteAllocate_shape {C F : Type} (args : List BvlSem.Value) (source next : BvlSem.State C F)
    (value : BvlSem.Value) (run : BvlSem.applyMemory (.copyByte true) args source = some (value, next)) :
    ∃ flag src offset length sourceFlag sourceBytes copied,
      args = [.refPtr flag src, .number offset, .number length] ∧
      source.refs.lookup src = some (.byteArray sourceFlag sourceBytes) ∧
      copyArray (sourceBytes, offset) length none = some copied ∧
      value = .refPtr true (BvlSem.leastUnusedRef source.refs) ∧
      next = { source with refs := source.refs.updateEq (BvlSem.leastUnusedRef source.refs, .byteArray true copied) } := by
  unfold BvlSem.applyMemory at run
  repeat' first | split at run | contradiction
  all_goals simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨srcCell, srcLookup, remainder⟩ := run
  all_goals cases srcCell <;> simp_all [Option.bind_eq_some_iff]
  all_goals aesop (add safe cases Bool)

/-- Allocating byte copies satisfy pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_copyByteAllocate {C F : Type} (arguments : List Bvl.Exp)
    (env : List BvlSem.Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp (.copyByte true)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp (.copyByte true)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyMemory (.copyByte true) values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨flag, src, offset, length, sourceFlag, sourceBytes, copied,
          argsEq, srcLookup, copy, resultEq, lastEq⟩ := copyByteAllocate_shape values.reverse middle last result application
        subst result
        subst last
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        have valuesEq : values = [.number length, .number offset, .refPtr flag src] := by
          simpa using congrArg List.reverse argsEq
        rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
        have valuesLength := BvlSem.evaluate_length arguments env source middle values argsRun
        have codeLength := compileListSource_length n arguments
        rw [argsCompile] at codeLength
        have codeArity : argsCode.length = 3 := by simp [valuesEq] at valuesLength; simpa [valuesLength] using codeLength
        have lowered : compileOp (.memOp (.copyByte true)) argsCode =
            .let argsCode (.let [.op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .var 0]]
              (.let [.op (.memOp (.copyByte false)) [.op (.intOp (.const 0)) [], .var 0, .var 1, .var 2, .var 3]] (.var 1))) := by
          simp [compileOp, codeArity]
          rfl
        have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
        simp [compileListSource, compileSingSource, argsCompile, nilRight, lowered] at compiled
        rcases compiled with ⟨rfl, rfl, rfl⟩
        have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
        obtain ⟨targetNext, midRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
        have growth := BvlProps.evaluateRefsSubset arguments env source middle (.val values) argsRun
        obtain ⟨extended, keyEq, agree, relatedAlloc⟩ :=
          stateRel_allocateFresh midRelocate middle targetNext (BvlSem.leastUnusedRef middle.refs)
            (BvlSem.leastUnusedRef targetNext.refs) (.byteArray true copied) relatedNext preserved.1
            (BvlSem.leastUnusedRef_unused middle.refs) (BvlSem.leastUnusedRef_unused targetNext.refs)
        have envChange := adjustMap_eq_of_ok midRelocate extended env middle.refs preserved.2.2 agree
        have srcPresent : middle.refs.lookup src ≠ none := by rw [srcLookup]; simp
        have ptrEq := agree src srcPresent
        have targetLookup := stateRel_byteArray midRelocate middle targetNext sourceFlag sourceBytes src relatedNext srcLookup
        rw [ptrEq] at targetLookup
        have sourceAgree : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
          intro key present
          exact (refsEq key present).trans (agree key (growth key present))
        refine ⟨{ targetNext with refs := targetNext.refs.updateEq (BvlSem.leastUnusedRef targetNext.refs, .byteArray true copied) },
          extended, clock, ?_, ?_, envEq.trans envChange, sourceAgree⟩
        · rw [envChange] at targetArgs
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
          simp only [mapSimulationResult, valuesEq, List.map_cons, List.map_nil, adjustBv,
            List.cons_append, List.nil_append]
          rw [ptrEq]
          simpa [adjustBv, keyEq] using evaluate_copyByteAllocate_body targetNext (extended src) flag sourceFlag
            sourceBytes copied offset length (env.map (adjustBv extended)) targetLookup copy
        · simpa [adjustRef] using relatedAlloc

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
