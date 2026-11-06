import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ConcatByteStub
import Flapjack.Compiler.Backend.Semantics.BvlSem.MemoryChoice

/-! Byte-vector concatenation lowering in BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The generated concatenation body allocates and fills a fresh array.
Untagged pending evaluator and dispatcher correspondence review. -/
theorem evaluate_concatByteBody {C F : Type} (value : Value) (ptrs : List Nat)
    (chunks : List (List (BitVec 8))) (env : List Value) (state : BviSem.BviState C F)
    (decode : BvlSem.valueToList value = some (ptrs.map (Value.refPtr true)))
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (lengthCode : sptLookup sumListLengthLocation state.code = some sumListLengthCode)
    (concatCode : sptLookup concatByteLocation state.code = some concatByteCode) :
    ∃ clock, BviSem.evaluate [.call 0 (some concatByteLocation)
      [.var 0, .op (.intOp (.const 0)) [],
        .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [],
          .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none]
      (value :: env) (BviProps.incClock clock state) =
      (.val [.refPtr true (BvlSem.leastUnusedRef state.refs)],
        { state with refs := state.refs.updateEq (BvlSem.leastUnusedRef state.refs, .byteArray true chunks.flatten) }) := by
  let ptr := BvlSem.leastUnusedRef state.refs
  let zeros : List (BitVec 8) := List.replicate chunks.flatten.length 0
  let allocated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .byteArray true zeros) }
  have ptrDistinct : ptr ∉ ptrs := by
    intro member
    have present : state.refs.lookup ptr ∈ chunks.map (fun bytes => some (.byteArray true bytes)) := by
      rw [← lookups]
      exact List.mem_map.mpr ⟨ptr, member, rfl⟩
    obtain ⟨bytes, _, equal⟩ := List.mem_map.mp present
    have unused : state.refs.lookup ptr = none := by
      simpa [ptr] using BvlSem.leastUnusedRef_unused state.refs
    rw [unused] at equal
    cases equal
  have allocatedLookups : ptrs.map allocated.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
    rw [← lookups]
    apply List.map_congr_left
    intro key member
    have ne : key ≠ ptr := by intro eq; subst key; exact ptrDistinct member
    simp [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne]
  have arrayLookup : allocated.refs.lookup ptr = some (.byteArray true ([] ++ zeros)) := by
    simp [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have arrayCode : sptLookup concatByteLocation allocated.code = some concatByteCode := by simpa [allocated] using concatCode
  obtain ⟨writerClock, writerRun⟩ := evaluate_concatByte_decoded value ptrs chunks [] zeros ptr true allocated
    decode ptrDistinct allocatedLookups arrayLookup (by simp [zeros]) arrayCode
  have writerResult : BviSem.evaluate [concatByteCode.2] [value, .number 0, .refPtr true ptr]
      (BviProps.incClock writerClock allocated) =
      (.val [.refPtr true ptr], { state with refs := state.refs.updateEq (ptr, .byteArray true chunks.flatten) }) := by
    simpa [allocated, updateEq_overwrite] using writerRun
  obtain ⟨lengthClock, lengthRun⟩ := evaluate_sumListLength_call value ptrs chunks env state decode lookups lengthCode
  let extra := writerClock + 1
  let start := BviProps.incClock (extra + lengthClock) state
  let middle := BviProps.incClock extra state
  let allocatedMiddle := BviProps.incClock extra allocated
  have shifted := BviProps.evaluate_inv_clock
    [.call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]
    (value :: env) (BviProps.incClock lengthClock state) state (.val [.number (Int.ofNat chunks.flatten.length)]) extra
    (by simpa using lengthRun) (by simp)
  rw [BviProps.incClock_add] at shifted
  have lengthShifted : BviSem.evaluate [.call 0 (some sumListLengthLocation)
      [.var 0, .op (.intOp (.const 0)) []] none] (value :: env) start =
      (.val [.number (Int.ofNat chunks.flatten.length)], middle) := by simpa [start, middle] using shifted
  let zero : Bvi.Exp := .op (.intOp (.const 0)) []
  let lengthExp : Bvi.Exp := .call 0 (some sumListLengthLocation) [.var 0, zero] none
  let allocate : Bvi.Exp := .op (.memOp (.refByte true)) [zero, lengthExp]
  have zeroStart : BviSem.evaluate [zero] (value :: env) start = (.val [.number 0], start) := by
    apply evaluate_smallConst
    decide
  have varStart : BviSem.evaluate [.var 0] (value :: env) start = (.val [value], start) := by simp [BviSem.evaluate]
  have allocArgs : BviSem.evaluate [zero, lengthExp] (value :: env) start =
      (.val [.number 0, .number (Int.ofNat chunks.flatten.length)], middle) := by
    exact evaluate_pair_threaded _ _ _ _ _ _ _ _ zeroStart lengthShifted
  have allocRun : BviSem.evaluate [allocate] (value :: env) start = (.val [.refPtr true ptr], allocatedMiddle) := by
    dsimp [allocate]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocArgs]
    have nonnegative : ¬ (((chunks.map List.length).sum : Nat) : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ClosSem.intToByte,
      middle, allocatedMiddle, allocated, BviProps.incClock, ptr, zeros, nonnegative]
  have argsRun : BviSem.evaluate [.var 0, zero, allocate] (value :: env) start =
      (.val [value, .number 0, .refPtr true ptr], allocatedMiddle) := by
    have restRun := evaluate_pair_threaded zero allocate (value :: env) start start allocatedMiddle (.number 0) (.refPtr true ptr) zeroStart allocRun
    exact evaluate_cons_threaded _ _ _ _ _ _ _ _ varStart restRun
  refine ⟨extra + lengthClock, ?_⟩
  change BviSem.evaluate [.call 0 (some concatByteLocation) [.var 0, zero, allocate] none] (value :: env) start = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  have code : sptLookup concatByteLocation allocatedMiddle.code = some concatByteCode := by
    simpa [allocatedMiddle, allocated, BviProps.incClock] using concatCode
  have nonzero : allocatedMiddle.clock ≠ 0 := by simp [allocatedMiddle, BviProps.incClock, extra]
  have clocks : BviSem.decClock 1 allocatedMiddle = BviProps.incClock writerClock allocated := by
    simp [allocatedMiddle, BviProps.incClock, BviSem.decClock, extra]
  simp only [BvlSem.findCode, code, concatByteCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  have finalRun := writerResult
  simp [concatByteCode] at finalRun
  simp [clocks, finalRun, ptr]

/-- Related heaps contain the same byte arrays at corresponding pointers. -/
theorem byteArrayLookups_relocate {C F : Type} (ptrs : List Nat) (chunks : List (List (BitVec 8)))
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (lookups : ptrs.map source.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes))) :
    (ptrs.map relocate).map target.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  induction ptrs generalizing chunks with
  | nil => cases chunks <;> simp_all
  | cons ptr ptrs ih =>
    cases chunks with
    | nil => simp at lookups
    | cons bytes chunks =>
      simp only [List.map_cons, List.cons.injEq] at lookups
      simp only [List.map_cons]
      exact congrArg₂ List.cons (stateRel_byteArray relocate source target true bytes ptr related lookups.1)
        (ih chunks lookups.2)

/-- A successful source concatenation identifies the encoded list and its
referenced byte arrays. -/
theorem concatByte_shape {C F : Type} (args : List Value) (source next : BvlSem.State C F)
    (value : Value) (run : BvlSem.applyMemory .concatByteVec args source = some (value, next)) :
    ∃ (input : Value) (ptrs : List Nat) (chunks : List (List (BitVec 8))), args = [input] ∧
      BvlSem.valueToList input = some (ptrs.map (Value.refPtr true)) ∧
      ptrs.map source.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) ∧
      value = .refPtr true (BvlSem.leastUnusedRef source.refs) ∧
      next = { source with refs := source.refs.updateEq (BvlSem.leastUnusedRef source.refs, .byteArray true chunks.flatten) } := by
  cases args with
  | nil => simp [BvlSem.applyMemory] at run
  | cons input rest =>
    cases rest with
    | cons second tail => simp [BvlSem.applyMemory] at run
    | nil =>
      cases decode : BvlSem.valueToList input with
      | none => simp [BvlSem.applyMemory, decode] at run
      | some values =>
        cases chunksRun : BvlSem.byteArrays source.refs values with
        | none => simp [BvlSem.applyMemory, decode, chunksRun] at run
        | some chunks =>
          simp [BvlSem.applyMemory, decode, chunksRun] at run
          obtain ⟨ptrs, valuesEq, lookups⟩ := (BvlSem.byteArrays_eq_some source.refs values chunks).1 chunksRun
          exact ⟨input, ptrs, chunks, rfl, by simpa [valuesEq] using decode, lookups, run.1.symm, run.2.symm⟩

/-- Byte-vector concatenation satisfies pass simulation given operand
simulation. Untagged pending evaluator and dispatcher review. -/
theorem simulation_concatByte {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .concatByteVec) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .concatByteVec) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyMemory .concatByteVec values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨input, ptrs, chunks, argsEq, decode, lookups, resultEq, lastEq⟩ :=
          concatByte_shape values.reverse middle last result application
        subst result
        subst last
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        have valuesEq : values = [input] := by simpa using congrArg List.reverse argsEq
        rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
        have valuesLength := BvlSem.evaluate_length arguments env source middle values argsRun
        have codeLength := compileListSource_length n arguments
        rw [argsCompile] at codeLength
        have codeNonempty : argsCode ≠ [] := by intro eq; simp [eq, valuesEq] at codeLength valuesLength; omega
        have lowered : compileOp (.memOp .concatByteVec) argsCode =
            .let argsCode (.call 0 (some concatByteLocation)
              [.var 0, .op (.intOp (.const 0)) [],
                .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [],
                  .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none) := by
          cases argsCode with
          | nil => exact (codeNonempty rfl).elim
          | cons head tail => rfl
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
            (BvlSem.leastUnusedRef targetNext.refs) (.byteArray true chunks.flatten) relatedNext preserved.1
            (BvlSem.leastUnusedRef_unused middle.refs) (BvlSem.leastUnusedRef_unused targetNext.refs)
        have envChange := adjustMap_eq_of_ok midRelocate extended env middle.refs preserved.2.2 agree
        have targetDecode : BvlSem.valueToList (adjustBv midRelocate input) =
            some ((ptrs.map midRelocate).map (Value.refPtr true)) := by
          simpa [decode, List.map_map, Function.comp_def, adjustBv] using valueToList_adjust midRelocate input
        have targetLookups := byteArrayLookups_relocate ptrs chunks midRelocate middle targetNext relatedNext lookups
        have lengthCode : sptLookup sumListLengthLocation targetNext.code = some sumListLengthCode := relatedNext.2.2.2.2.2.2.2.2.2.2.2.1
        have concatCode : sptLookup concatByteLocation targetNext.code = some concatByteCode := relatedNext.2.2.2.2.2.2.2.2.2.2.2.2.1
        obtain ⟨extra, bodyRun⟩ := evaluate_concatByteBody (adjustBv midRelocate input) (ptrs.map midRelocate) chunks
          (env.map (adjustBv extended)) targetNext targetDecode targetLookups lengthCode concatCode
        have shifted := BviProps.evaluate_inv_clock argsCode (env.map (adjustBv midRelocate))
          (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv midRelocate))) extra
          (by simpa [mapSimulationResult] using targetArgs) (by simp)
        rw [BviProps.incClock_add, envChange] at shifted
        refine ⟨{ targetNext with refs := targetNext.refs.updateEq (BvlSem.leastUnusedRef targetNext.refs, .byteArray true chunks.flatten) },
          extended, extra + clock, ?_, ?_, envEq.trans envChange, ?_⟩
        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, shifted]
          simp only [valuesEq, List.map_cons, List.map_nil, List.cons_append, List.nil_append, mapSimulationResult]
          simpa [adjustBv, keyEq] using bodyRun
        · simpa [adjustRef] using relatedAlloc
        · intro key present
          exact (refsEq key present).trans (agree key (growth key present))

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
