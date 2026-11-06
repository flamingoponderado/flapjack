import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CopyGlobalsStub

/-! Global-array allocation stub in BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The global allocator reads the current size and increments it in the
existing array before deciding whether to grow that array. The continuation
is the allocator's actual conditional. Untagged pending evaluator and
dispatcher correspondence review. -/
theorem evaluate_allocGlobal_prefix {C F : Type} (ptr used count : Nat) (fields : List Value)
    (state final : BviSem.BviState C F) (result : Value)
    (global : state.global = some ptr)
    (lookup : state.refs.lookup ptr = some (.valueArray (.number (Int.ofNat used) :: fields)))
    (continuation : BviSem.evaluate
      [.ifThenElse (.op (.intOp .less) [.var 1, .var 2]) (.var 0)
        (.let [.op (.memOp .refArray) [.op (.intOp (.const 0)) [],
          .op (.intOp .add) [.var 2, .var 2]]]
          (.let [.op (.globOp .setGlobalsPtr) [.var 0]]
            (.call 0 (some copyGlobalsLocation) [.var 1, .var 6,
              .op (.intOp .sub) [.op (.intOp (.const 1)) [], .var 3]] none)))]
      [BvlSem.unitValue, .number (fields.length + 1), .number (Int.ofNat (used + count)),
        .number used, .refPtr true ptr, .number count]
      { state with refs := state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (used + count)) :: fields)) } =
      (.val [result], final)) :
    BviSem.evaluate [allocGlobalCode.2] [.number count] state = (.val [result], final) := by
  let env : List Value := [.number count]
  let getGlobal : Bvi.Exp := .op (.globOp .globalsPtr) []
  let readSize : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 0)) [], .var 0]
  let add : Bvi.Exp := .op (.intOp .add) [.var 0, .var 2]
  let arrayLength : Bvi.Exp := .op (.memOp .length) [.var 2]
  let write : Bvi.Exp := .op (.memOp .update) [.var 1, .op (.intOp (.const 0)) [], .var 3]
  let env2 := .refPtr true ptr :: env
  let env3 := .number (Int.ofNat used) :: env2
  let env4 := .number (Int.ofNat (used + count)) :: env3
  let env5 := .number (Int.ofNat (fields.length + 1)) :: env4
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (used + count)) :: fields)) }
  have globalRun : BviSem.evaluate [getGlobal] env state = (.val [.refPtr true ptr], state) := by
    simp [getGlobal, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, global]
    cases state
    simp_all
  have readArgs : BviSem.evaluate [.op (.intOp (.const 0)) [], .var 0] env2 state =
      (.val [.number 0, .refPtr true ptr], state) := by
    apply evaluate_readOnly
    simp [env2, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have readRun : BviSem.evaluate [readSize] env2 state = (.val [.number used], state) := by
    dsimp [readSize]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, readArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, lookup]
  have addArgs : BviSem.evaluate [.var 0, .var 2] env3 state = (.val [.number used, .number count], state) := by
    apply evaluate_readOnly
    simp [env3, env2, env, BviSem.evaluate]
  have addRun : BviSem.evaluate [add] env3 state = (.val [.number (Int.ofNat (used + count))], state) := by
    dsimp [add]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, addArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl, Int.add_comm]
  have lengthRun : BviSem.evaluate [arrayLength] env4 state = (.val [.number (fields.length + 1)], state) := by
    simp [arrayLength, env4, env3, env2, env, BviSem.evaluate, BviSem.fixClock, BviSem.doApp,
      BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, lookup]
  have writeArgs : BviSem.evaluate [.var 1, .op (.intOp (.const 0)) [], .var 3] env5 state =
      (.val [.number (Int.ofNat (used + count)), .number 0, .refPtr true ptr], state) := by
    apply evaluate_readOnly
    simp [env5, env4, env3, env2, env, BviSem.evaluate, BviSem.fixClock, BviSem.doApp,
      BviSem.doAppFallback, BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have writeRun : BviSem.evaluate [write] env5 state = (.val [BvlSem.unitValue], updated) := by
    dsimp [write]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, lookup, updated]
  change BviSem.evaluate [.let [getGlobal] (.let [readSize] (.let [add] (.let [arrayLength] (.let [write] _))))] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, globalRun]
  change BviSem.evaluate [.let [readSize] (.let [add] (.let [arrayLength] (.let [write] _)))] env2 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, readRun]
  change BviSem.evaluate [.let [add] (.let [arrayLength] (.let [write] _))] env3 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, addRun]
  change BviSem.evaluate [.let [arrayLength] (.let [write] _)] env4 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, lengthRun]
  change BviSem.evaluate [.let [write] _] env5 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeRun]
  exact continuation

/-- If the existing global array has enough space, allocation changes only
its size header. Untagged pending evaluator and dispatcher review. -/
theorem evaluate_allocGlobal_noGrow {C F : Type} (ptr used count : Nat) (fields : List Value)
    (state : BviSem.BviState C F) (global : state.global = some ptr)
    (lookup : state.refs.lookup ptr = some (.valueArray (.number (Int.ofNat used) :: fields)))
    (fits : used + count < fields.length + 1) :
    BviSem.evaluate [allocGlobalCode.2] [.number count] state =
      (.val [BvlSem.unitValue],
        { state with refs := state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (used + count)) :: fields)) }) := by
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (used + count)) :: fields)) }
  let env : List Value := [BvlSem.unitValue, .number (fields.length + 1), .number (Int.ofNat (used + count)),
    .number used, .refPtr true ptr, .number count]
  apply evaluate_allocGlobal_prefix ptr used count fields state updated BvlSem.unitValue global lookup
  have args : BviSem.evaluate [.var 1, .var 2] env updated =
      (.val [.number (fields.length + 1), .number (Int.ofNat (used + count))], updated) := by
    apply evaluate_readOnly
    simp [env, BviSem.evaluate]
  have test : BviSem.evaluate [.op (.intOp .less) [.var 1, .var 2]] env updated =
      (.val [BvlSem.boolValue true], updated) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    have fitsInt : (used : Int) + (count : Int) < (fields.length : Int) + 1 := by omega
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl, fitsInt]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, test]
  change BviSem.evaluate [.var 0] env updated = _
  simp [env, BviSem.evaluate]

/-- If the old array is full, the allocator creates a larger array and copies
the old global cells into it. Untagged pending evaluator and dispatcher
review. -/
theorem evaluate_allocGlobal_grow {C F : Type} (ptr used count : Nat) (fields : List Value)
    (state : BviSem.BviState C F) (global : state.global = some ptr)
    (lookup : state.refs.lookup ptr = some (.valueArray (.number (Int.ofNat used) :: fields)))
    (grow : fields.length + 1 ≤ used + count)
    (code : sptLookup copyGlobalsLocation state.code = some copyGlobalsCode) :
    ∃ newPtr clock, newPtr ≠ ptr ∧ state.refs.lookup newPtr = none ∧
      BviSem.evaluate [allocGlobalCode.2] [.number count] (BviProps.incClock clock state) =
      (.val [BvlSem.unitValue],
        { state with
          global := some newPtr
          refs := (state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (used + count)) :: fields))).updateEq
            (newPtr, .valueArray (.number (Int.ofNat (used + count)) :: fields ++
              List.replicate (2 * (used + count) - (fields.length + 1)) (.number 0))) }) := by
  let size := used + count
  let oldFields : List Value := .number (Int.ofNat size) :: fields
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .valueArray oldFields) }
  let newPtr := BvlSem.leastUnusedRef updated.refs
  let zeros : List Value := List.replicate (2 * size) (.number 0)
  let allocated : BviSem.BviState C F := { updated with refs := updated.refs.updateEq (newPtr, .valueArray zeros) }
  let moved : BviSem.BviState C F := { allocated with global := some newPtr }
  have oldLookup : updated.refs.lookup ptr = some (.valueArray oldFields) := by
    simp [updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have unused : updated.refs.lookup newPtr = none := BvlSem.leastUnusedRef_unused updated.refs
  have different : ptr ≠ newPtr := by
    intro eq
    rw [eq, unused] at oldLookup
    contradiction
  have originalUnused : state.refs.lookup newPtr = none := by
    simpa [updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different.symm] using unused
  have movedSrc : moved.refs.lookup ptr = some (.valueArray oldFields) := by
    simpa [moved, allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using oldLookup
  have movedDst : moved.refs.lookup newPtr = some (.valueArray zeros) := by
    simp [moved, allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have movedCode : sptLookup copyGlobalsLocation moved.code = some copyGlobalsCode := by
    simpa [moved, allocated, updated] using code
  have dstBound : fields.length < zeros.length := by simp [zeros, size]; omega
  obtain ⟨copyClock, copyRun⟩ := evaluate_copyGlobals fields.length ptr newPtr true true oldFields zeros moved
    different movedSrc movedDst (by simp [oldFields]) dstBound movedCode
  have finalCopy : BviSem.evaluate [copyGlobalsCode.2] [.refPtr true newPtr, .refPtr true ptr, .number fields.length]
      (BviProps.incClock copyClock moved) =
      (.val [BvlSem.unitValue],
        { state with
          global := some newPtr
          refs := (state.refs.updateEq (ptr, .valueArray oldFields)).updateEq
            (newPtr, .valueArray (oldFields ++ List.replicate (2 * size - (fields.length + 1)) (.number 0))) }) := by
    simpa [moved, allocated, updated, oldFields, zeros, updateEq_overwrite] using copyRun
  refine ⟨newPtr, copyClock + 1, different.symm, originalUnused, ?_⟩
  let start := BviProps.incClock (copyClock + 1) state
  let changed := BviProps.incClock (copyClock + 1) updated
  let allocatedStart := BviProps.incClock (copyClock + 1) allocated
  let movedStart := BviProps.incClock (copyClock + 1) moved
  let env : List Value := [BvlSem.unitValue, .number (fields.length + 1), .number (Int.ofNat size),
    .number used, .refPtr true ptr, .number count]
  have startGlobal : start.global = some ptr := by simpa [start, BviProps.incClock] using global
  have startLookup : start.refs.lookup ptr = some (.valueArray (.number (Int.ofNat used) :: fields)) := by
    simpa [start, BviProps.incClock] using lookup
  apply evaluate_allocGlobal_prefix ptr used count fields start _ BvlSem.unitValue startGlobal startLookup
  change BviSem.evaluate [.ifThenElse (.op (.intOp .less) [.var 1, .var 2]) (.var 0) _] env changed = _
  have testArgs : BviSem.evaluate [.var 1, .var 2] env changed =
      (.val [.number (fields.length + 1), .number (Int.ofNat size)], changed) := by
    apply evaluate_readOnly
    simp [env, BviSem.evaluate]
  have test : BviSem.evaluate [.op (.intOp .less) [.var 1, .var 2]] env changed =
      (.val [BvlSem.boolValue false], changed) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, testArgs]
    have notFits : ¬ (used : Int) + (count : Int) < (fields.length : Int) + 1 := by omega
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl, size, notFits]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, test]
  let zero : Bvi.Exp := .op (.intOp (.const 0)) []
  let double : Bvi.Exp := .op (.intOp .add) [.var 2, .var 2]
  let allocate : Bvi.Exp := .op (.memOp .refArray) [zero, double]
  let env2 : List Value := .refPtr true newPtr :: env
  let setGlobal : Bvi.Exp := .op (.globOp .setGlobalsPtr) [.var 0]
  let env3 := BvlSem.unitValue :: env2
  let dec : Bvi.Exp := .op (.intOp .sub) [.op (.intOp (.const 1)) [], .var 3]
  have zeroRun : BviSem.evaluate [zero] env changed = (.val [.number 0], changed) := by
    apply evaluate_smallConst
    decide
  have doubleArgs : BviSem.evaluate [.var 2, .var 2] env changed =
      (.val [.number (Int.ofNat size), .number (Int.ofNat size)], changed) := by
    apply evaluate_readOnly
    simp [env, BviSem.evaluate]
  have doubleRun : BviSem.evaluate [double] env changed = (.val [.number (Int.ofNat (2 * size))], changed) := by
    dsimp [double]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, doubleArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl]
    omega
  have allocArgs := evaluate_pair zero double env changed (.number 0) (.number (Int.ofNat (2 * size))) zeroRun doubleRun
  have allocRun : BviSem.evaluate [allocate] env changed = (.val [.refPtr true newPtr], allocatedStart) := by
    dsimp [allocate]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocArgs]
    have nonnegative : ¬ (2 : Int) * (size : Int) < 0 := by omega
    have naturalSize : ((2 : Int) * (size : Int)).toNat = 2 * size := by omega
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, changed, allocatedStart, allocated, updated,
      BviProps.incClock, zeros, newPtr, nonnegative, naturalSize]
  have setRun : BviSem.evaluate [setGlobal] env2 allocatedStart = (.val [BvlSem.unitValue], movedStart) := by
    simp [setGlobal, env2, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, movedStart, allocatedStart, moved, BviProps.incClock]
  have decRun : BviSem.evaluate [dec] env3 movedStart = (.val [.number fields.length], movedStart) := by
    have one : BviSem.evaluate [.op (.intOp (.const 1)) []] env3 movedStart = (.val [.number 1], movedStart) := by
      apply evaluate_smallConst
      decide
    have var : BviSem.evaluate [.var 3] env3 movedStart = (.val [.number (fields.length + 1)], movedStart) := by
      simp [env3, env2, env, BviSem.evaluate]
    have args := evaluate_pair _ _ env3 movedStart (.number 1) (.number (fields.length + 1)) one var
    dsimp [dec]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  have callArgs : BviSem.evaluate [.var 1, .var 6, dec] env3 movedStart =
      (.val [.refPtr true newPtr, .refPtr true ptr, .number fields.length], movedStart) := by
    apply evaluate_readOnly
    constructor
    · simp [env3, env2, BviSem.evaluate]
    constructor
    · simp [env3, env2, env, BviSem.evaluate]
    constructor
    · exact decRun
    constructor
  change BviSem.evaluate [.let [allocate] (.let [setGlobal] (.call 0 (some copyGlobalsLocation) [.var 1, .var 6, dec] none))] env changed = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocRun]
  change BviSem.evaluate [.let [setGlobal] (.call 0 (some copyGlobalsLocation) [.var 1, .var 6, dec] none)] env2 allocatedStart = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, setRun]
  change BviSem.evaluate [.call 0 (some copyGlobalsLocation) [.var 1, .var 6, dec] none] env3 movedStart = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, callArgs]
  have startCode : sptLookup copyGlobalsLocation movedStart.code = some copyGlobalsCode := by
    simpa [movedStart, moved, allocated, updated, BviProps.incClock] using code
  have nonzero : movedStart.clock ≠ 0 := by simp [movedStart, BviProps.incClock]
  have clocks : BviSem.decClock 1 movedStart = BviProps.incClock copyClock moved := by
    simp [movedStart, BviProps.incClock, BviSem.decClock]
  simp only [BvlSem.findCode, startCode, copyGlobalsCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  simp [copyGlobalsCode] at finalCopy
  simp [clocks, finalCopy, oldFields, size]

/-- The allocating-globals stub either reuses the existing array or replaces
it with a fresh larger one, preserving all old entries. Untagged pending BVI
evaluator and dispatcher correspondence review. -/
theorem evaluate_allocGlobal {C F : Type} (ptr n count : Nat) (fields : List Value)
    (state : BviSem.BviState C F) (global : state.global = some ptr)
    (lookup : state.refs.lookup ptr = some (.valueArray (.number (Int.ofNat (n + 1)) :: fields)))
    (_bound : n ≤ fields.length)
    (code : sptLookup copyGlobalsLocation state.code = some copyGlobalsCode) :
    ∃ newPtr clock extra, (newPtr ≠ ptr → state.refs.lookup newPtr = none) ∧
      n + count + 1 ≤ fields.length + extra ∧
      BviSem.evaluate [allocGlobalCode.2] [.number count] (BviProps.incClock clock state) =
      (.val [BvlSem.unitValue],
        { state with
          global := some newPtr
          refs := (state.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (n + count + 1)) :: fields))).updateEq
            (newPtr, .valueArray (.number (Int.ofNat (n + count + 1)) :: fields ++
              List.replicate extra (.number 0))) }) := by
  by_cases fits : (n + 1) + count < fields.length + 1
  · refine ⟨ptr, 0, 0, ?_, ?_, ?_⟩
    · simp
    · omega
    have run := evaluate_allocGlobal_noGrow ptr (n + 1) count fields state global lookup fits
    cases state
    simp_all [BviProps.incClock, updateEq_overwrite, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have grow : fields.length + 1 ≤ (n + 1) + count := by omega
    obtain ⟨newPtr, clock, different, unused, run⟩ :=
      evaluate_allocGlobal_grow ptr (n + 1) count fields state global lookup grow code
    refine ⟨newPtr, clock, 2 * ((n + 1) + count) - (fields.length + 1), ?_, ?_, ?_⟩
    · intro _
      exact unused
    · omega
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
