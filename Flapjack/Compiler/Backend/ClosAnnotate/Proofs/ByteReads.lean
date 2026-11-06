import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MemoryReads

/-! Byte-array and byte-vector observations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Extract bytes from an optional byte-array reference. -/
def refByteArray : Option (Ref Value) → Option (List (BitVec 8))
  | some (.byteArray bytes) => some bytes
  | _ => none

/-- Related references expose exactly the same optional byte contents. -/
theorem refByteArray_related (left right : Option (Ref Value)) (related : optionRel RefRel left right) :
    refByteArray left = refByteArray right := by
  cases left with
  | none => cases right <;> simp_all [optionRel, refByteArray]
  | some leftRef =>
    cases right with
    | none => simp [optionRel] at related
    | some rightRef => cases leftRef <;> cases rightRef <;> simp_all [optionRel, RefRel, refByteArray]

/-- Obtain bytes either from a reference or from a byte vector. -/
def observedBytes (reference : Bool) (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (List (BitVec 8)) :=
  match reference, value with
  | true, .refPtr _ ptr => refByteArray (refs.lookup ptr)
  | false, .byteVector bytes => some bytes
  | _, _ => none

/-- Byte observations agree for related values and stores. -/
theorem observedBytes_related {C F : Type} (reference : Bool) (value nextValue : Value)
    (related : ValueRel value nextValue) (source target : State C F) (states : StateRel source target) :
    observedBytes reference value source.refs = observedBytes reference nextValue target.refs := by
  cases related with
  | refPtr flag ptr =>
    cases reference with
    | false => rfl
    | true => exact refByteArray_related _ _ (states.2.2.2.2.2.2.1 ptr)
  | _ => cases reference <;> rfl

/-- Read one byte as an integer, rejecting negative and out-of-range indices. -/
def byteAt (reference : Bool) (value : Value) (index : Int)
    (refs : HolFiniteMapExact Nat (Ref Value)) : Option Value :=
  if index < 0 then none else do
    let bytes ← observedBytes reference value refs
    let byte ← bytes[index.toNat]?
    some (.number byte.toNat)

/-- Related byte observations give the same indexed result. -/
theorem byteAt_related {C F : Type} (reference : Bool) (value nextValue : Value)
    (related : ValueRel value nextValue) (index : Int) (source target : State C F) (states : StateRel source target) :
    byteAt reference value index source.refs = byteAt reference nextValue index target.refs := by
  simp only [byteAt, observedBytes_related reference value nextValue related source target states]

/-- The two byte-read dispatcher cases expose the corresponding observation. -/
theorem applyMemory_byteAt {C F : Type} (reference : Bool) (value : Value) (index : Int) (state : State C F) :
    applyMemory (if reference then .derefByte else .derefByteVec) [value, .number index] state =
      (byteAt reference value index state.refs).map (fun result => (result, state)) := by
  cases reference with
  | false =>
    cases value <;> simp [applyMemory, byteAt, observedBytes]
    all_goals split <;> simp_all [Option.map_eq_bind, Function.comp_def, Option.bind_assoc]
  | true =>
    cases value with
    | refPtr flag ptr =>
      cases h : state.refs.lookup ptr with
      | none => simp [applyMemory, byteAt, observedBytes, refByteArray, h]
      | some ref =>
        cases ref <;> simp [applyMemory, byteAt, observedBytes, refByteArray, h]
        all_goals split <;> simp_all [Option.map_eq_bind, Function.comp_def, Option.bind_assoc]
    | _ => simp [applyMemory, byteAt, observedBytes]

/-- Reading byte arrays or byte vectors preserves the primitive simulation. -/
theorem primitiveSimulation_byteAt {C F : Type} (reference : Bool) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (if reference then .derefByte else .derefByteVec)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => cases reference <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => cases reference <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases second with
        | number index =>
          rename_i value nextValue
          have same := byteAt_related reference value nextValue first index source target states
          cases result : byteAt reference value index source.refs with
          | none =>
            have nextResult : byteAt reference nextValue index target.refs = none := by rw [← same, result]
            refine ⟨.err (.abort .typeError), ?_, ?_⟩
            · simp [doApp, applyMemory_byteAt, nextResult]
            · simp [doApp, applyMemory_byteAt, result, AppResultRel, ResultRel]
          | some read =>
            have nextResult : byteAt reference nextValue index target.refs = some read := by rw [← same, result]
            have valueRel : ValueRel read read := by
              unfold byteAt at result
              split at result <;> simp_all [Option.bind_eq_some_iff]
              obtain ⟨bytes, _, b, _, rfl⟩ := result
              exact .number _
            refine ⟨.val (read, target), ?_, ?_⟩
            · simp [doApp, applyMemory_byteAt, nextResult]
            · simp only [doApp, applyMemory_byteAt, result, AppResultRel]
              exact ⟨valueRel, states⟩
        | _ => cases first <;> cases reference <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest => cases reference <;>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- Bounds checks accept both byte vectors and byte-array references. -/
def byteBounds (loose : Bool) (value : Value) (index : Int)
    (refs : HolFiniteMapExact Nat (Ref Value)) : Option Value := do
  let bytes ← (observedBytes false value refs).orElse (fun _ => observedBytes true value refs)
  some (boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)))

/-- Related values and stores give identical byte bounds observations. -/
theorem byteBounds_related {C F : Type} (loose : Bool) (value nextValue : Value)
    (related : ValueRel value nextValue) (index : Int) (source target : State C F) (states : StateRel source target) :
    byteBounds loose value index source.refs = byteBounds loose nextValue index target.refs := by
  simp only [byteBounds, observedBytes_related false value nextValue related source target states,
    observedBytes_related true value nextValue related source target states]

/-- The bounds-check dispatcher exposes the optional Boolean observation. -/
theorem applyMemory_byteBounds {C F : Type} (loose : Bool) (value : Value) (index : Int) (state : State C F) :
    applyMemory (.boundsCheckByte loose) [value, .number index] state =
      (byteBounds loose value index state.refs).map (fun result => (result, state)) := by
  cases value with
  | refPtr flag ptr =>
    cases h : state.refs.lookup ptr with
    | none => simp [applyMemory, byteBounds, observedBytes, refByteArray, h]
    | some ref => cases ref <;> simp [applyMemory, byteBounds, observedBytes, refByteArray, h]
  | _ => simp [applyMemory, byteBounds, observedBytes]

/-- Byte bounds checks preserve the primitive simulation. -/
theorem primitiveSimulation_byteBounds {C F : Type} (loose : Bool) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (.boundsCheckByte loose)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases second with
        | number index =>
          rename_i value nextValue
          have same := byteBounds_related loose value nextValue first index source target states
          cases result : byteBounds loose value index source.refs with
          | none =>
            have nextResult : byteBounds loose nextValue index target.refs = none := by rw [← same, result]
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory_byteBounds, nextResult], by
              simp [doApp, applyMemory_byteBounds, result, AppResultRel, ResultRel]⟩
          | some read =>
            have nextResult : byteBounds loose nextValue index target.refs = some read := by rw [← same, result]
            have valueRel : ValueRel read read := by
              cases bytesRun : (observedBytes false value source.refs).orElse
                  (fun _ => observedBytes true value source.refs) with
              | none =>
                rw [byteBounds, bytesRun] at result
                cases result
              | some bytes =>
                rw [byteBounds, bytesRun] at result
                simp only [bind, Option.bind, Option.some.injEq] at result
                subst read
                exact .block _ [] [] .nil
            refine ⟨.val (read, target), ?_, ?_⟩
            · simp [doApp, applyMemory_byteBounds, nextResult]
            · simp only [doApp, applyMemory_byteBounds, result, AppResultRel]
              exact ⟨valueRel, states⟩
        | _ => cases first <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- Byte-vector lengths agree for related values. -/
theorem primitiveSimulation_lengthByteVec {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .lengthByteVec) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | byteVector bytes =>
        refine ⟨.val (.number bytes.length, target), ?_, ?_⟩
        · simp [doApp, applyMemory]
        · simp only [doApp, applyMemory, AppResultRel]
          exact ⟨.number _, states⟩
      | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- String comparison observes identical byte-vector arguments. -/
theorem primitiveSimulation_stringCmp {C F : Type} (fast : Bool) (op : Opb) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (.stringCmp fast op)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases first with
        | byteVector left =>
          cases second with
          | byteVector right =>
            refine ⟨.val (boolValue (SemanticPrimitivesHOL.strCmp fast op (.implode left) (.implode right)), target), ?_, ?_⟩
            · simp [doApp, applyMemory]
            · simp only [doApp, applyMemory, AppResultRel]
              exact ⟨.block _ [] [] .nil, states⟩
          | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | _ => cases second <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
