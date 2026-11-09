module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ByteUpdate

@[expose] public section

/-! Byte copying under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Obtain byte contents from either a vector or a byte-array reference. -/
def copySourceBytes (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : Option (List (BitVec 8)) :=
  (observedBytes false value refs).orElse (fun _ => observedBytes true value refs)

/-- Related source values and stores expose identical optional byte contents. -/
theorem copySourceBytes_related {C F : Type} (left right : Value) (related : ValueRel left right)
    (source target : State C F) (states : StateRel source target) :
    copySourceBytes left source.refs = copySourceBytes right target.refs := by
  simp only [copySourceBytes, observedBytes_related false left right related source target states,
    observedBytes_related true left right related source target states]

/-- Read a slice into a new byte vector. -/
def copyByteNew (value : Value) (offset length : Int) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (List (BitVec 8)) := do
  let bytes ← copySourceBytes value refs
  SemanticPrimitivesHOL.copyArray (bytes, offset) length none

/-- The copy-to-vector dispatcher exposes the byte-slice computation. -/
theorem applyMemory_copyByteNew {C F : Type} (value : Value) (offset length : Int) (state : State C F) :
    applyMemory (.copyByte true) [value, .number offset, .number length] state =
      (copyByteNew value offset length state.refs).map (fun bytes => (.byteVector bytes, state)) := by
  cases value with
  | byteVector bytes =>
    cases h : SemanticPrimitivesHOL.copyArray (bytes, offset) length none <;>
      simp [applyMemory, copyByteNew, copySourceBytes, observedBytes, h]
  | refPtr flag ptr =>
    cases h : state.refs.lookup ptr with
    | none => simp [applyMemory, copyByteNew, copySourceBytes, observedBytes, refByteArray, h]
    | some ref =>
      cases ref with
      | byteArray bytes =>
        cases copy : SemanticPrimitivesHOL.copyArray (bytes, offset) length none <;>
          simp [applyMemory, copyByteNew, copySourceBytes, observedBytes, refByteArray, h, copy]
      | _ => simp [applyMemory, copyByteNew, copySourceBytes, observedBytes, refByteArray, h]
  | _ => simp [applyMemory, copyByteNew, copySourceBytes, observedBytes]

/-- Copying bytes to a new vector preserves the candidate primitive relation. -/
theorem primitiveSimulation_copyByteNew {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp (.copyByte true)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        cases rest with
        | nil =>
          cases second with
          | number offset =>
            cases third with
            | number length =>
              rename_i value nextValue
              have sameSource := copySourceBytes_related value nextValue first source target states
              have same : copyByteNew value offset length source.refs = copyByteNew nextValue offset length target.refs := by
                simp only [copyByteNew, sameSource]
              cases copy : copyByteNew value offset length source.refs with
              | none =>
                have nextCopy : copyByteNew nextValue offset length target.refs = none := by rw [← same, copy]
                exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory_copyByteNew, nextCopy], by
                  simp [doApp, applyMemory_copyByteNew, copy, AppResultRel, ResultRel]⟩
              | some bytes =>
                have nextCopy : copyByteNew nextValue offset length target.refs = some bytes := by rw [← same, copy]
                refine ⟨.val (.byteVector bytes, target), ?_, ?_⟩
                · simp [doApp, applyMemory_copyByteNew, nextCopy]
                · simp only [doApp, applyMemory_copyByteNew, copy, AppResultRel]
                  exact ⟨.byteVector bytes, states⟩
            | _ => cases first <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
          | _ => cases first <;> cases third <;>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | cons fourth rest =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- Compute the new destination bytes for an in-place copy. -/
def copyByteWrite (value : Value) (offset length : Int) (dst : Nat) (dstOffset : Int)
    (refs : HolFiniteMapExact Nat (Ref Value)) : Option (List (BitVec 8)) := do
  let input ← copySourceBytes value refs
  let bytes ← refByteArray (refs.lookup dst)
  SemanticPrimitivesHOL.copyArray (input, offset) length (some (bytes, dstOffset))

/-- Related source values and stores compute the same destination bytes. -/
theorem copyByteWrite_related {C F : Type} (left right : Value) (related : ValueRel left right)
    (offset length : Int) (dst : Nat) (dstOffset : Int) (source target : State C F) (states : StateRel source target) :
    copyByteWrite left offset length dst dstOffset source.refs =
      copyByteWrite right offset length dst dstOffset target.refs := by
  have sourceEq := copySourceBytes_related left right related source target states
  have destEq := refByteArray_related _ _ (states.2.2.2.2.2.2.1 dst)
  simp only [copyByteWrite, sourceEq, destEq]

/-- In-place copy performs the computed byte-array update. -/
theorem applyMemory_copyByteWrite {C F : Type} (value : Value) (offset length : Int)
    (flag : Bool) (dst : Nat) (dstOffset : Int) (state : State C F) :
    applyMemory (.copyByte false) [value, .number offset, .number length, .refPtr flag dst, .number dstOffset] state =
      (copyByteWrite value offset length dst dstOffset state.refs).map
        (fun bytes => (unitValue, { state with refs := state.refs.updateEq (dst, .byteArray bytes) })) := by
  cases value with
  | byteVector input =>
    cases h : state.refs.lookup dst with
    | none => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h]
    | some ref =>
      cases ref with
      | byteArray bytes =>
        cases copy : SemanticPrimitivesHOL.copyArray (input, offset) length (some (bytes, dstOffset)) <;>
          simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h, copy]
      | _ => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h]
  | refPtr srcFlag src =>
    cases h : state.refs.lookup src with
    | none => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h]
    | some ref =>
      cases ref with
      | byteArray input =>
        cases dstRun : state.refs.lookup dst with
        | none => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h, dstRun]
        | some dstRef =>
          cases dstRef with
          | byteArray bytes =>
            cases copy : SemanticPrimitivesHOL.copyArray (input, offset) length (some (bytes, dstOffset)) <;>
              simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h, dstRun, copy]
          | _ => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h, dstRun]
      | _ => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes, refByteArray, h]
  | _ => simp [applyMemory, copyByteWrite, copySourceBytes, observedBytes]

/-- A byte copy into a shared destination address preserves related stores. -/
theorem copyByteWrite_simulation {C F : Type} (value nextValue : Value) (related : ValueRel value nextValue)
    (offset length : Int) (flag : Bool) (dst : Nat) (dstOffset : Int)
    (source target : State C F) (states : StateRel source target) :
    ∃ outcome,
      doApp (.memOp (.copyByte false))
        [nextValue, .number offset, .number length, .refPtr flag dst, .number dstOffset] target = outcome ∧
      AppResultRel (doApp (.memOp (.copyByte false))
        [value, .number offset, .number length, .refPtr flag dst, .number dstOffset] source) outcome := by
  have same := copyByteWrite_related value nextValue related offset length dst dstOffset source target states
  cases copy : copyByteWrite value offset length dst dstOffset source.refs with
  | none =>
    have nextCopy : copyByteWrite nextValue offset length dst dstOffset target.refs = none := by rw [← same, copy]
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory_copyByteWrite, nextCopy], by
      simp [doApp, applyMemory_copyByteWrite, copy, AppResultRel, ResultRel]⟩
  | some bytes =>
    have nextCopy : copyByteWrite nextValue offset length dst dstOffset target.refs = some bytes := by rw [← same, copy]
    have nextStates := stateRel_updateRefFfi source target states dst (.byteArray bytes) (.byteArray bytes) rfl source.ffi
    refine ⟨.val (unitValue, { target with refs := target.refs.updateEq (dst, .byteArray bytes) }), ?_, ?_⟩
    · simp [doApp, applyMemory_copyByteWrite, nextCopy]
    · simp only [doApp, applyMemory_copyByteWrite, copy, AppResultRel]
      exact ⟨.block _ [] [] .nil, by simpa [states.2.1] using nextStates⟩

/-- In-place byte copies preserve simulation, including aliased references. -/
theorem primitiveSimulation_copyByteWrite {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp (.copyByte false)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        cases rest with
        | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | cons fourth rest =>
          cases rest with
          | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
          | cons fifth rest =>
            cases rest with
            | nil =>
              cases second with
              | number offset =>
                cases third with
                | number length =>
                  cases fourth with
                  | refPtr flag dst =>
                    cases fifth with
                    | number dstOffset => exact copyByteWrite_simulation _ _ first offset length flag dst dstOffset source target states
                    | _ => cases first <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
                  | _ => cases first <;>
                      exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
                | _ => cases first <;>
                    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
              | _ => cases first <;>
                  exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
            | cons sixth rest =>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
