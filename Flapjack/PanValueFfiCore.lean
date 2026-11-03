module

public import Flapjack.PanExpressionEvaluator
public import Flapjack.Ffi

@[expose] public section

/-!
# Shared definitions for structured Pancake semantics with stateful FFI

The evaluation context, `SharedMem` load/store, byte-array FFI calls, control
results, handler types and the non-recursive simple-statement helpers used by
both the clocked evaluator (`PanValueFfiClockSemantics`) and the stepped
evaluator (`PanValueFfiSemantics`).

This module contains no recursive statement evaluator, so the clocked semantics
and the compiler can depend on it without depending on the stepped semantics
(issue #1251).

The source memory map remains the ordinary Pancake memory.  Shared memory is
observable only through the FFI state, as in CakeML.  The byte codec is
explicit because the source evaluator is polymorphic in its word type.
-/

namespace Flapjack

structure PanValueFfiContext (α : Type u) where
  sharedDomain : α → Bool
  byteAlign : α → α
  bigEndian : Bool
  wordToBytes : α → Bool → List UInt8
  wordOfBytes : Bool → List UInt8 → α
  wordToByte : α → UInt8
  byteToWord : UInt8 → α
  valueToNat : α → Nat

def panValueFfiWidth : OpSize → Nat
  | .op8 => 1
  | .opW => 0
  | .op32 => 4
  | .op16 => 2

def panValueFfiSharedAddress (context : PanValueFfiContext α)
    (size : OpSize) (address : α) : α :=
  let width := panValueFfiWidth size
  if width = 0 then address else context.byteAlign address

inductive PanValueFfiSharedResult (α : Type u) (σ : Type v) where
  | loaded (ffi : FfiState σ) (value : α)
  | stored (ffi : FfiState σ)
  | final (ffi : FfiState σ) (event : FfiFinalEvent)

def panValueFfiSharedLoad (context : PanValueFfiContext α)
    (ffi : FfiState σ) (size : OpSize) (address : α) :
    Option (PanValueFfiSharedResult α σ) :=
  let width := panValueFfiWidth size
  let alignedAddress := panValueFfiSharedAddress context size address
  if !context.sharedDomain alignedAddress then none
  else
    match callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat width]
        (context.wordToBytes address false) with
    | .returned nextFfi bytes =>
        some (.loaded nextFfi (context.wordOfBytes false bytes))
    | .final event => some (.final ffi event)

def panValueFfiSharedStore (context : PanValueFfiContext α)
    (ffi : FfiState σ) (size : OpSize) (address value : α) :
    Option (PanValueFfiSharedResult α σ) :=
  let width := panValueFfiWidth size
  let alignedAddress := panValueFfiSharedAddress context size address
  if !context.sharedDomain alignedAddress then none
  else
    let payload :=
      if width = 0 then
        context.wordToBytes value false ++ context.wordToBytes address false
      else
        (context.wordToBytes value false).take width ++
          context.wordToBytes address false
    match callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat width] payload with
    | .returned nextFfi _ => some (.stored nextFfi)
    | .final event => some (.final ffi event)

/-- Inversion of a successful mapped read: the address passes the shared-memory
    domain guard and `call_FFI` (Lean `callFfi`) returns bytes whose
    `word_of_bytes` image is the observed value. -/
theorem panValueFfiSharedLoad_loaded_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address : α) (nextFfi : FfiState σ) (value : α)
    (h : panValueFfiSharedLoad context ffi size address = some (.loaded nextFfi value)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    ∃ bytes,
      callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
          (context.wordToBytes address false) = .returned nextFfi bytes ∧
      value = context.wordOfBytes false bytes := by
  simp only [panValueFfiSharedLoad] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hval
        exact ⟨hdom, bytes, by simp only [hffi], hval.symm⟩
    | final event =>
        rw [hcall] at h
        simp at h
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a terminal mapped read. -/
theorem panValueFfiSharedLoad_final_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address : α) (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (h : panValueFfiSharedLoad context ffi size address = some (.final nextFfi event)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    nextFfi = ffi ∧
    callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) = .final event := by
  simp only [panValueFfiSharedLoad] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp at h
    | final event' =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hev
        exact ⟨hdom, hffi.symm, by simp only [hev]⟩
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a successful mapped write: the address passes the domain guard
    and the `SharedMem MappedWrite` send returns normally, updating the ffi. -/
theorem panValueFfiSharedStore_stored_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address value : α) (nextFfi : FfiState σ)
    (h : panValueFfiSharedStore context ffi size address value = some (.stored nextFfi)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    ∃ bytes,
      callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
          (if panValueFfiWidth size = 0 then
              context.wordToBytes value false ++ context.wordToBytes address false
            else
              (context.wordToBytes value false).take (panValueFfiWidth size) ++
                context.wordToBytes address false) = .returned nextFfi bytes := by
  simp only [panValueFfiSharedStore] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi
        exact ⟨hdom, bytes, by simp only [hffi]⟩
    | final event =>
        rw [hcall] at h
        simp at h
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a terminal mapped write. -/
theorem panValueFfiSharedStore_final_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address value : α) (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (h : panValueFfiSharedStore context ffi size address value = some (.final nextFfi event)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    nextFfi = ffi ∧
    callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) = .final event := by
  simp only [panValueFfiSharedStore] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp at h
    | final event' =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hev
        exact ⟨hdom, hffi.symm, by simp only [hev]⟩
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

def panValueFfiReadBytes [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord address : α) :
    Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
      let byte ← access.readByte access.domain memory bytesInWord address
      let rest ← panValueFfiReadBytes access context memory bytesInWord
        (address + 1) length
      pure (context.wordToByte byte :: rest)
termination_by length => length

def panValueFfiWriteBytes [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
  (memory : α → Option (PanValue α)) (bytesInWord address : α) :
    List UInt8 → (α → Option (PanValue α))
  | [] => memory
  | byte :: bytes =>
      let tailMemory := panValueFfiWriteBytes access context memory bytesInWord
        (address + 1) bytes
      match access.storeByte access.domain tailMemory bytesInWord address
          (context.byteToWord byte) with
      | some updatedMemory => updatedMemory
      | none => memory
termination_by bytes => sizeOf bytes

inductive PanValueFfiExtCallResult (α : Type u) (σ : Type v) where
  | returned (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | final (ffi : FfiState σ) (event : FfiFinalEvent)

def panValueFfiExtCall [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α) :
    Option (PanValueFfiExtCallResult α σ) := do
  let configurationBytes ← panValueFfiReadBytes access context memory bytesInWord
    configuration (context.valueToNat configurationLength)
  let arrayBytes ← panValueFfiReadBytes access context memory bytesInWord
    array (context.valueToNat arrayLength)
  match callFfi ffi (.extCall function) configurationBytes arrayBytes with
  | .returned nextFfi bytes =>
      let memory := panValueFfiWriteBytes access context memory bytesInWord array bytes
      pure (.returned memory nextFfi)
  | .final event => pure (.final ffi event)

/-! The successful byte-array ExtCall path preserves the incoming Cake FFI
    trace.  This is the concrete FFI premise used by the evaluator-level
    `evaluate_io_events_mono` bridge below. -/
theorem panValueFfiExtCall_returned_ioEvents_prefix
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength =
      some (.returned nextMemory nextFfi)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  unfold panValueFfiExtCall at hcall
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => simp [hconfiguration] at hcall
  | some configurationBytes =>
      cases harray : panValueFfiReadBytes access context memory bytesInWord
          array (context.valueToNat arrayLength) with
      | none => simp [hconfiguration, harray] at hcall
      | some arrayBytes =>
          cases hffi : callFfi ffi (.extCall function) configurationBytes arrayBytes with
          | final event => simp [hconfiguration, harray, hffi] at hcall
          | returned returnedFfi returnedBytes =>
              simp [hconfiguration, harray, hffi] at hcall
              rcases hcall with ⟨_, rfl⟩
              exact callFfi_return_ioEvents_prefix ffi (.extCall function)
                configurationBytes arrayBytes returnedFfi returnedBytes hffi

/-- Inversion of a successful `panValueFfiExtCall` outcome: the two argument
    reads and the `call_FFI` returned result, with the write-back memory. -/
theorem panValueFfiExtCall_returned_inv
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (h : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength =
      some (.returned nextMemory nextFfi)) :
    ∃ configurationBytes arrayBytes bytes,
      panValueFfiReadBytes access context memory bytesInWord configuration
          (context.valueToNat configurationLength) = some configurationBytes ∧
      panValueFfiReadBytes access context memory bytesInWord array
          (context.valueToNat arrayLength) = some arrayBytes ∧
      callFfi ffi (.extCall function) configurationBytes arrayBytes =
        .returned nextFfi bytes ∧
      nextMemory = panValueFfiWriteBytes access context memory bytesInWord
        array bytes := by
  unfold panValueFfiExtCall at h
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => simp [hconfiguration] at h
  | some configurationBytes =>
      cases harray : panValueFfiReadBytes access context memory bytesInWord
          array (context.valueToNat arrayLength) with
      | none => simp [hconfiguration, harray] at h
      | some arrayBytes =>
          cases hffi : callFfi ffi (.extCall function) configurationBytes arrayBytes with
          | final event => simp [hconfiguration, harray, hffi] at h
          | returned returnedFfi bytes =>
              simp [hconfiguration, harray, hffi] at h
              rcases h with ⟨hmem, hffiEq⟩
              exact ⟨configurationBytes, arrayBytes, bytes, rfl, rfl,
                by rw [← hffiEq]; exact hffi, hmem.symm⟩

inductive PanValueFfiControlResult (α : Type u) (σ : Type v) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | error (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (exception : ExceptionId) (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | finalFfi (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (event : FfiFinalEvent)

abbrev PanValueFfiSteppedResult (α : Type u) (σ : Type v) :=
  PanValueFfiControlResult α σ × Nat

abbrev PanValueStatefulFfiHandler (α : Type u) (σ : Type v) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) → FfiState σ →
      Option ((VarName → Option (PanValue α)) × FfiState σ)

/-! Bare-metal accelerator calls may update the Pancake memory map as well as
    the local environment and FFI state.  This is intentionally separate from
    `PanValueStatefulFfiHandler`: the latter models CakeML's ordinary FFI
    boundary, while this handler models an instruction-like target extension
    such as a ZisK accelerator. -/
abbrev PanValueMemoryFfiHandler (α : Type u) (σ : Type v) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
    (α → Option (PanValue α)) → FfiState σ →
      Option ((VarName → Option (PanValue α)) ×
        (α → Option (PanValue α)) × FfiState σ)

def restorePanValueFfiLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueFfiControlResult α σ → PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (restorePanValueLocal locals name oldValue) globals memory ffi
  | .error locals globals memory ffi =>
      .error (restorePanValueLocal locals name oldValue) globals memory ffi
  | .returned locals globals memory ffi values =>
      .returned (restorePanValueLocal locals name oldValue) globals memory ffi values
  | .raised locals globals memory ffi exception value =>
      .raised (restorePanValueLocal locals name oldValue) globals memory ffi exception value
  | .broke locals globals memory ffi =>
      .broke (restorePanValueLocal locals name oldValue) globals memory ffi
  | .continued locals globals memory ffi =>
      .continued (restorePanValueLocal locals name oldValue) globals memory ffi
  | .finalFfi locals globals memory ffi event =>
      .finalFfi (restorePanValueLocal locals name oldValue) globals memory ffi event

/-- Result of a `local` assignment leaf.  HOL's `Assign` returns `SOME Error`
with the unchanged state both when the source expression does not evaluate and
when `is_valid_value` rejects the evaluated value; this helper returns the
explicit `.error` control result in both cases. -/
def panValueAssignLocalResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueAssignmentValid structs locals globals .local name value then
        some (.normal (updatePanValueMap locals name value) globals memory ffi, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of a `global` assignment leaf; see `panValueAssignLocalResult`. -/
def panValueAssignGlobalResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueAssignmentValid structs locals globals .global name value then
        some (.normal locals (updatePanValueMap globals name value) memory ffi, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Acceptance test for the `Dec` leaf.  HOL's `Dec` returns `SOME Error` with
the unchanged state both when the initialiser does not evaluate and when its
shape does not match; this helper returns the accepted value with its step count
in the successful case and `none` otherwise. -/
def panValueDecAccepted
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape) :
    Option (PanValue α × Nat) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => none
  | some (evaluated, valueSteps) =>
      if panShapeMatches (panValueShape structs evaluated) shape then
        some (evaluated, valueSteps)
      else none

/-- Uncounted acceptance test for `Dec`, used by the clocked evaluators. -/
def panValueDecAcceptedValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValue α) :=
  match evalPanValueExpWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => none
  | some evaluated =>
      if panShapeMatches (panValueShape structs evaluated) shape then some evaluated else none

/-- Condition value of an `If`.  HOL evaluates the condition and requires a
word, returning `SOME Error` with the unchanged state otherwise. -/
def panValueIteConditionValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (condition : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option α :=
  match evalPanValueExpWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      condition memoryAccess with
  | some (.word value) => some value
  | _ => none

/-- Result of the `Primitive` leaf.  HOL returns `SOME Error` with the unchanged
state when the arguments do not evaluate, when `pan_primop` returns `NONE`, or
when `is_valid_value` rejects the result; the successful case updates the
destination variable. -/
def panValuePrimitiveResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (primitive : PanPrimitiveHandler α)
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpsCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      arguments memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (values, valueSteps) =>
      match primitive operator values with
      | none => some (.error locals globals memory ffi, valueSteps + 1)
      | some value =>
          match locals name with
          | none => some (.error locals globals memory ffi, valueSteps + 1)
          | some oldValue =>
              if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
                some (.normal (updatePanValueMap locals name value) globals memory ffi,
                  valueSteps + 1)
              else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of the `Store` leaf.  HOL's `Store` returns `SOME Error` with the
unchanged state when either operand does not evaluate, when the address is not a
word, or when the memory store fails. -/
def panValueStoreResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      address memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
          value memoryAccess with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address with
          | .word address =>
              match panValueStoreWithAccess memory bytesInWord address value memoryAccess with
              | some memory =>
                  some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
              | none =>
                  some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _ => some (.error locals globals memory ffi, addressSteps + valueSteps + 1)

/-- Result of the `Store32` leaf; see `panValueStoreResult`. -/
def panValueStore32Result
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      address memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
          value memoryAccess with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match memoryAccess with
              | none =>
                  some (.normal locals globals
                    (updatePanValueMemory memory address (.word value)) ffi,
                    addressSteps + valueSteps + 1)
              | some access =>
                  match access.store32 access.domain memory bytesInWord address value with
                  | some memory =>
                      some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
                  | none =>
                      some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Result of the `StoreByte` leaf; see `panValueStoreResult`. -/
def panValueStoreByteResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      address memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
          value memoryAccess with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match memoryAccess with
              | none =>
                  some (.normal locals globals
                    (updatePanValueMemory memory address (.word value)) ffi,
                    addressSteps + valueSteps + 1)
              | some access =>
                  match access.storeByte access.domain memory bytesInWord address value with
                  | some memory =>
                      some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
                  | none =>
                      some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Result of the `ShMemLoad` leaf.  HOL returns `SOME Error` with the unchanged
state when the address does not evaluate to a word, when the destination is not a
word-valued variable, or when the shared load fails. -/
def panValueShMemLoadResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      address memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match address with
      | .word address =>
          if panValueSharedLoadValid structs locals globals kind name (.word 0) then
            match panValueFfiSharedLoad context ffi size address with
            | some (.loaded nextFfi value) =>
                match kind with
                | .local =>
                    some (.normal (updatePanValueMap locals name (.word value)) globals memory
                      nextFfi, addressSteps + 1)
                | .global =>
                    some (.normal locals (updatePanValueMap globals name (.word value)) memory
                      nextFfi, addressSteps + 1)
            | some (.final nextFfi event) =>
                some (.finalFfi (fun _ => none) globals memory nextFfi event, addressSteps + 1)
            | some (.stored _) | none =>
                some (.error locals globals memory ffi, addressSteps + 1)
          else some (.error locals globals memory ffi, addressSteps + 1)
      | _ => some (.error locals globals memory ffi, addressSteps)

/-- Result of the `ShMemStore` leaf; see `panValueShMemLoadResult`. -/
def panValueShMemStoreResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (size : OpSize) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      address memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
          value memoryAccess with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match panValueFfiSharedStore context ffi size address value with
              | some (.stored nextFfi) =>
                  some (.normal locals globals memory nextFfi, addressSteps + valueSteps + 1)
              | some (.final nextFfi event) =>
                  some (.finalFfi locals globals memory nextFfi event,
                    addressSteps + valueSteps + 1)
              | some (.loaded _ _) | none =>
                  some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Counted condition value of an `If`, used by the executable leaf evaluator. -/
def panValueIteCondition
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (condition : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (α × Nat) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      condition memoryAccess with
  | some (.word value, steps) => some (value, steps)
  | _ => none

/-- Resolve the callee body and locals for a call.  HOL returns `SOME Error`
with the unchanged state when the function is missing or the arguments are
invalid. -/
def panValueCallTarget
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (contracts : Option PanValueCallContracts)
    (function : FunName) (functions : List (FunName × List VarName × Prog α))
    (values : List (PanValue α)) :
    Option (Prog α × (VarName → Option (PanValue α))) :=
  match lookupPanFunction function functions with
  | none => none
  | some (parameters, body) =>
      if panValueParametersValid structs contracts function values then
        match bindPanValueParameters parameters values with
        | some calleeLocals => some (body, calleeLocals)
        | none => none
      else none

/-- Counted evaluation of a call's argument list.  HOL returns `SOME Error`
with the unchanged state when this fails. -/
def panValueCallArguments
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (arguments : List (Exp α)) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (List (PanValue α) × Nat) :=
  evalPanValueExpsCounted structs locals globals memory baseAddress topAddress bytesInWord
    arguments memoryAccess

/-- Uncounted evaluation of a call's argument list; the clocked counterpart of
`panValueCallArguments`. -/
def panValueCallArgumentsValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (arguments : List (Exp α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (List (PanValue α)) :=
  evalPanValueExpsWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
    arguments memoryAccess

/-- Result of the `Return` leaf.  HOL returns `SOME Error` with the unchanged
state when the expression fails to evaluate or the payload exceeds the limit. -/
def panValueReturnResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValuePayloadWithinLimit structs value then
        some (.returned (fun _ => none) globals memory ffi [value], valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of the `Raise` leaf.  HOL returns `SOME Error` with the unchanged
state when the expression fails to evaluate or the exception shape/size is
invalid. -/
def panValueRaiseResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (contracts : Option PanValueCallContracts)
    (exception : VarName) (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      value memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueExceptionValid structs contracts exception value &&
          panValuePayloadWithinLimit structs value then
        some (.raised (fun _ => none) globals memory ffi exception value, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- The `ExtCall` program clause as a non-recursive helper.  Factoring it out
keeps the recursive `evalPanValueFfiProgSteps` match shape (and its generated
induction principle) unchanged while restoring the HOL `SOME Error` outcome on
argument-evaluation failure (`panSemScript.sml:711-729`). -/
def panValueFfiExtCallSteps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpsCountedWith evaluator structs locals globals memory baseAddress topAddress bytesInWord
      [configuration, configurationLength, array, arrayLength]
      memoryAccess with
  | none => some (.error locals globals memory ffi, 0)
  | some (values, expressionSteps) => do
      let [.word configuration, .word configurationLength, .word array, .word arrayLength] := values |
        some (.error locals globals memory ffi, expressionSteps)
      match memoryHandler with
      | some memoryHandler =>
          match memoryHandler function configuration configurationLength array arrayLength
              locals memory ffi with
          | some (locals, memory, ffi) =>
              pure (.normal locals globals memory ffi, expressionSteps + 1)
          | none =>
              match memoryAccess with
              | none =>
                  let (locals, ffi) ←
                    handler function configuration configurationLength array arrayLength locals ffi
                  pure (.normal locals globals memory ffi, expressionSteps + 1)
              | some access =>
                  match panValueFfiExtCall access context memory bytesInWord ffi function
                      configuration configurationLength array arrayLength with
                  | some (.returned memory ffi) =>
                      pure (.normal locals globals memory ffi, expressionSteps + 1)
                  | some (.final ffi event) =>
                      pure (.finalFfi (fun _ => none) globals memory ffi event,
                        expressionSteps + 1)
                  | none =>
                      some (.error locals globals memory ffi, expressionSteps + 1)
      | none =>
          match memoryAccess with
          | none =>
              let (locals, ffi) ←
                handler function configuration configurationLength array arrayLength locals ffi
              pure (.normal locals globals memory ffi, expressionSteps + 1)
          | some access =>
              match panValueFfiExtCall access context memory bytesInWord ffi function
                  configuration configurationLength array arrayLength with
              | some (.returned memory ffi) =>
                  pure (.normal locals globals memory ffi, expressionSteps + 1)
              | some (.final ffi event) =>
                  pure (.finalFfi (fun _ => none) globals memory ffi event,
                    expressionSteps + 1)
              | none =>
                  some (.error locals globals memory ffi, expressionSteps + 1)

structure PanValueFfiProgramState (α : Type u) (σ : Type v) where
  source : PanValueProgramState α
  ffi : FfiState σ
end Flapjack
