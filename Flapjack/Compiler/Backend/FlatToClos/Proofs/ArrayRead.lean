import Flapjack.Compiler.Backend.FlatToClos.Proofs.Element

/-! Array indexing prerequisites for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Related value arrays give the same bounds-check result. -/
theorem arrayBounds_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (items : List FlatSem.Value) (index : Int)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.varray items)) :
    ClosSem.applyMemory .boundsCheckArray [.refPtr true pointer, .number index] target =
      some (ClosSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat items.length)), target) := by
  obtain ⟨targetItems, targetFound, related⟩ := lookup_array states found
  have sameLength := related.length_eq
  simp [ClosSem.applyMemory, targetFound, ← sameLength]

/-- Related byte arrays give the same bounds-check result. -/
theorem byteArrayBounds_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (bytes : List (BitVec 8)) (index : Int)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.w8array bytes)) :
    ClosSem.applyMemory (.boundsCheckByte false) [.refPtr true pointer, .number index] target =
      some (ClosSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat bytes.length)), target) := by
  have targetFound := lookup_byteArray states found
  simp [ClosSem.applyMemory, targetFound]

/-- A successful value-array read retrieves related elements on both sides.
The same conclusion covers both safe and unsafe primitive reads. -/
theorem arrayRead_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int) (value : FlatSem.Value)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.varray items))
    (nonnegative : ¬index < 0) (element : items[index.toNat]? = some value) :
    ∃ targetValue,
      FlatSem.doAppMemory source .asub [.loc flag pointer, .litv (.intLit index)] =
        some (some (source, .val value)) ∧
      FlatSem.doAppMemory source .asubUnsafe [.loc flag pointer, .litv (.intLit index)] =
        some (some (source, .val value)) ∧
      ClosSem.applyMemory .el [.refPtr flag pointer, .number index] target = some (targetValue, target) ∧
      ValueRel value targetValue := by
  obtain ⟨targetItems, targetFound, related⟩ := lookup_array states found
  obtain ⟨targetValue, targetElement, valueRel⟩ := valueList_get_related items targetItems index.toNat value related element
  refine ⟨targetValue, ?_, ?_, ?_, valueRel⟩
  · simp [FlatSem.doAppMemory, FlatSem.readIndexed, found, nonnegative, element]
  · simp [FlatSem.doAppMemory, FlatSem.readIndexed, found, nonnegative, element]
  · simp [ClosSem.applyMemory, targetFound, nonnegative, targetElement]

/-- A successful byte-array read retrieves the same byte on both sides. -/
theorem byteArrayRead_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.w8array bytes))
    (nonnegative : ¬index < 0) (element : bytes[index.toNat]? = some byte) :
    FlatSem.doAppMemory source .aw8sub [.loc flag pointer, .litv (.intLit index)] =
      some (some (source, .val (.litv (.word8 byte)))) ∧
    FlatSem.doAppMemory source .aw8subUnsafe [.loc flag pointer, .litv (.intLit index)] =
      some (some (source, .val (.litv (.word8 byte)))) ∧
    ClosSem.applyMemory .derefByte [.refPtr flag pointer, .number index] target =
      some (.number byte.toNat, target) ∧
    ValueRel (.litv (.word8 byte)) (.number byte.toNat) := by
  have targetFound := lookup_byteArray states found
  simp [FlatSem.doAppMemory, FlatSem.readIndexed, found, nonnegative, element,
    ClosSem.applyMemory, targetFound, ValueRel.word8]

/-- A checked value-array read raises Subscript outside the valid range;
the unchecked primitive rejects the same invalid index. -/
theorem arrayRead_outOfBounds {C F : Type} (source : FlatSem.State C F)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int)
    (found : storeLookup pointer source.refs = some (.varray items))
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    FlatSem.doAppMemory source .asub [.loc flag pointer, .litv (.intLit index)] =
      some (some (source, .err (.raise FlatSem.subscriptExnV))) ∧
    FlatSem.doAppMemory source .asubUnsafe [.loc flag pointer, .litv (.intLit index)] = some none := by
  rcases bad with negative | bound
  · simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative]
  · by_cases negative : index < 0
    · simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative]
    · have missing : items[index.toNat]? = none := List.getElem?_eq_none bound
      simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, missing]

/-- A checked byte-array read raises Subscript outside the valid range;
the unchecked primitive rejects the same invalid index. -/
theorem byteArrayRead_outOfBounds {C F : Type} (source : FlatSem.State C F)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int)
    (found : storeLookup pointer source.refs = some (.w8array bytes))
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    FlatSem.doAppMemory source .aw8sub [.loc flag pointer, .litv (.intLit index)] =
      some (some (source, .err (.raise FlatSem.subscriptExnV))) ∧
    FlatSem.doAppMemory source .aw8subUnsafe [.loc flag pointer, .litv (.intLit index)] = some none := by
  rcases bad with negative | bound
  · simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative]
  · by_cases negative : index < 0
    · simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative]
    · have missing : bytes[index.toNat]? = none := List.getElem?_eq_none bound
      simp [FlatSem.doAppMemory, FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, missing]

/-- The closure code emitted for a checked byte read returns the selected
byte when the index is valid. -/
theorem evaluate_checkedByteRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (found : state.refs.lookup pointer = some (.byteArray bytes))
    (nonnegative : ¬index < 0) (element : bytes[index.toNat]? = some byte) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) state = (.val [.number byte.toNat], state) := by
  have bound : index.toNat < bytes.length := (List.getElem?_eq_some_iff.mp element).1
  have byteEq : bytes[index.toNat] = byte := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (bytes.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, found, valid, nonnegative, byteEq]

/-- The closure code emitted for a checked byte read raises Subscript when
the index is outside the byte array. -/
theorem evaluate_checkedByteRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (bytes : List (BitVec 8)) (index : Int)
    (found : state.refs.lookup pointer = some (.byteArray bytes))
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (bytes.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, found, invalid]

/-- The emitted checked byte read and the flat operation have related
results and leave related states unchanged, for all integer indices. -/
theorem checkedByteRead_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.w8array bytes)) :
    let flat := FlatSem.applyResult source (.src .aw8sub) [.loc flag pointer, .litv (.intLit index)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have targetFound := lookup_byteArray states found
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedByteRead_outOfBounds target trace env pointer flag bytes index targetFound (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, body, states, EvalResultRel.raise exception]
  · cases element : bytes[index.toNat]? with
    | none =>
      have bound : bytes.length ≤ index.toNat := List.getElem?_eq_none_iff.mp element
      have body := evaluate_checkedByteRead_outOfBounds target trace env pointer flag bytes index targetFound (Or.inr bound)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, element, body, states, EvalResultRel.raise exception]
    | some byte =>
      have body := evaluate_checkedByteRead_inBounds target trace env pointer flag bytes index byte targetFound negative element
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.readIndexed, found, negative, element, body, states, EvalResultRel.value (.cons (ValueRel.word8 byte) .nil)]

/-- Checked byte reads reject any argument count other than two. -/
theorem checkedByteRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .aw8sub) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Checked byte-array indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_checkedByteRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .aw8sub) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .aw8sub) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
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
        have resultShape : (FlatSem.applyResult next (.src .aw8sub) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply checkedByteRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory] at resultShape
              case int.loc index flag pointer =>
                cases found : storeLookup pointer next.refs with
                | none => simp [found] at resultShape
                | some entry =>
                  cases entry <;> simp [found] at resultShape
                  case w8array bytes =>
                    simpa using checkedByteRead_body_related next nextTarget trace values pointer flag bytes index states found

/-- The emitted checked value-array read returns the indexed element. -/
theorem evaluate_checkedArrayRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (items : List ClosSem.Value) (index : Int) (value : ClosSem.Value)
    (found : state.refs.lookup pointer = some (.valueArray items))
    (nonnegative : ¬index < 0) (element : items[index.toNat]? = some value) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) state = (.val [value], state) := by
  have bound : index.toNat < items.length := (List.getElem?_eq_some_iff.mp element).1
  have valueEq : items[index.toNat] = value := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (items.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, found, valid, nonnegative, valueEq]

/-- The emitted checked value-array read raises Subscript outside bounds. -/
theorem evaluate_checkedArrayRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (pointer : Nat) (flag : Bool)
    (items : List ClosSem.Value) (index : Int)
    (found : state.refs.lookup pointer = some (.valueArray items))
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (items.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, found, invalid]

/-- The emitted checked value-array read agrees with the flat operation for
every integer index and preserves related states. -/
theorem checkedArrayRead_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (items : List FlatSem.Value) (index : Int)
    (states : StateRel source target) (found : storeLookup pointer source.refs = some (.varray items)) :
    let flat := FlatSem.applyResult source (.src .asub) [.loc flag pointer, .litv (.intLit index)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .refPtr flag pointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  obtain ⟨targetItems, targetFound, related⟩ := lookup_array states found
  have sameLength := related.length_eq
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedArrayRead_outOfBounds target trace env pointer flag targetItems index targetFound (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, body, states, EvalResultRel.raise exception]
  · cases element : items[index.toNat]? with
    | none =>
      have bound : targetItems.length ≤ index.toNat := by
        have bound := List.getElem?_eq_none_iff.mp element
        omega
      have body := evaluate_checkedArrayRead_outOfBounds target trace env pointer flag targetItems index targetFound (Or.inr bound)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.readIndexed, FlatSem.boundsFailure, found, negative, element, body, states, EvalResultRel.raise exception]
    | some value =>
      obtain ⟨targetValue, targetElement, valueRel⟩ := valueList_get_related items targetItems index.toNat value related element
      have body := evaluate_checkedArrayRead_inBounds target trace env pointer flag targetItems index targetValue targetFound negative targetElement
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        FlatSem.readIndexed, found, negative, element, body, states, EvalResultRel.value (.cons valueRel .nil)]

/-- Checked value-array reads reject any argument count other than two. -/
theorem checkedArrayRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .asub) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Checked value-array indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_checkedArrayRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .asub) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .asub) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
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
        have resultShape : (FlatSem.applyResult next (.src .asub) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply checkedArrayRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory] at resultShape
              case int.loc index flag pointer =>
                cases found : storeLookup pointer next.refs with
                | none => simp [found] at resultShape
                | some entry =>
                  cases entry <;> simp [found] at resultShape
                  case varray items =>
                    simpa using checkedArrayRead_body_related next nextTarget trace values pointer flag items index states found


/-- Unchecked value-array reads reject any argument count other than two. -/
theorem uncheckedArrayRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .asubUnsafe) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Unchecked value-array indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_uncheckedArrayRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .asubUnsafe) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .asubUnsafe) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
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
        have resultShape : (FlatSem.applyResult next (.src .asubUnsafe) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply uncheckedArrayRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory] at resultShape
              case int.loc index flag pointer =>
                cases found : storeLookup pointer next.refs with
                | none => simp [found] at resultShape
                | some entry =>
                  cases entry <;> simp [found] at resultShape
                  case varray items =>
                    by_cases negative : index < 0
                    · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at resultShape
                    · cases element : items[index.toNat]? with
                      | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at resultShape
                      | some value =>
                        obtain ⟨targetValue, _, _, targetRead, valueRel⟩ :=
                          arrayRead_related next nextTarget pointer flag items index value states found negative element
                        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.readIndexed, found, negative, element, ClosSem.doApp, targetRead,
                          states, EvalResultRel.value (.cons valueRel .nil)]


/-- Unchecked byte-array reads reject any argument count other than two. -/
theorem uncheckedByteRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .aw8subUnsafe) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Unchecked byte-array indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_uncheckedByteRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .aw8subUnsafe) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .aw8subUnsafe) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
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
        have resultShape : (FlatSem.applyResult next (.src .aw8subUnsafe) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply uncheckedByteRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory] at resultShape
              case int.loc index flag pointer =>
                cases found : storeLookup pointer next.refs with
                | none => simp [found] at resultShape
                | some entry =>
                  cases entry <;> simp [found] at resultShape
                  case w8array bytes =>
                    by_cases negative : index < 0
                    · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at resultShape
                    · cases element : bytes[index.toNat]? with
                      | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at resultShape
                      | some byte =>
                        obtain ⟨_, _, targetRead, valueRel⟩ :=
                          byteArrayRead_related next nextTarget pointer flag bytes index byte states found negative element
                        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.readIndexed, found, negative, element, ClosSem.doApp, targetRead,
                          states, EvalResultRel.value (.cons valueRel .nil)]

end Flapjack.Compiler.Backend.FlatToClos
