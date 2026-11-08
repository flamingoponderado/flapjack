import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl

/-! Array operation simulation for the source-to-flat primitive proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- A non-type-error dynamic allocation has an integer size operand. -/
theorem aalloc_size_operand {F : Type} (source : State F) (size value : Value)
    (successful : doApp (source.refs, source.ffi) .aalloc [size, value] ≠ none) :
    ∃ n, size = .litv (.intLit n) := by
  cases size <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv lit =>
    cases lit <;> simp at successful
    case intLit n => exact ⟨n, rfl⟩

/-- A non-type-error byte-array allocation has integer size and Word8 value operands. -/
theorem aw8alloc_operands {F : Type} (source : State F) (size value : Value)
    (successful : doApp (source.refs, source.ffi) .aw8alloc [size, value] ≠ none) :
    ∃ n byte, size = .litv (.intLit n) ∧ value = .litv (.word8 byte) := by
  cases size <;> cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv.litv sizeLit valueLit =>
    cases sizeLit <;> cases valueLit <;> simp at successful
    case intLit.word8 n byte => exact ⟨n, byte, rfl, rfl⟩

/-- A successful array length operation identifies a source array cell. -/
theorem alength_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .alength [operand] ≠ none) :
    ∃ flag address values, operand = .loc flag address ∧ storeLookup address source.refs = some (.varray values) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases lookup : storeLookup address source.refs with
    | none => simp [lookup] at successful
    | some cell =>
      cases cell with
      | varray values => exact ⟨flag, address, values, rfl, lookup⟩
      | refv value => simp [lookup] at successful
      | w8array bytes => simp [lookup] at successful
      | thunk mode value => simp [lookup] at successful

/-- A successful byte-array length operation identifies a source byte-array cell. -/
theorem aw8length_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .aw8length [operand] ≠ none) :
    ∃ flag address bytes, operand = .loc flag address ∧ storeLookup address source.refs = some (.w8array bytes) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases lookup : storeLookup address source.refs with
    | none => simp [lookup] at successful
    | some cell =>
      cases cell with
      | w8array bytes => exact ⟨flag, address, bytes, rfl, lookup⟩
      | refv value => simp [lookup] at successful
      | varray values => simp [lookup] at successful
      | thunk mode value => simp [lookup] at successful

/-- A byte-array subscript without a type error has a location, integer
index, and byte-array store cell. -/
theorem aw8sub_operands {F : Type} (source : State F) (pointer index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aw8subUnsafe else .aw8sub)
      [pointer, index] ≠ none) :
    ∃ flag address n bytes, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.w8array bytes) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i bytes
  all_goals exact ⟨flag, address, n, bytes, rfl, rfl, lookup⟩

/-- Byte-array subscript dispatch agrees on success, checked bounds errors,
and unchecked failure. Both states remain unchanged. -/
theorem aw8sub_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8subUnsafe else .aw8sub
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = sourceState.refs ∧ ffi = sourceState.ffi ∧ nextFlat = flatState ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aw8sub_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
      index (Or.inl negative) unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
  · cases element : bytes[index.toNat]? with
    | none =>
      have ⟨src, dst, exceptionRel⟩ := aw8sub_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
        index (Or.inr element) unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
    | some byte =>
      have ⟨src, dst, valueRel⟩ := aw8sub_related genv sourceState flatState statesRel flag n bytes lookup index
        (Int.le_of_not_gt negative) byte element unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.value valueRel]

/-- An array subscript without a type error has a location, integer
index, and array store cell. -/
theorem asub_operands {F : Type} (source : State F) (pointer index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .asubUnsafe else .asub)
      [pointer, index] ≠ none) :
    ∃ flag address n values, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.varray values) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i values
  all_goals exact ⟨flag, address, n, values, rfl, rfl, lookup⟩

/-- Array subscript dispatch preserves related results and states. -/
theorem asub_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value) (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.asubUnsafe else .asub
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = sourceState.refs ∧ ffi = sourceState.ffi ∧ nextFlat = flatState ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := asub_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
      index (Or.inl negative) unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
  · cases element : values[index.toNat]? with
    | none =>
      have ⟨src, dst, exceptionRel⟩ := asub_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
        index (Or.inr element) unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
    | some value =>
      obtain ⟨flatValue, src, dst, valueRel⟩ := asub_related genv sourceState flatState statesRel flag n values lookup index
        (Int.le_of_not_gt negative) value element unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.value valueRel]

/-- A byte-array update without a type error has a byte-array location,
integer index, and byte value. -/
theorem aw8update_operands {F : Type} (source : State F) (pointer index value : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aw8updateUnsafe else .aw8update)
      [pointer, index, value] ≠ none) :
    ∃ flag address n byte bytes, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      value = .litv (.word8 byte) ∧ storeLookup address source.refs = some (.w8array bytes) := by
  cases unsafeOp <;> cases pointer <;> cases index <;> cases value <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address indexLit valueLit
  all_goals cases indexLit <;> cases valueLit <;> simp at successful
  all_goals rename_i n byte
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i bytes
  all_goals exact ⟨flag, address, n, byte, bytes, rfl, rfl, rfl, lookup⟩

/-- Checked and unchecked byte-array updates preserve the factored state
relation, result relation, and reserved flat store entry. -/
theorem aw8update_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (byte : BitVec 8) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8updateUnsafe else .aw8update
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index), .litv (.word8 byte)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index), .litv (.word8 byte)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = sourceState.ffi ∧ nextFlat = { flatState with refs := nextFlat.refs } ∧
        StateRel genv { sourceState with refs := refs } nextFlat ∧
        nextFlat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aw8update_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
      index (Or.inl negative) byte unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]
  · by_cases inBounds : index.toNat < bytes.length
    · obtain ⟨flatRefs, src, dst, valueRel, nextRel, reserved⟩ := aw8update_related genv sourceState flatState
        statesRel flag n bytes lookup index (Int.le_of_not_gt negative) inBounds byte unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, nextRel, reserved, ResultRel.value valueRel]
    · have ⟨src, dst, exceptionRel⟩ := aw8update_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
        index (Or.inr (Nat.le_of_not_gt inBounds)) byte unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]

/-- A value-array update without a type error has an array location and integer index. -/
theorem aupdate_operands {F : Type} (source : State F) (pointer index value : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aupdateUnsafe else .aupdate)
      [pointer, index, value] ≠ none) :
    ∃ flag address n values, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.varray values) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address indexLit
  all_goals cases indexLit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i values
  all_goals exact ⟨flag, address, n, values, rfl, rfl, lookup⟩

/-- Checked and unchecked value-array updates preserve the factored state
relation, result relation, and reserved flat store entry. -/
theorem aupdate_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value) (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (value : SemanticPrimitivesHOL.Value) (flatValue : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aupdateUnsafe else .aupdate
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index), value],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index), flatValue] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = sourceState.ffi ∧ nextFlat = { flatState with refs := nextFlat.refs } ∧
        StateRel genv { sourceState with refs := refs } nextFlat ∧
        nextFlat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aupdate_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
      index (Or.inl negative) value flatValue unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]
  · by_cases inBounds : index.toNat < values.length
    · obtain ⟨flatRefs, src, dst, resultRel, nextRel, reserved⟩ := aupdate_related genv sourceState flatState
        statesRel flag n values lookup index (Int.le_of_not_gt negative) inBounds value flatValue valueRel unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, nextRel, reserved, ResultRel.value resultRel]
    · have ⟨src, dst, exceptionRel⟩ := aupdate_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
        index (Or.inr (Nat.le_of_not_gt inBounds)) value flatValue unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]

end Flapjack.Compiler.Backend.SourceToFlat
