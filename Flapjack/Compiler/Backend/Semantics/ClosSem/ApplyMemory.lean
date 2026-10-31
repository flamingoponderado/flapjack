import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic
import Flapjack.SemanticPrimitivesHOL.Array
import Flapjack.SemanticPrimitivesHOL.Thunk
import Flapjack.SemanticPrimitivesHOL.Compare
import Mathlib.Data.Nat.Find

/-! Memory cases of the closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private theorem natList_bounded (keys : List Nat) : ∃ bound, ∀ key ∈ keys, key < bound := by
  induction keys with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
    obtain ⟨bound, h⟩ := ih
    refine ⟨max first bound + 1, ?_⟩
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := h key member
      omega

/-- A finite-support reference map always has an unused natural index. -/
theorem unusedRef_exists (refs : HolFiniteMapExact Nat (Ref Value)) : ∃ index, refs.lookup index = none := by
  classical
  obtain ⟨keys, support⟩ := refs.finiteSupport
  obtain ⟨bound, bounded⟩ := natList_bounded keys
  refine ⟨bound, ?_⟩
  cases h : refs.lookup bound with
  | none => rfl
  | some value =>
    have member := support bound (by simp [h])
    have impossible := bounded bound member
    omega

/-- Least unallocated reference, matching the HOL `LEAST` selection. -/
noncomputable def leastUnusedRef (refs : HolFiniteMapExact Nat (Ref Value)) : Nat := by
  classical
  exact Nat.find (unusedRef_exists refs)

/-- The selected reference is unused. -/
theorem leastUnusedRef_unused (refs : HolFiniteMapExact Nat (Ref Value)) :
    refs.lookup (leastUnusedRef refs) = none := by
  classical
  exact Nat.find_spec (unusedRef_exists refs)

/-- Every smaller reference is allocated. -/
theorem leastUnusedRef_minimal (refs : HolFiniteMapExact Nat (Ref Value)) (index : Nat)
    (smaller : index < leastUnusedRef refs) : refs.lookup index ≠ none := by
  classical
  exact Nat.find_min (unusedRef_exists refs) smaller

/-- A free zero slot is necessarily the next allocated reference. -/
theorem leastUnusedRef_eq_zero (refs : HolFiniteMapExact Nat (Ref Value))
    (free : refs.lookup 0 = none) : leastUnusedRef refs = 0 := by
  classical
  have bound := Nat.find_min' (unusedRef_exists refs) free
  exact Nat.eq_zero_of_le_zero bound

/-- Decode byte-vector values in their original list order. -/
def byteVectors : List Value → Option (List (List (BitVec 8)))
  | [] => some []
  | .byteVector bytes :: values => (byteVectors values).map (bytes :: ·)
  | _ => none

/-- Decode numeric values as bytes, rejecting values outside the byte range. -/
def byteNumbers : List Value → Option (List (BitVec 8))
  | [] => some []
  | .number number :: values => do
    let byte ← intToByte number
    let rest ← byteNumbers values
    some (byte :: rest)
  | _ => none

/-- Closure memory operations. Invalid argument shapes, bounds and store
entries return `none`, representing the original type error. This proof-side
dispatcher remains untagged pending finite-map and source review. -/
noncomputable def applyMemory {C F : Type} (op : ClosLang.MemOp) (args : List Value) (state : State C F) :
    Option (Value × State C F) := by
  let result (value : Value) := some (value, state)
  let write (index : Nat) (value : Ref Value) :=
    some (unitValue, { state with refs := state.refs.updateEq (index, value) })
  let allocate (flag : Bool) (value : Ref Value) :=
    let index := leastUnusedRef state.refs
    some (Value.refPtr flag index, { state with refs := state.refs.updateEq (index, value) })
  exact match op, args with
  | .el, [.block _ values, .number index] =>
    if index < 0 then none else (values[index.toNat]?).bind result
  | .el, [.refPtr _ ptr, .number index] =>
    match state.refs.lookup ptr with
    | some (.valueArray values) => if index < 0 then none else (values[index.toNat]?).bind result
    | _ => none
  | .length, [.refPtr _ ptr] => match state.refs.lookup ptr with
    | some (.valueArray values) => result (.number values.length)
    | _ => none
  | .lengthByte, [.refPtr _ ptr] => match state.refs.lookup ptr with
    | some (.byteArray bytes) => result (.number bytes.length)
    | _ => none
  | .refByte false, [.number count, .number byte] => do
    if count < 0 then none else
      let b ← intToByte byte
      allocate true (.byteArray (List.replicate count.toNat b))
  | .refArray, [.number count, value] =>
    if count < 0 then none else allocate true (.valueArray (List.replicate count.toNat value))
  | .ref, values => allocate true (.valueArray values)
  | .derefByte, [.refPtr _ ptr, .number index] => match state.refs.lookup ptr with
    | some (.byteArray bytes) =>
      if index < 0 then none else (bytes[index.toNat]?).bind (fun b => result (.number b.toNat))
    | _ => none
  | .updateByte, [.refPtr _ ptr, .number index, .number byte] => match state.refs.lookup ptr with
    | some (.byteArray bytes) => do
      if index < 0 ∨ index.toNat ≥ bytes.length then none else
        let b ← intToByte byte
        write ptr (.byteArray (bytes.set index.toNat b))
    | _ => none
  | .update, [.refPtr _ ptr, .number index, value] => match state.refs.lookup ptr with
    | some (.valueArray values) =>
      if index < 0 ∨ index.toNat ≥ values.length then none
      else write ptr (.valueArray (values.set index.toNat value))
    | _ => none
  | .concatByteVec, [value] => do
    let values ← valueToList value
    let chunks ← byteVectors values
    result (.byteVector chunks.flatten)
  | .fromListByte, [value] => do
    let values ← valueToList value
    let bytes ← byteNumbers values
    result (.byteVector bytes)
  | .toListByte, [.byteVector bytes] => result (listToValue (bytes.map (fun b => .number b.toNat)))
  | .lengthByteVec, [.byteVector bytes] => result (.number bytes.length)
  | .derefByteVec, [.byteVector bytes, .number index] =>
    if index < 0 then none else (bytes[index.toNat]?).bind (fun b => result (.number b.toNat))
  | .copyByte false, [.byteVector source, .number offset, .number length, .refPtr _ dst, .number dstOffset] => do
    let .byteArray bytes ← state.refs.lookup dst | none
    let copied ← copyArray (source, offset) length (some (bytes, dstOffset))
    write dst (.byteArray copied)
  | .copyByte false, [.refPtr _ src, .number offset, .number length, .refPtr _ dst, .number dstOffset] => do
    let .byteArray source ← state.refs.lookup src | none
    let .byteArray bytes ← state.refs.lookup dst | none
    let copied ← copyArray (source, offset) length (some (bytes, dstOffset))
    write dst (.byteArray copied)
  | .copyByte true, [.byteVector source, .number offset, .number length] => do
    let copied ← copyArray (source, offset) length none
    result (.byteVector copied)
  | .copyByte true, [.refPtr _ src, .number offset, .number length] => do
    let .byteArray source ← state.refs.lookup src | none
    let copied ← copyArray (source, offset) length none
    result (.byteVector copied)
  | .xorByte, [.refPtr _ dst, .byteVector source] => do
    let .byteArray bytes ← state.refs.lookup dst | none
    let updated ← xorBytes source bytes
    write dst (.byteArray updated)
  | .stringCmp fast op, [.byteVector a, .byteVector b] =>
    result (boolValue (strCmp fast op (.implode a) (.implode b)))
  | .boundsCheckByte loose, [.byteVector bytes, .number index] =>
    result (boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)))
  | .boundsCheckByte loose, [.refPtr _ ptr, .number index] => match state.refs.lookup ptr with
    | some (.byteArray bytes) =>
      result (boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)))
    | _ => none
  | .boundsCheckArray, [.refPtr _ ptr, .number index] => match state.refs.lookup ptr with
    | some (.valueArray values) => result (boolValue (decide (0 ≤ index ∧ index < Int.ofNat values.length)))
    | _ => none
  | .configGC, [.number _, .number _] => result unitValue
  | _, _ => none

private theorem byteNumbers_charEncoding (chars : List (BitVec 8)) :
    byteNumbers (chars.map (fun byte => .number byte.toNat)) = some chars := by
  induction chars with
  | nil => rfl
  | cons first rest ih => simp [byteNumbers, intToByte_toNat, ih]

/-- Decoding a closure character list constructs the corresponding byte
vector. This is a Lean helper for the flat-to-closure simulation. -/
theorem applyMemory_fromCharList {C F : Type} (state : State C F) (value : Value) (chars : List (BitVec 8))
    (decoded : valueToList value = some (chars.map (fun byte => .number byte.toNat))) :
    applyMemory .fromListByte [value] state = some (.byteVector chars, state) := by
  simp [applyMemory, decoded, byteNumbers_charEncoding]

private theorem byteVectors_encoded (chunks : List (List (BitVec 8))) :
    byteVectors (chunks.map Value.byteVector) = some chunks := by
  induction chunks with
  | nil => rfl
  | cons first rest ih => simp [byteVectors, ih]

/-- Decoding a list of byte vectors yields their flattened concatenation.
This is a Lean helper for the flat-to-closure simulation. -/
theorem applyMemory_concatByteVectors {C F : Type} (state : State C F) (value : Value)
    (chunks : List (List (BitVec 8)))
    (decoded : valueToList value = some (chunks.map Value.byteVector)) :
    applyMemory .concatByteVec [value] state = some (.byteVector chunks.flatten, state) := by
  simp [applyMemory, decoded, byteVectors_encoded]

end Flapjack.Compiler.Backend.ClosSem
