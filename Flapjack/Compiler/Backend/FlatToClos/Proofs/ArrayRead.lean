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

end Flapjack.Compiler.Backend.FlatToClos
