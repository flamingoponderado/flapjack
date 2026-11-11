module

public import Flapjack.Misc.ByteDecoding
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
public import Flapjack.Misc.Option.Characterization
public import Aesop

@[expose] public section

/-! Correspondence between closure byte traversals and the guarded choices
used by the original primitive dispatcher. These are Lean infrastructure
lemmas, not separate HOL declarations. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

namespace MemoryChoicePort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end MemoryChoicePort

/-- The byte-vector traversal succeeds exactly on the corresponding list. -/
theorem byteVectors_eq_some (values : List Value) (chunks : List (List (BitVec 8))) :
    byteVectors values = some chunks ↔ values = chunks.map Value.byteVector := by
  induction values generalizing chunks with
  | nil => cases chunks <;> simp [byteVectors]
  | cons head tail ih =>
    cases head <;> cases chunks <;> simp_all [byteVectors, Option.map_eq_some_iff]
    exact and_comm

/-- The byte-number traversal succeeds exactly on unsigned byte encodings. -/
theorem byteNumbers_eq_some (values : List Value) (bytes : List (BitVec 8)) :
    byteNumbers values = some bytes ↔ values = bytes.map (fun b => .number b.toNat) := by
  induction values generalizing bytes with
  | nil => cases bytes <;> simp [byteNumbers]
  | cons head tail ih =>
    cases head <;> cases bytes <;> simp_all [byteNumbers, Option.bind_eq_some_iff, intToByte_iff]

/-- Decode a closure list of byte-vector chunks. -/
def byteVectorChunks (value : Value) : Option (List (List (BitVec 8))) :=
  (valueToList value).bind byteVectors

/-- Chunk decoding matches the predicate in `ConcatByteVec`. -/
theorem byteVectorChunks_eq_some (value : Value) (chunks : List (List (BitVec 8))) :
    byteVectorChunks value = some chunks ↔ valueToList value = some (chunks.map Value.byteVector) := by
  simp [byteVectorChunks, Option.bind_eq_some_iff, byteVectors_eq_some]

/-- Chunk decoding agrees with the original guarded choice, including failure. -/
theorem byteVectorChunks_eq_holChoice (value : Value) :
    byteVectorChunks value = Flapjack.holOptionSome
      (fun chunks : List (List (BitVec 8)) => valueToList value = some (chunks.map Value.byteVector)) := by
  exact Flapjack.option_eq_holChoice _ _ (byteVectorChunks_eq_some value)

/-- Decode byte-valued integer elements as their natural numbers. -/
def byteNaturalValues (values : List Value) : Option (List Nat) :=
  (byteNumbers values).map (List.map BitVec.toNat)

/-- Natural decoding preserves precisely the original element bounds. -/
theorem byteNaturalValues_eq_some (values : List Value) (numbers : List Nat) :
    byteNaturalValues values = some numbers ↔
      values = numbers.map (fun n => .number n) ∧ ∀ n ∈ numbers, n < 256 :=
  byteNaturalValues_eq_some_generic (fun n => Value.number (n : Int)) byteNumbers
    byteNumbers_eq_some values numbers

/-- The naturals selected by the source `FromListByte` predicate. -/
def byteNaturalList (value : Value) : Option (List Nat) :=
  (valueToList value).bind byteNaturalValues

/-- Natural-list decoding matches the original list and range predicate. -/
theorem byteNaturalList_eq_some (value : Value) (numbers : List Nat) :
    byteNaturalList value = some numbers ↔
      valueToList value = some (numbers.map (fun n => .number n)) ∧
        ∀ n ∈ numbers, n < 256 := by
  simp [byteNaturalList, Option.bind_eq_some_iff, byteNaturalValues_eq_some]
  aesop

/-- The natural-list decoder agrees with HOL's choice, including failure. -/
theorem byteNaturalList_eq_holChoice (value : Value) :
    byteNaturalList value = Flapjack.holOptionSome
      (fun numbers : List Nat => valueToList value = some (numbers.map (fun n => .number n)) ∧
        ∀ n ∈ numbers, n < 256) := by
  exact Flapjack.option_eq_holChoice _ _ (byteNaturalList_eq_some value)

/-- Converting the selected naturals back to bytes gives the actual traversal
used by the closure primitive dispatcher. -/
theorem byteNaturalList_reconstruct (value : Value) :
    (byteNaturalList value).map (List.map (BitVec.ofNat 8)) =
      (valueToList value).bind byteNumbers := by
  cases decoded : valueToList value with
  | none => simp [byteNaturalList, decoded]
  | some values =>
    simp only [byteNaturalList, decoded, Option.bind_some, byteNaturalValues]
    cases run : byteNumbers values with
    | none => rfl
    | some bytes => simp [List.map_map, Function.comp_def]

/-- The actual concatenation branch has the same result, including errors,
as the source guarded-choice expression. -/
theorem applyMemory_concatByteVec_choice {C F : Type} (state : State C F) (value : Value) :
    applyMemory .concatByteVec [value] state =
      (Flapjack.holOptionSome
        (fun chunks : List (List (BitVec 8)) => valueToList value = some (chunks.map Value.byteVector))).map
        (fun chunks => (.byteVector chunks.flatten, state)) := by
  rw [← byteVectorChunks_eq_holChoice]
  unfold byteVectorChunks applyMemory
  cases decoded : valueToList value with
  | none => simp [decoded]
  | some values => cases chunks : byteVectors values <;> simp [decoded, chunks]

/-- The actual byte-list branch agrees with the source choice of bounded
natural numbers, followed by conversion to word8. -/
theorem applyMemory_fromListByte_choice {C F : Type} (state : State C F) (value : Value) :
    applyMemory .fromListByte [value] state =
      (Flapjack.holOptionSome
        (fun numbers : List Nat => valueToList value = some (numbers.map (fun n => .number n)) ∧
          ∀ n ∈ numbers, n < 256)).map
        (fun numbers => (.byteVector (numbers.map (BitVec.ofNat 8)), state)) := by
  rw [← byteNaturalList_eq_holChoice]
  unfold byteNaturalList byteNaturalValues applyMemory
  cases decoded : valueToList value with
  | none => simp [decoded]
  | some values =>
    cases bytes : byteNumbers values <;> simp [decoded, bytes, List.map_map, Function.comp_def]

/-- The assembled dispatcher implements the original concatenation choice. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "do_app_def"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_concatByteVec_choice {C F : Type} (state : State C F) (value : Value) :
    doApp (.memOp .concatByteVec) [value] state =
      match Flapjack.holOptionSome
        (fun chunks : List (List (BitVec 8)) => valueToList value = some (chunks.map Value.byteVector)) with
      | none => .err (.abort .typeError)
      | some chunks => .val (.byteVector chunks.flatten, state) := by
  simp only [doApp, applyMemory_concatByteVec_choice]
  cases Flapjack.holOptionSome
    (fun chunks : List (List (BitVec 8)) => valueToList value = some (chunks.map Value.byteVector)) <;> rfl

/-- The assembled dispatcher implements the original bounded-natural choice. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "do_app_def"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_fromListByte_choice {C F : Type} (state : State C F) (value : Value) :
    doApp (.memOp .fromListByte) [value] state =
      match Flapjack.holOptionSome
        (fun numbers : List Nat => valueToList value = some (numbers.map (fun n => .number n)) ∧
          ∀ n ∈ numbers, n < 256) with
      | none => .err (.abort .typeError)
      | some numbers => .val (.byteVector (numbers.map (BitVec.ofNat 8)), state) := by
  simp only [doApp, applyMemory_fromListByte_choice]
  cases Flapjack.holOptionSome
    (fun numbers : List Nat => valueToList value = some (numbers.map (fun n => .number n)) ∧
      ∀ n ∈ numbers, n < 256) <;> rfl

end Flapjack.Compiler.Backend.ClosSem
