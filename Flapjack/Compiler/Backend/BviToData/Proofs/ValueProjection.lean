module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
import Aesop

@[expose] public section

/-! Constructor characterizations for value projection. -/

namespace Flapjack.Compiler.Backend.BviToData

/-- Characterize each projected value constructor. The four independent
inhabited types model HOL’s unused polymorphic binders. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_eq"]
theorem dataToBviValue_eq {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] :
    (∀ (v : DataSem.Value) (_ : A) (i : Int),
      dataToBviValue v = .number i ↔ v = .number i) ∧
    (∀ (v : DataSem.Value) (_ : B) (w : BitVec 64),
      dataToBviValue v = .word64 w ↔ v = .word64 w) ∧
    (∀ (v : DataSem.Value) (_ : C) (p : Nat),
      dataToBviValue v = .codePtr p ↔ v = .codePtr p) ∧
    (∀ (v : DataSem.Value) (_ : D) (r : Nat) (b : Bool),
      dataToBviValue v = .refPtr b r ↔ v = .refPtr b r) ∧
    (∀ (v : DataSem.Value) (n : Nat) (values : List BvlSem.Value),
      dataToBviValue v = .block n values ↔
        ∃ timestamp dataValues, v = .block timestamp n dataValues ∧
          values = dataValues.map dataToBviValue) := by
  repeat' constructor
  all_goals intro v
  all_goals cases v <;> simp [dataToBviValue, eq_comm] <;> aesop

/-- The constructor characterizations with their equalities reversed. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_eq'"]
theorem dataToBviValue_eq_flip {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] :
    (∀ (v : DataSem.Value) (_ : A) (i : Int),
      .number i = dataToBviValue v ↔ v = .number i) ∧
    (∀ (v : DataSem.Value) (_ : B) (w : BitVec 64),
      .word64 w = dataToBviValue v ↔ v = .word64 w) ∧
    (∀ (v : DataSem.Value) (_ : C) (p : Nat),
      .codePtr p = dataToBviValue v ↔ v = .codePtr p) ∧
    (∀ (v : DataSem.Value) (_ : D) (r : Nat) (b : Bool),
      .refPtr b r = dataToBviValue v ↔ v = .refPtr b r) ∧
    (∀ (v : DataSem.Value) (n : Nat) (values : List BvlSem.Value),
      .block n values = dataToBviValue v ↔
        ∃ timestamp dataValues, v = .block timestamp n dataValues ∧
          values = dataValues.map dataToBviValue) := by
  simpa only [eq_comm] using (dataToBviValue_eq (A := A) (B := B) (C := C) (D := D))

/-- A projected list of 64-bit words has exactly the corresponding DATA
word-list preimage. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "MAP_data_to_bvi_Word64"]
theorem mapDataToBviWord64 (xs : List (BitVec 64)) (ws : List DataSem.Value) :
    (xs.map DataSem.Value.word64).map dataToBviValue = ws.map dataToBviValue ↔
      xs.map DataSem.Value.word64 = ws := by
  induction xs generalizing ws with
  | nil => cases ws <;> simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      cases w <;> simp only [List.map_cons, dataToBviValue, List.cons.injEq,
        BvlSem.Value.word64.injEq, DataSem.Value.word64.injEq, ih] <;> simp

/-- A projected list of integers has exactly the corresponding DATA
number-list preimage. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "MAP_data_to_bvi_Number"]
theorem mapDataToBviNumber (xs : List Int) (ws : List DataSem.Value) :
    (xs.map DataSem.Value.number).map dataToBviValue = ws.map dataToBviValue ↔
      xs.map DataSem.Value.number = ws := by
  induction xs generalizing ws with
  | nil => cases ws <;> simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      cases w <;> simp only [List.map_cons, dataToBviValue, List.cons.injEq,
        BvlSem.Value.number.injEq, DataSem.Value.number.injEq, ih] <;> simp

/-- Projecting a list of 64-bit word values preserves each word. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_word_eq"]
theorem dataToBviWordMap (words : List (BitVec 64)) :
    (words.map DataSem.Value.word64).map dataToBviValue = words.map BvlSem.Value.word64 := by
  induction words with
  | nil => rfl
  | cons word words ih => simp only [List.map_cons, dataToBviValue, ih]

/-- Projecting unsigned word values represented as integers preserves each
value for every positive word width. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_number_eq"
  (words_as_type_indexed_bitvec)]
theorem dataToBviNumberMap {width : Nat} [NeZero width] (words : List (BitVec width)) :
    (words.map (fun word => DataSem.Value.number (Int.ofNat word.toNat))).map dataToBviValue =
      words.map (fun word => BvlSem.Value.number (Int.ofNat word.toNat)) := by
  induction words with
  | nil => rfl
  | cons word words ih => simp only [List.map_cons, dataToBviValue, ih]

end Flapjack.Compiler.Backend.BviToData
