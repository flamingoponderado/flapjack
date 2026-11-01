import Flapjack.Compiler.Backend.Semantics.DataSem.Value
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions

/-! Data-language installation value decoders. -/
namespace Flapjack.Compiler.Backend.DataSem

/-- Decode integer-valued bytes. -/
def byteNumbers : List Value → Option (List (BitVec 8))
  | [] => some []
  | .number n :: rest => do
      let byte ← ClosSem.intToByte n
      let bytes ← byteNumbers rest
      pure (byte :: bytes)
  | _ => none

/-- Decode 64-bit word-valued elements. -/
def wordValues : List Value → Option (List (BitVec 64))
  | [] => some []
  | .word64 word :: rest => do
      let words ← wordValues rest
      pure (word :: words)
  | _ => none

/-- The byte decoder's exact successful-input characterization. -/
theorem byteNumbers_eq_some (values : List Value) (bytes : List (BitVec 8)) :
    byteNumbers values = some bytes ↔ values = bytes.map (fun b => .number b.toNat) := by
  induction values generalizing bytes with
  | nil => cases bytes <;> simp [byteNumbers]
  | cons head tail ih =>
    cases head <;> cases bytes <;> simp_all [byteNumbers, Option.bind_eq_some_iff, BvlSem.intToByte_iff]

/-- The word decoder's exact successful-input characterization. -/
theorem wordValues_eq_some (values : List Value) (words : List (BitVec 64)) :
    wordValues values = some words ↔ values = words.map Value.word64 := by
  induction values generalizing words with
  | nil => cases words <;> simp [wordValues]
  | cons head tail ih =>
    cases head <;> cases words <;> simp_all [wordValues, Option.bind_eq_some_iff]
    exact and_comm

/-- Decode an installation byte list. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v_to_bytes_def"]
def valueToBytes (value : Value) : Option (List (BitVec 8)) :=
  (valueToList value).bind byteNumbers

/-- Decode an installation word list. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v_to_words_def"]
def valueToWords (value : Value) : Option (List (BitVec 64)) :=
  (valueToList value).bind wordValues

/-- Successful byte decoding gives precisely the source encoding. -/
theorem valueToBytes_eq_some (value : Value) (bytes : List (BitVec 8)) :
    valueToBytes value = some bytes ↔
      valueToList value = some (bytes.map (fun b => .number b.toNat)) := by
  simp [valueToBytes, Option.bind_eq_some_iff, byteNumbers_eq_some]

/-- Successful word decoding gives precisely the source encoding. -/
theorem valueToWords_eq_some (value : Value) (words : List (BitVec 64)) :
    valueToWords value = some words ↔ valueToList value = some (words.map Value.word64) := by
  simp [valueToWords, Option.bind_eq_some_iff, wordValues_eq_some]

/-- The executable byte decoder equals the guarded HOL choice. -/
theorem valueToBytes_eq_holChoice (value : Value) :
    valueToBytes value = Flapjack.holOptionSome
      (fun bytes : List (BitVec 8) => valueToList value = some (bytes.map (fun b => .number b.toNat))) := by
  exact BvlSem.option_eq_holChoice _ _ (valueToBytes_eq_some value)

/-- The executable word decoder equals the guarded HOL choice. -/
theorem valueToWords_eq_holChoice (value : Value) :
    valueToWords value = Flapjack.holOptionSome
      (fun words : List (BitVec 64) => valueToList value = some (words.map Value.word64)) := by
  exact BvlSem.option_eq_holChoice _ _ (valueToWords_eq_some value)

end Flapjack.Compiler.Backend.DataSem
