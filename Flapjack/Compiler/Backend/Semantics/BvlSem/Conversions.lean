import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyMemory

/-! Deterministic list decoders used by BVL installation. -/
namespace Flapjack.Compiler.Backend.BvlSem

/-- Decode word-valued elements, rejecting any other value constructor. -/
def wordValues : List Value → Option (List (BitVec 64))
  | [] => some []
  | .word64 word :: values => do
    let rest ← wordValues values
    pure (word :: rest)
  | _ => none

/-- Successful decoding characterizes the exact word encoding. -/
theorem wordValues_eq_some (values : List Value) (words : List (BitVec 64)) :
    wordValues values = some words ↔ values = words.map Value.word64 := by
  induction values generalizing words with
  | nil => cases words <;> simp [wordValues]
  | cons head tail ih =>
    cases head <;> cases words <;> simp_all [wordValues, Option.bind_eq_some_iff]
    exact and_comm

/-- Successful decoding characterizes the exact integer byte encoding. -/
theorem byteNumbers_eq_some (values : List Value) (bytes : List (BitVec 8)) :
    byteNumbers values = some bytes ↔ values = bytes.map (fun b => .number b.toNat) := by
  induction values generalizing bytes with
  | nil => cases bytes <;> simp [byteNumbers]
  | cons head tail ih =>
    cases head <;> cases bytes <;> simp_all [byteNumbers, Option.bind_eq_some_iff, intToByte_iff]

/-- Decode the list value used as an installation byte sequence. This
deterministic implementation remains untagged pending review against HOL's
choice operator; `valueToBytes_eq_some` characterizes its successful results. -/
def valueToBytes (value : Value) : Option (List (BitVec 8)) :=
  (valueToList value).bind byteNumbers

/-- Decode the list value used as an installation word sequence. This remains
untagged pending review against HOL's choice operator. -/
def valueToWords (value : Value) : Option (List (BitVec 64)) :=
  (valueToList value).bind wordValues

/-- The deterministic byte decoder satisfies the original choice predicate. -/
theorem valueToBytes_eq_some (value : Value) (bytes : List (BitVec 8)) :
    valueToBytes value = some bytes ↔
      valueToList value = some (bytes.map (fun b => .number b.toNat)) := by
  simp [valueToBytes, Option.bind_eq_some_iff, byteNumbers_eq_some]

/-- The deterministic word decoder satisfies the original choice predicate. -/
theorem valueToWords_eq_some (value : Value) (words : List (BitVec 64)) :
    valueToWords value = some words ↔ valueToList value = some (words.map Value.word64) := by
  simp [valueToWords, Option.bind_eq_some_iff, wordValues_eq_some]

end Flapjack.Compiler.Backend.BvlSem
