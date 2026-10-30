import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyMemory
import Flapjack.Misc.Option
import Flapjack.HolRef

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

/-- Decode the list value used as an installation byte sequence. The
deterministic implementation equals HOL's choice expression, as established
by `valueToBytes_eq_holChoice` below. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "v_to_bytes_def"]
def valueToBytes (value : Value) : Option (List (BitVec 8)) :=
  (valueToList value).bind byteNumbers

/-- Decode the list value used as an installation word sequence. The
deterministic implementation equals HOL's choice expression, as established
by `valueToWords_eq_holChoice` below. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "v_to_words_def"]
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

/-- A deterministic option characterized by a predicate equals HOL's guarded
choice of a witness of that predicate. -/
theorem option_eq_holChoice {α : Type} (decoded : Option α) (P : α → Prop)
    (characterization : ∀ x, decoded = some x ↔ P x) : decoded = Flapjack.holOptionSome P := by
  cases choice : Flapjack.holOptionSome P with
  | none =>
    cases result : decoded with
    | none => rfl
    | some value =>
      have valid := (characterization value).mp result
      exact False.elim (Flapjack.holOptionSome_none choice value valid)
  | some value =>
    exact (characterization value).mpr (Flapjack.holOptionSome_some choice)

/-- The executable byte decoder equals the original HOL choice expression. -/
theorem valueToBytes_eq_holChoice (value : Value) :
    valueToBytes value = Flapjack.holOptionSome
      (fun bytes : List (BitVec 8) => valueToList value = some (bytes.map (fun b => .number b.toNat))) := by
  exact option_eq_holChoice _ _ (valueToBytes_eq_some value)

/-- The executable word decoder equals the original HOL choice expression. -/
theorem valueToWords_eq_holChoice (value : Value) :
    valueToWords value = Flapjack.holOptionSome
      (fun words : List (BitVec 64) => valueToList value = some (words.map Value.word64)) := by
  exact option_eq_holChoice _ _ (valueToWords_eq_some value)

end Flapjack.Compiler.Backend.BvlSem
