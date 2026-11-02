import Flapjack.CakeParser.ToSexp
import Mathlib.Tactic.IntervalCases

/-! Round-trip properties for CakeML's S-expression character escaping. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000 in
private theorem decode_encoded_byte (c : HolChar) (tail : List HolChar) :
    decodeControl (ToSexp.encodeControl [c] ++ tail) =
      (decodeControl tail).map (c :: ·) := by
  have bound : c.toNat < 256 := c.isLt
  generalize h : c.toNat = n at *
  have ceq : c = BitVec.ofNat 8 n := by
    apply BitVec.eq_of_toNat_eq
    simpa [Nat.mod_eq_of_lt bound] using h
  subst c
  interval_cases n <;> simp [ToSexp.encodeControl, ToSexp.hexDigit, decodeControl, upperHex, isPrint] <;>
    rw [decodeControl.eq_def] <;> rfl

/-- Encoded control characters decode to the original byte sequence. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decode_encode_control"]
theorem decode_encode_control (xs : List HolChar) :
    decodeControl (ToSexp.encodeControl xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    have append : ToSexp.encodeControl (c :: xs) =
        ToSexp.encodeControl [c] ++ ToSexp.encodeControl xs := by simp [ToSexp.encodeControl]
    rw [append]
    rw [decode_encoded_byte, ih]
    rfl

end Flapjack.CakeParser.FromSexp
