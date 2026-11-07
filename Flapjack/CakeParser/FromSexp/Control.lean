import Flapjack.CakeParser.ToSexp
import Mathlib.Tactic.IntervalCases

/-! Round-trip properties for CakeML's S-expression character escaping. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000 in
private theorem decode_encoded_byte (c : HolChar) (tail : List HolChar) :
    decodeControl (encodeControl [c] ++ tail) =
      (decodeControl tail).map (c :: ·) := by
  have bound : c.toNat < 256 := c.isLt
  generalize h : c.toNat = n at *
  have ceq : c = BitVec.ofNat 8 n := by
    apply BitVec.eq_of_toNat_eq
    simpa [Nat.mod_eq_of_lt bound] using h
  subst c
  interval_cases n <;> simp [encodeControl, hexDigit, decodeControl, upperHex, isPrint] <;>
    rw [decodeControl.eq_def] <;> rfl

/-- Encoded control characters decode to the original byte sequence. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decode_encode_control"]
theorem decode_encode_control (xs : List HolChar) :
    decodeControl (encodeControl xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    have append : encodeControl (c :: xs) =
        encodeControl [c] ++ encodeControl xs := by simp [encodeControl]
    rw [append]
    rw [decode_encoded_byte, ih]
    rfl

/-- Encoded string S-expressions are injective. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "SEXSTR_11"]
theorem sexstr_injective (left right : List HolChar) : sexstr left = sexstr right ↔ left = right := by
  constructor
  · intro eq
    have bytes : encodeControl left = encodeControl right := Sexp.Sexp.str.inj eq
    have decoded := congrArg decodeControl bytes
    simpa only [decode_encode_control, Option.some.injEq] using decoded
  · intro eq
    subst right
    rfl

/-- Encoded strings have a distinct S-expression constructor. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "SEXSTR_distinct"]
theorem sexstr_distinct (s symbol other : List HolChar) (n : Nat) (a d : Sexp.Sexp) :
    sexstr s ≠ .sym symbol ∧ sexstr s ≠ .num n ∧ sexstr s ≠ .cons a d ∧
      (sexstr s = .str other ↔ other = encodeControl s) := by
  simp [sexstr, eq_comm]

/-- Printable bytes other than backslash need no control encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "encode_control_remove"]
theorem encode_control_remove (xs : List HolChar) :
    xs.all isPrint = true ∧ (92 : HolChar) ∉ xs → encodeControl xs = xs := by
  induction xs with
  | nil => simp [encodeControl]
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, not_or]
    rintro ⟨⟨printable, restPrintable⟩, notSlash, restNotSlash⟩
    have range : 32 ≤ x.toNat ∧ x.toNat < 127 := by simpa [isPrint] using printable
    have notSlashNat : x.toNat ≠ 92 := by
      intro equal
      apply notSlash
      apply BitVec.eq_of_toNat_eq
      simpa using equal.symm
    have step : encodeControl (x :: xs) = x :: encodeControl xs := by
      simp [encodeControl, range.1, range.2, notSlashNat]
    rw [step, ih ⟨restPrintable, restNotSlash⟩]

/-- Printable strings without backslashes are already in canonical form. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "SEXSTR_remove"]
theorem sexstr_remove (xs : List HolChar) :
    xs.all isPrint = true ∧ (92 : HolChar) ∉ xs → sexstr xs = .str xs := by
  intro h
  simp [sexstr, encode_control_remove xs h]

end Flapjack.CakeParser.FromSexp
