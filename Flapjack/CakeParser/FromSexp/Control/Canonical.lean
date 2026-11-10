module

public import Flapjack.CakeParser.FromSexp.Control

@[expose] public section

/-! Canonical control escaping for successfully decoded S-expressions. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.Basis.Pure.MlString

private theorem upperHex_spec (c : HolChar) (n : Nat) (h : upperHex c = some n) :
    n < 16 ∧ hexDigit n = c := by
  simp only [upperHex, Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  next digits =>
    simp only [Option.some.injEq] at h
    subst n
    constructor
    · omega
    · apply BitVec.eq_of_toNat_eq
      simp only [hexDigit, BitVec.toNat_ofNat]
      have below : c.toNat < 256 := c.isLt
      have d : c.toNat - 48 < 10 := by omega
      simp only [d, ↓reduceIte]
      omega
  next notDigits =>
    split at h
    next letters =>
      simp only [Option.some.injEq] at h
      subst n
      constructor
      · omega
      · apply BitVec.eq_of_toNat_eq
        simp only [hexDigit, BitVec.toNat_ofNat]
        have below : c.toNat < 256 := c.isLt
        have d : ¬ c.toNat - 65 + 10 < 10 := by omega
        simp only [d, ↓reduceIte]
        omega
    next _ => contradiction

/-- Successful decoding accepts only the canonical control encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "encode_decode_control"]
theorem encode_decode_control (xs r : List HolChar) (h : decodeControl xs = some r) :
    xs = encodeControl r := by
  cases xs with
  | nil =>
    simp [decodeControl] at h
    subst r
    rfl
  | cons c cs =>
    rw [decodeControl.eq_def] at h
    by_cases slash : c.toNat = 92
    · simp only [slash, beq_self_eq_true, ↓reduceIte] at h
      cases cs with
      | nil => simp at h
      | cons d ds =>
        by_cases double : d.toNat = 92
        · simp only [double, beq_self_eq_true, ↓reduceIte] at h
          cases hd : decodeControl ds with
          | none => simp [hd] at h
          | some rest =>
            simp only [hd, Option.map_some, Option.some.injEq] at h
            subst r
            have recursiveEq := encode_decode_control ds rest hd
            have cd : c = d := BitVec.eq_of_toNat_eq (slash.trans double.symm)
            subst d
            simpa [encodeControl, slash] using congrArg (fun t => c :: c :: t) recursiveEq
        · simp only [double, beq_iff_eq, ↓reduceIte] at h
          cases ds with
          | nil => simp at h
          | cons e tail =>
            cases hi : upperHex d with
            | none => simp [hi] at h
            | some a =>
              cases lo : upperHex e with
              | none => simp [hi, lo] at h
              | some b =>
                simp only [hi, lo] at h
                change (if isPrint (BitVec.ofNat 8 (16 * a + b)) then none else
                  (decodeControl tail).map (BitVec.ofNat 8 (16 * a + b) :: ·)) = some r at h
                by_cases printable : isPrint (BitVec.ofNat 8 (16 * a + b)) = true
                · simp [printable] at h
                · simp only [printable, Bool.false_eq_true, ↓reduceIte] at h
                  cases ht : decodeControl tail with
                  | none => simp [ht] at h
                  | some rest =>
                    simp only [ht, Option.map_some, Option.some.injEq] at h
                    subst r
                    have recursiveEq := encode_decode_control tail rest ht
                    obtain ⟨aBound, dEq⟩ := upperHex_spec d a hi
                    obtain ⟨bBound, eEq⟩ := upperHex_spec e b lo
                    have valueBound : 16 * a + b < 256 := by omega
                    have byteNat : (BitVec.ofNat 8 (16 * a + b)).toNat = 16 * a + b := by
                      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueBound]
                    have notSlash : (BitVec.ofNat 8 (16 * a + b)).toNat ≠ 92 := by
                      intro eq
                      have : isPrint (BitVec.ofNat 8 (16 * a + b)) = true := by simp [isPrint, eq]
                      exact printable this
                    have first : BitVec.ofNat 8 92 = c := by
                      apply BitVec.eq_of_toNat_eq
                      simp [slash]
                    have hexHigh : (16 * a + b) / 16 = a := by omega
                    have hexLow : (16 * a + b) % 16 = b := by omega
                    have notPrint : ¬ (32 ≤ 16 * a + b ∧ 16 * a + b < 127) := by
                      simpa [isPrint, byteNat] using printable
                    have notSlashNat : 16 * a + b ≠ 92 := by simpa [byteNat] using notSlash
                    have encodedHead : encodeControl [BitVec.ofNat 8 (16 * a + b)] = [c, d, e] := by
                      simp [encodeControl, byteNat, notSlashNat, notPrint, hexHigh, hexLow, dEq, eEq, first]
                    have append : encodeControl (BitVec.ofNat 8 (16 * a + b) :: rest) =
                        encodeControl [BitVec.ofNat 8 (16 * a + b)] ++ encodeControl rest := by
                      simp [encodeControl]
                    rw [append, encodedHead, ← recursiveEq]
                    rfl
    · simp only [slash, beq_iff_eq, ↓reduceIte] at h
      by_cases printable : isPrint c = true
      · simp only [printable, ↓reduceIte] at h
        cases hd : decodeControl cs with
        | none => simp [hd] at h
        | some rest =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst r
          have recursiveEq := encode_decode_control cs rest hd
          have range : 32 ≤ c.toNat ∧ c.toNat < 127 := by
            simpa [isPrint] using printable
          simpa [encodeControl, slash, range.1, range.2] using congrArg (List.cons c) recursiveEq
      · simp [printable] at h
termination_by xs.length

end Flapjack.CakeParser.FromSexp
