module

public import Init.Data.BitVec.Lemmas
public import Init.Data.List.Lemmas
public import Init.Data.Option.Lemmas

@[expose] public section

/-!
# Generic byte-list decoding facts

The BVL and closure semantics both decode value lists as byte lists and then as
natural numbers. This module states the shared natural-number characterization
for any decoder with the first-match byte-list characterization.
-/

namespace Flapjack

/-- Successful natural-number decoding of a byte-list decoder is equivalent to
the encoded value list plus the byte bound on every element. -/
theorem byteNaturalValues_eq_some_generic {α : Type} (mk : Nat → α)
    (decode : List α → Option (List (BitVec 8)))
    (decode_eq : ∀ values bytes, decode values = some bytes ↔
      values = bytes.map (fun b => mk b.toNat))
    (values : List α) (numbers : List Nat) :
    (decode values).map (List.map BitVec.toNat) = some numbers ↔
      values = numbers.map mk ∧ ∀ n ∈ numbers, n < 256 := by
  simp only [Option.map_eq_some_iff, decode_eq]
  constructor
  · rintro ⟨bytes, encoded, rfl⟩
    constructor
    · simpa [List.map_map, Function.comp_def] using encoded
    · intro n member
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
      simpa using byte.isLt
  · rintro ⟨encoded, bound⟩
    let bytes : List (BitVec 8) := numbers.map (BitVec.ofNat 8)
    have roundtrip : bytes.map BitVec.toNat = numbers := by
      simp only [bytes, List.map_map]
      conv =>
        rhs
        rw [← List.map_id numbers]
      apply List.map_congr_left
      intro n member
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound n member)]
    refine ⟨bytes, ?_, roundtrip⟩
    have mapped : bytes.map (fun b => mk b.toNat) = numbers.map mk := by
      rw [← roundtrip]
      simp [List.map_map, Function.comp_def]
    exact encoded.trans mapped.symm

end Flapjack
