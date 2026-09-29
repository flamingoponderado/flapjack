import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem
import Flapjack.Misc.GoodDimindex

/-!
# Exact `TAKE_1_word_to_bytes` byte-codec support

Counterpart of `cakeml/pancake/proofs/loop_to_wordProofScript.sml:1449-1452`.
The source theorem is a byte-codec identity used by the `Arith` case of
`compile_correct`:

```
Theorem TAKE_1_word_to_bytes:
  good_dimindex(:'a) ⇒ TAKE 1 (word_to_bytes (w:'a word) F) = [get_byte 0w w F]
```

The HOL standard-library byte helpers are outside the CakeML submodule and are
rendered by the repository's reviewed untagged carriers, exactly as in the
`wordSem` shared-memory ports (`Flapjack/Compiler/Backend/Semantics/WordSem/ShMem.lean`):
`word_to_bytes` is `panWordToBytesHOL` (`List (BitVec 8)`) and `get_byte` is
`getByteHOL8` (`BitVec 8`). HOL `good_dimindex (:α)` is the tagged `goodDimindex`
predicate on the word width. The word-dimension translation is the reviewed
type-indexed `'a word` -> positive-width `BitVec width` one.
-/

namespace Flapjack

/-- Exact HOL `TAKE_1_word_to_bytes`
    (`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1449-1451`):

    ```
    good_dimindex(:'a) ⇒ TAKE 1 (word_to_bytes (w:'a word) F) = [get_byte 0w w F]
    ```

    The sole side condition is HOL `good_dimindex (:α)` (rendered `goodDimindex`),
    not a strengthened positivity premise. `word_to_bytes` and `get_byte` are the
    reviewed untagged standard-library renderings `panWordToBytesHOL` /
    `getByteHOL8`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "TAKE_1_word_to_bytes"
  (words_as_type_indexed_bitvec)]
theorem takeOneWordToBytesHOL {width : Nat} [NeZero width] (w : RiscV.Word width)
    (h : goodDimindex width) :
    (panWordToBytesHOL w false).take 1 = [getByteHOL8 0 w false] := by
  have hle : 1 ≤ width / 8 := by rcases h with h | h <;> omega
  unfold panWordToBytesHOL
  have htake : (List.map (fun index => BitVec.ofNat 8
      (panGetByteHOL (BitVec.ofNat width index) w false).toNat)
      (List.range (width / 8))).take 1
      = [BitVec.ofNat 8
          (panGetByteHOL (BitVec.ofNat width 0) w false).toNat] := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width / 8 ≠ 0)
    rw [hm]
    rw [List.range_eq_range', List.range'_succ]
    simp
  rw [htake]
  congr 1
  simp only [getByteHOL8, panGetByteHOL, byteIndexHOL, Bool.false_eq_true, if_false,
    BitVec.ofNat_eq_ofNat, Nat.zero_mod, Nat.pow_zero, Nat.div_one, Nat.mul_zero,
    BitVec.toNat_ofNat, UInt8.ofNat, UInt8.toNat]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

end Flapjack
