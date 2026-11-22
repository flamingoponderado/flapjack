module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefByte
public import Flapjack.HolRef

@[expose] public section

/-! Numeral-indexed unfolding equations for `last_bytes` (`last_bytes_simp`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.HolByte

/-- HOL `last_bytes_simp`, after `SUC_TO_NUMERAL_DEFN_CONV`: the zero case and
the two numeral cases `NUMERAL (BIT1 n) = 2 * n + 1` and
`NUMERAL (BIT2 n) = 2 * n + 2`. As in HOL, the `BIT1` case keeps the
unevaluated `- 1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "last_bytes_simp"
  (words_as_type_indexed_bitvec)]
theorem lastBytes_simp {width : Nat} [NeZero width] :
    (∀ (w : BitVec width) (be : Bool) (b : BitVec 8) (a : BitVec width),
      lastBytes 0 b a w be = w) ∧
    (∀ (w : BitVec width) (n : Nat) (be : Bool) (b : BitVec 8) (a : BitVec width),
      lastBytes (2 * n + 1) b a w be =
        setByte a b (lastBytes (2 * n + 1 - 1) b (a + 1#width) w be) be) ∧
    (∀ (w : BitVec width) (n : Nat) (be : Bool) (b : BitVec 8) (a : BitVec width),
      lastBytes (2 * n + 2) b a w be =
        setByte a b (lastBytes (2 * n + 1) b (a + 1#width) w be) be) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w be b a
    rw [lastBytes, if_pos rfl]
  · intro w n be b a
    rw [lastBytes, if_neg (by omega)]
  · intro w n be b a
    rw [lastBytes, if_neg (by omega), show 2 * n + 2 - 1 = 2 * n + 1 by omega]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
