module

public import Flapjack.Byte.BytesToWordSame
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WriteBytes
public import Mathlib.Tactic
@[expose] public section

/-! Bounded agreement for byte packing. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.HolByte Flapjack.Compiler.Backend.DataToWord

/-- Byte inputs agreeing throughout the capacity of the word list pack identically.
The bounds provide the proofs required by Lean’s indexed list notation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytes_same"
  (words_as_type_indexed_bitvec)]
theorem writeBytes_same {width : Nat} [NeZero width] (ws : List (BitVec width))
    (first second : List (BitVec 8)) (be : Bool)
    (h : ∀ n, n < ws.length * (width / 8) →
      ∃ (h1 : n < first.length) (h2 : n < second.length), first[n] = second[n]) :
    writeBytes first ws be = writeBytes second ws be := by
  induction ws generalizing first second with
  | nil => rfl
  | cons word rest ih =>
    have headH : ∀ n, n < width / 8 →
        ∃ (h1 : n < first.length) (h2 : n < second.length), first[n] = second[n] := by
      intro n hn
      apply h n
      simp only [List.length_cons, Nat.succ_mul]
      omega
    have headEq := bytesToWord_same (width / 8) 0 first word be second headH
    have tailH : ∀ n, n < rest.length * (width / 8) →
        ∃ (h1 : n < (first.drop (width / 8)).length)
          (h2 : n < (second.drop (width / 8)).length),
            (first.drop (width / 8))[n] = (second.drop (width / 8))[n] := by
      intro n hn
      obtain ⟨h1, h2, eq⟩ := h (n + width / 8) (by simp only [List.length_cons, Nat.succ_mul]; omega)
      refine ⟨by simp; omega, by simp; omega, ?_⟩
      simpa [List.getElem_drop, Nat.add_comm] using eq
    simp only [writeBytes, headEq, List.cons.injEq, true_and]
    exact ih _ _ tailH

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
