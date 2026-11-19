module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WriteBytes
public import Flapjack.Byte.BytesToWordSame

@[expose] public section

/-! The packed-word change needed by the byte-array heap update. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

/-- Flapjack proof infrastructure for `heap_in_memory_store_UpdateByte`:
changing one input byte modifies precisely its containing packed word, while
all other words are unchanged. The byte index is decomposed into a word index
and its in-word remainder, as in the HOL proof. -/
theorem writeBytes_setByte {width : Nat} [NeZero width] (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be : Bool) (j r : Nat) (byte : BitVec 8) (good : goodDimindex width)
    (rbound : r < width / 8) (ibound : j * (width / 8) + r < bytes.length) :
    writeBytes (bytes.set (j * (width / 8) + r) byte) words be =
      (writeBytes bytes words be).modify j (fun word => setByte (BitVec.ofNat width r) byte word be) := by
  induction words generalizing bytes j with
  | nil => simp [writeBytes]
  | cons word words ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add] at ibound ⊢
      simp only [writeBytes, List.modify_zero_cons]
      have change := bytesToWord_setByte_aux (width / 8) 0 bytes word be r byte good (by omega) rbound ibound
      simp only [Nat.zero_add] at change
      rw [List.drop_set_of_lt rbound]
      congr 1
      simpa using change.symm
    | succ j =>
      simp only [Nat.add_mul, Nat.one_mul] at ibound ⊢
      have pos : 0 < width / 8 := by rcases good with h | h <;> subst width <;> decide
      have past : width / 8 ≤ j * (width / 8) + width / 8 + r := by omega
      have same : bytesToWord (width / 8) 0 (bytes.set (j * (width / 8) + width / 8 + r) byte) word be =
          bytesToWord (width / 8) 0 bytes word be := by
        apply bytesToWord_same
        intro n hn
        refine ⟨by simpa using (show n < bytes.length by omega), by omega, ?_⟩
        apply List.getElem_set_ne
        omega
      simp only [writeBytes, List.modify_succ_cons]
      rw [same, List.drop_set, if_neg (by omega)]
      have tailBound : j * (width / 8) + r < (bytes.drop (width / 8)).length := by simp; omega
      have sub : j * (width / 8) + width / 8 + r - width / 8 = j * (width / 8) + r := by omega
      rw [sub, ih _ j tailBound]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
