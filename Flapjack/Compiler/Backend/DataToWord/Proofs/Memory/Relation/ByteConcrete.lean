module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeaderDecode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- A correctly bounded byte cell is represented by its header and packed
payload. This Flapjack helper supplies the concrete fresh-byte allocation proof. -/
theorem wordElBytesEq {width : Nat} [NeZero width] (c : DataToWord.Config)
    (addr : BitVec width) (bytes : List (BitVec 8)) (be flag : Bool)
    (good : goodDimindex width) (config : c.lenSize + 7 < width)
    (countBound : bytes.length / (width / 8) + 1 < 2 ^ (width - 4))
    (lenBound : bytes.length / (width / 8) + 1 < 2 ^ c.lenSize) :
    wordEl addr (bytesRep be flag bytes (List.replicate (bytes.length / (width / 8) + 1) (0 : BitVec width))) c =
      Misc.wordList addr (.word (makeByteHeader c flag bytes.length) ::
        (writeBytes bytes (List.replicate (bytes.length / (width / 8) + 1) (0 : BitVec width)) be).map .word) := by
  let count := bytes.length / (width / 8) + 1
  have lengthBound : bytes.length + 2 ^ wordShiftAmount width < 2 ^ (c.lenSize + wordShiftAmount width) := by
    rcases good with hw | hw <;> subst width <;>
      simp only [wordShiftAmount, Nat.pow_add] at * <;> norm_num at * <;> omega
  have decodedNat := decodeLength_makeByteHeader_exact c flag bytes.length ⟨good, config, lengthBound⟩
  have countWidth : count < 2 ^ width := by
    apply Nat.lt_of_lt_of_le countBound
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have decoded : WordGcFunctions.decodeLength c (makeByteHeader c flag bytes.length) = BitVec.ofNat width count := by
    apply BitVec.eq_of_toNat_eq
    simpa [count, Nat.mod_eq_of_lt countWidth] using decodedNat
  have payloadBound : bytes.length + (if width = 32 then 4 else 8) <
      2 ^ (c.lenSize + if width = 32 then 2 else 3) := by
    rcases good with hw | hw <;> subst width <;> simpa [wordShiftAmount] using lengthBound
  funext heap
  apply propext
  simp only [wordEl, bytesRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map,
    writeBytes_wordCount, List.length_replicate]
  simp [decoded, count, countBound, payloadBound, StackRemove.WordListExists.starCond]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
