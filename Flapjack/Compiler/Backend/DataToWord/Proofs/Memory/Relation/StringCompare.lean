module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Compare byte sequences one byte at a time, with the original clock and
independently typed result words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_str_cmp_loop_def"
  (words_as_type_indexed_bitvec)]
def wordStrCmpLoop {width : Nat} {resultWidth1 : Nat} {resultWidth2 : Nat}
    [NeZero width] [NeZero resultWidth1] [NeZero resultWidth2]
    (a1 a2 : BitVec width) (r1 : BitVec resultWidth1) (r2 : BitVec resultWidth2)
    (len : BitVec width) (dm : BitVec width → Bool) (m : BitVec width → WordLocW width)
    (be : Bool) : Nat → Option (BitVec resultWidth1 × BitVec resultWidth2)
  | 0 => none
  | ck + 1 =>
      if len = wordSemBytesInWord then some (r1, r2)
      else
        match memLoadByteAuxExact m dm be a1 with
        | none => none
        | some b1 =>
          match memLoadByteAuxExact m dm be a2 with
          | none => none
          | some b2 =>
            if b1 = b2 then wordStrCmpLoop (a1 + 1) (a2 + 1) r1 r2 (len - 1) dm m be ck
            else some (BitVec.ofNat resultWidth1 b1.toNat, BitVec.ofNat resultWidth2 b2.toNat)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
