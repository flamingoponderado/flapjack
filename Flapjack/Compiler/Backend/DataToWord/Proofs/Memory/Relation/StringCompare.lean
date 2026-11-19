module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem
public import Flapjack.Compiler.Backend.WordGcFunctions
public import Flapjack.HolArb

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

/-- Compare the two length headers before walking their byte payloads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_str_cmp_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordStrCmp {width : Nat} [NeZero width]
    (b : Bool) (a1 a2 : BitVec width) (dm : BitVec width → Bool)
    (m : BitVec width → WordLocW width) (be : Bool) (c : DataToWord.Config) :
    Option (BitVec width × BitVec width) :=
  let k := width - c.lenSize - Flapjack.wordShiftAmount width
  if dm a1 && dm a2 && wordSemIsWordLoc (m a1) && wordSemIsWordLoc (m a2) then
    let l1 := wordSemTheWord (m a1) >>> k
    let l2 := wordSemTheWord (m a2) >>> k
    if b then
      if l1 ≠ l2 then some (l1, l2)
      else wordStrCmpLoop (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        l1 l1 l1 dm m be (2 ^ width)
    else
      let len := BitVec.ofNat width (min l1.toNat l2.toNat)
      wordStrCmpLoop (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        l1 l2 len dm m be (2 ^ width)
  else none

/-- Find the first differing words. HOL pattern completion assigns `ARB` at
    the result-pair type to either unequal-length case. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "find_diff_def"
  (words_as_type_indexed_bitvec)]
noncomputable def findDiff {inputWidth : Nat} {resultWidth1 : Nat} {resultWidth2 : Nat}
    [NeZero inputWidth] [NeZero resultWidth1] [NeZero resultWidth2] :
    List (BitVec inputWidth) → List (BitVec inputWidth) →
      BitVec resultWidth1 → BitVec resultWidth2 → BitVec resultWidth1 × BitVec resultWidth2
  | [], [], r1, r2 => (r1, r2)
  | x :: xs, y :: ys, r1, r2 =>
      if x = y then findDiff xs ys r1 r2
      else (BitVec.ofNat resultWidth1 x.toNat, BitVec.ofNat resultWidth2 y.toNat)
  | _, _, _, _ => holArb _

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
