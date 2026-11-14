module

public import Flapjack.Pancake.Semantics.CrepSem.Eval
public import Flapjack.RiscV.PanMemory

@[expose] public section


/-!
# Crep word/byte codec helpers

This module retains the little-endian byte projection `crepClockWordToBytes`
(HOL `word_to_bytes w F`) and its inverse `crepClockWordOfBytes` (HOL
`word_of_bytes F 0w`) over `BitVec width`/`UInt8`. They are shared by the exact
`CrepSemHOLState` evaluator in `CrepSem/EvaluateHOL.lean` and by the ShMem byte
bridges.

The restricted `CrepClockProg`/`CrepHolState` total evaluator and its clause
lemmas were retired once every test replayed its rows on the reviewed exact
`CrepSemHOLState`/`CrepProgHOL` carriers; HOL
`evaluate_nested_decs_load_globals` is mapped by the tagged
`evaluateNestedDecsLoadGlobalsCrepHOL`.
-/

namespace Flapjack

/-- Little-endian byte projection used by HOL `word_to_bytes w F` at a fixed
    positive word width. HOL's `F` selects increasing-address, least
    significant byte first. -/
def crepClockWordToBytes {width : Nat} (word : BitVec width) : List UInt8 :=
  (List.range (width / 8)).map fun index =>
    UInt8.ofNat ((word.toNat / 2 ^ (8 * index)) % 256)

/-- Accumulator for the recursive HOL `word_of_bytes` mirror `crepClockWordOfBytes`.

Installs bytes at increasing word addresses starting from word address `a`, with
`byte_index = (w2n a) MOD (dimindex DIV 8)` exactly as HOL `byteTheory.set_byte`
does. Because the recursion is applied outermost first (the word is built from
the list tail inward), the byte at the smallest address reaching a given byte
slot wins when the address wraps, matching HOL `word_of_bytes`'s `set_byte a b
(word_of_bytes be (a+1w) bs)` recursion. Doing the address arithmetic at the
`BitVec` word carrier makes the address wrap modulo `dimindex` faithful for
arbitrary positive widths, not only multiples of eight. All intermediate values
stay below `2^width`, so the final `BitVec.ofNat` truncation is the identity. -/
def crepClockWordOfBytesAux {width : Nat} : Nat → List UInt8 → Nat
  | _, [] => 0
  | a, byte :: rest =>
      let byteIndex := (BitVec.ofNat width a).toNat % (width / 8)
      let offset := 256 ^ byteIndex
      let block := offset * 256
      let value := crepClockWordOfBytesAux (width := width) (a + 1) rest
      value % offset + byte.toNat * offset + value / block * block

/-- HOL `word_of_bytes F 0w` over the same fixed-width word carrier, as the exact
recursive `set_byte`-fold from word address `0w`. Bytes are installed in
increasing-address order, so the earliest byte at each byte slot is the one that
survives; `BitVec.ofNat` supplies HOL word truncation. This matches HOL for all
positive widths (in particular the non-multiples of eight), where the previous
fold-left formulation kept the last wrapped byte instead. -/
def crepClockWordOfBytes {width : Nat} (bytes : List UInt8) : BitVec width :=
  BitVec.ofNat width (crepClockWordOfBytesAux (width := width) 0 bytes)

end Flapjack
