module

public import Flapjack.Compiler.Backend.DataToWord.Build

@[expose] public section

/-! Proof-side constant builders used by the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- Build a part as word locations, following the memory proof definition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "build_part_words_def"
  (words_as_type_indexed_bitvec)]
def buildPartWords {width : Nat} [NeZero width] (conf : Config) (memory : Nat → WordLocW width)
    (part : ClosLang.ConstPart) (offset : BitVec width) : Option (WordLocW width × List (WordLocW width)) := do
  match part with
  | .int i =>
    if smallInt width i then some (.word (smallnum i), [])
    else
      let (sign, words) := Misc.Multiword.i2mw (width := width) i
      let signWord : BitVec width := if sign then 1 else 0
      let tag := ((signWord <<< 2) ||| (3 : BitVec width)).toNat
      let header ← encodeHeader conf tag words.length
      some (Build.makePtr conf offset (0 : BitVec width) words.length, (header :: words).map .word)
  | .con tag refs =>
    if refs.isEmpty then
      if tag < 2 ^ width / 16 then some (.word (BitVec.ofNat width (16 * tag + 2)), []) else none
    else
      let header ← encodeHeader conf (4 * tag) refs.length
      some (Build.makeConsPtr conf offset tag refs.length, .word header :: refs.map memory)
  | .w64 word =>
    let words : List (BitVec width) := if width < 64 then
      [BitVec.ofNat width (word.toNat / 2 ^ 32), BitVec.ofNat width (word.toNat % 2 ^ 32)]
      else [BitVec.ofNat width word.toNat]
    let header ← encodeHeader conf 3 words.length
    some (Build.makePtr conf offset (0 : BitVec width) words.length, (header :: words).map .word)
  | .str text =>
    let bytes := text.explode
    let n := bytes.length
    let header := makeByteHeader (width := width) conf true n
    let count := Build.byteLen width n
    let words := writeBytes bytes (List.replicate count 0) conf.be
    if count < 2 ^ (width - 4) ∧ count < 2 ^ conf.lenSize then
      some (Build.makePtr conf offset (0 : BitVec width) count, (header :: words).map .word)
    else none

/-- Build all parts while threading the value function and byte offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "build_words_def"
  (words_as_type_indexed_bitvec)]
def buildWords {width : Nat} [NeZero width] (conf : Config) (memory : Nat → WordLocW width)
    (index : Nat) : List ClosLang.ConstPart → BitVec width → Option (WordLocW width × List (WordLocW width))
  | [], _ => some (memory (index - 1), [])
  | part :: parts, offset => do
      let (value, words) ← buildPartWords conf memory part offset
      let (result, rest) ← buildWords conf (fun key => if key = index then value else memory key)
        (index + 1) parts (offset + wordSemBytesInWord * BitVec.ofNat width words.length)
      some (result, words ++ rest)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
