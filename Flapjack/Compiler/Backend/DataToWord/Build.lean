import Flapjack.Compiler.Backend.DataLang.Syntax
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Misc.Sptree

/-! Word layouts for closure constant parts. This executable path covers the
32-bit and 64-bit targets. Other widths are rejected until their byte packing
and word behavior have been reviewed. -/
namespace Flapjack.Compiler.Backend.DataToWord.Build
open Flapjack.Basis.Pure.MlString

abbrev Value (width : Nat) := Bool × BitVec width

private def ptrBits {width : Nat} (conf : Config) (tag len : Nat) : BitVec width :=
  let field (n bits shift : Nat) : BitVec width :=
    let maximum := 2 ^ bits - 1
    BitVec.ofNat width ((if n < maximum then n else maximum) * 2 ^ shift)
  field tag conf.tagBits (1 + conf.lenBits) ||| field len conf.lenBits 1

private def digits {width : Nat} (fuel : Nat) (n : Nat) : List (BitVec width) :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n == 0 then [] else
      BitVec.ofNat width (n % (2 ^ width)) :: digits fuel (n / (2 ^ width))

private def pointer {width : Nat} [NeZero width] (conf : Config) (offset : BitVec width) : BitVec width :=
  (offset <<< (shiftLength conf - wordShiftAmount width)) ||| 1

private def byteWord {width : Nat} (be : Bool) (bs : List HolChar) : BitVec width :=
  let k := width / 8
  (List.range k).foldl (fun word i =>
    let b := ((bs[i]?).getD 0).toNat
    let shift := 8 * (if be then k - 1 - i else i)
    word ||| (BitVec.ofNat width b <<< shift)) 0

private def bytesWords {width : Nat} (be : Bool) (bytes : List HolChar) (count : Nat) : List (BitVec width) :=
  (List.range count).map fun i => byteWord be (bytes.drop (i * (width / 8)))

/-- Lower one closure constant part. The sparse map supplies preceding
constant values; the Boolean indicates a pointer relative to the allocation base.
This is executable infrastructure pending cross-language source review. -/
def partWords {width : Nat} [NeZero width] (conf : Config) (memory : Spt (Value width))
    (part : ClosLang.ConstPart) (offset : BitVec width) : Option (Value width × List (Value width)) := do
  if width != 32 && width != 64 then none else
  match part with
  | .int i =>
    let bound : Int := Int.ofNat (2 ^ width / 8)
    if -bound ≤ i ∧ i < bound then
      let w := BitVec.ofNat width (4 * i.natAbs)
      some ((false, if i < 0 then -w else w), [])
    else
      let ws := digits (width := width) (i.natAbs + 1) i.natAbs
      let header ← encodeHeader (width := width) conf (if i < 0 then 7 else 3) ws.length
      some ((true, pointer conf offset), (header :: ws).map (false, ·))
  | .con tag refs =>
    if refs.isEmpty then
      if tag < 2 ^ width / 16 then some ((false, BitVec.ofNat width (16 * tag + 2)), []) else none
    else
      let header ← encodeHeader (width := width) conf (4 * tag) refs.length
      let addr := (offset <<< (shiftLength conf - wordShiftAmount width)) + (ptrBits conf tag refs.length ||| 1)
      let fields := refs.map fun n => (sptLookup n memory).getD (false, 0)
      some ((true, addr), (false, header) :: fields)
  | .w64 word =>
    let ws : List (BitVec width) := if width < 64 then
      [BitVec.ofNat width (word.toNat / 2 ^ 32), BitVec.ofNat width word.toNat]
      else [BitVec.ofNat width word.toNat]
    let header ← encodeHeader (width := width) conf 3 ws.length
    some ((true, pointer conf offset), (header :: ws).map (false, ·))
  | .str s =>
    let bs := s.explode
    let n := bs.length
    let k := if width == 32 then n / 4 + 1 else n / 8 + 1
    if !(k < 2 ^ (width - 4) ∧ k < 2 ^ conf.lenSize) then none else
    let header : BitVec width :=
      (BitVec.ofNat width (n + (if width == 32 then 4 else 8)) <<<
        (width - (if width == 32 then 2 else 3) - conf.lenSize)) ||| 7
    let ws := header :: bytesWords conf.be bs k
    some ((true, pointer conf offset), ws.map (false, ·))

/-- Convert all constant parts in source order, preserving earlier references
and the exact emitted word order. -/
def partsWords {width : Nat} [NeZero width] (conf : Config)
    (parts : List ClosLang.ConstPart) : Option (Value width × List (Value width)) := do
  let (_, memory, _, chunks) ← parts.foldlM (fun (i, memory, offset, chunks) p => do
    let (value, ws) ← partWords conf memory p offset
    let offset := offset + BitVec.ofNat width ((width / 8) * ws.length)
    pure (i + 1, sptInsert i value memory, offset, ws :: chunks))
      (0, (.ln : Spt (Value width)), (0 : BitVec width), ([] : List (List (Value width))))
  let last := (sptLookup (parts.length - 1) memory).getD (false, 0)
  some (last, chunks.reverse.flatten)

end Flapjack.Compiler.Backend.DataToWord.Build
