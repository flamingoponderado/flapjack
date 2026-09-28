import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.Semantics.LoopSem

/-!
# `wordSem` helpers shared by the Loop semantics

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml` for the
declarations the exact loopSem evaluator needs.
-/

namespace Flapjack

/-- Exact HOL `wordSem$the_words_def` (`wordSemScript.sml:297-302`):

    ```
    the_words [] = SOME []
    the_words (w::ws) = case (w, the_words ws) of
                          | SOME (Word x), SOME xs => SOME (x::xs)
                          | _ => NONE
    ```

    over the exact `word_loc` carrier `WordLocW`, HOL `'a word` rendered as
    `BitVec width`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "the_words_def"
  (words_as_type_indexed_bitvec)]
def theWords {width : Nat} [NeZero width] :
    List (Option (WordLocW width)) → Option (List (BitVec width))
  | [] => some []
  | w :: ws =>
      match w, theWords ws with
      | some (.word x), some xs => some (x :: xs)
      | _, _ => none

/-- HOL `byte$byte_index` (`src/n-bit/byteScript.sml:15-19`), HOL standard
    library, so no HOL tag:

    ```
    byte_index a be = let d = dimindex (:'a) DIV 8 in
      if be then 8 * ((d - 1) - w2n a MOD d) else 8 * (w2n a MOD d)
    ```

    Lean `Nat` `%` and truncated `-` match HOL `MOD` (including `MOD_0`) and
    `-` on `num`. -/
def byteIndexHOL {width : Nat} (address : BitVec width) (bigEndian : Bool) : Nat :=
  let d := width / 8
  if bigEndian then 8 * ((d - 1) - address.toNat % d) else 8 * (address.toNat % d)

/-- HOL `byte$get_byte` (`byteScript.sml:21-24`),
    `get_byte a w be = (w2w (w >>> byte_index a be)) : word8`, with HOL `w2w`
    as `BitVec.setWidth`.  HOL standard library, so no HOL tag. -/
def getByteHOL8 {width : Nat} (address value : BitVec width) (bigEndian : Bool) :
    BitVec 8 :=
  (value >>> byteIndexHOL address bigEndian).setWidth 8

/-- HOL `byte$set_byte` (`byteScript.sml:30-36`):

    ```
    set_byte a b w be = let i = byte_index a be in
      word_slice_alt (dimindex (:'a)) (i + 8) w || w2w b << i || word_slice_alt i 0 w
    ```

    The two `word_slice_alt` slices keep exactly the bits of `w` outside
    `[i, i + 8)`, which is `w && ~~(255w << i)`.  HOL standard library, so no
    HOL tag. -/
def setByteHOL8 {width : Nat} (address : BitVec width) (byte : BitVec 8)
    (value : BitVec width) (bigEndian : Bool) : BitVec width :=
  let i := byteIndexHOL address bigEndian
  (value &&& ~~~(BitVec.ofNat width 255 <<< i)) ||| (byte.setWidth width <<< i)

/-- HOL `byte$word_of_bytes` (`byteScript.sml:197-201`).  HOL standard
    library, so no HOL tag. -/
def wordOfBytesHOL8 {width : Nat} (bigEndian : Bool) (address : BitVec width) :
    List (BitVec 8) → BitVec width
  | [] => 0
  | b :: bs => setByteHOL8 address b (wordOfBytesHOL8 bigEndian (address + 1) bs) bigEndian

/-- Exact HOL `wordSem$mem_load_32_def` (`wordSemScript.sml:70-81`) over the
    exact `word_loc` memory carrier `BitVec width → WordLocW width`, with the
    memory domain `dm` as a `Bool` predicate. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_32_def"
  (words_as_type_indexed_bitvec)]
def memLoad32Exact {width : Nat} [NeZero width] (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (bigEndian : Bool) (address : BitVec width) :
    Option (BitVec 32) :=
  if riscvAlignedHOL 2 address then
    match memory (riscvByteAlignHOL address) with
    | .loc _ _ => none
    | .word v =>
        if domain (riscvByteAlignHOL address) then
          some (wordOfBytesHOL8 bigEndian (0 : BitVec 32)
            [getByteHOL8 address v bigEndian, getByteHOL8 (address + 1) v bigEndian,
             getByteHOL8 (address + 2) v bigEndian, getByteHOL8 (address + 3) v bigEndian])
        else none
  else none

/-- Exact HOL `wordSem$mem_store_32_def` (`wordSemScript.sml:84-98`); the HOL
    update `(byte_align w =+ Word v3) m` is the pointwise `if` update. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_32_def"
  (words_as_type_indexed_bitvec)]
def memStore32Exact {width : Nat} [NeZero width] (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (bigEndian : Bool) (address : BitVec width)
    (hw : BitVec 32) : Option (BitVec width → WordLocW width) :=
  if riscvAlignedHOL 2 address then
    match memory (riscvByteAlignHOL address) with
    | .word v =>
        if domain (riscvByteAlignHOL address) then
          let v0 := setByteHOL8 address (getByteHOL8 (0 : BitVec 32) hw bigEndian) v bigEndian
          let v1 := setByteHOL8 (address + 1) (getByteHOL8 (1 : BitVec 32) hw bigEndian) v0
            bigEndian
          let v2 := setByteHOL8 (address + 2) (getByteHOL8 (2 : BitVec 32) hw bigEndian) v1
            bigEndian
          let v3 := setByteHOL8 (address + 3) (getByteHOL8 (3 : BitVec 32) hw bigEndian) v2
            bigEndian
          some (fun a => if a = riscvByteAlignHOL address then .word v3 else memory a)
        else none
    | _ => none
  else none

/-- Exact HOL `wordSem$mem_load_byte_aux_def` (`wordSemScript.sml:159-166`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_byte_aux_def"
  (words_as_type_indexed_bitvec)]
def memLoadByteAuxExact {width : Nat} [NeZero width]
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address : BitVec width) : Option (BitVec 8) :=
  match memory (riscvByteAlignHOL address) with
  | .loc _ _ => none
  | .word v =>
      if domain (riscvByteAlignHOL address) then some (getByteHOL8 address v bigEndian)
      else none

/-- Exact HOL `wordSem$mem_store_byte_aux_def` (`wordSemScript.sml:168-175`). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_byte_aux_def"
  (words_as_type_indexed_bitvec)]
def memStoreByteAuxExact {width : Nat} [NeZero width]
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address : BitVec width) (byte : BitVec 8) :
    Option (BitVec width → WordLocW width) :=
  match memory (riscvByteAlignHOL address) with
  | .word v =>
      if domain (riscvByteAlignHOL address) then
        some (fun a => if a = riscvByteAlignHOL address then
          .word (setByteHOL8 address byte v bigEndian) else memory a)
      else none
  | _ => none

/-- Exact HOL `wordSem$write_bytearray_def` (`wordSemScript.sml:178-184`) over
    the exact `word_loc` memory: the tail is written first, the head byte is
    stored into that result with `mem_store_byte_aux`, and a failed store
    returns the original memory `m`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "write_bytearray_def"
  (words_as_type_indexed_bitvec)]
def writeBytearrayExact {width : Nat} [NeZero width] (address : BitVec width) :
    List (BitVec 8) → (BitVec width → WordLocW width) → (BitVec width → Bool) → Bool →
      BitVec width → WordLocW width
  | [], memory, _, _ => memory
  | b :: bs, memory, domain, bigEndian =>
      match memStoreByteAuxExact (writeBytearrayExact (address + 1) bs memory domain bigEndian)
          domain bigEndian address b with
      | some m => m
      | none => memory

end Flapjack
