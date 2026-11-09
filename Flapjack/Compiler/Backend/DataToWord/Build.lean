module

public import Flapjack.Compiler.Backend.DataLang.Syntax
public import Flapjack.Compiler.Backend.DataToWord.Header
public import Flapjack.Compiler.Backend.DataToWord.Numbers
public import Flapjack.Compiler.Backend.DataToWord.Bytes
public import Flapjack.Misc.Multiword
public import Flapjack.Compiler.Backend.BackendCommon
public import Flapjack.Misc.Sptree

@[expose] public section

/-! Word and location layouts for closure constant parts. -/
namespace Flapjack.Compiler.Backend.DataToWord.Build
open Flapjack.Basis.Pure.MlString

abbrev Value (width : Nat) [NeZero width] := Bool × WordLocW width

/-- Extract a word, returning zero for a location. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "get_Word_def"
  (words_as_type_indexed_bitvec)]
def getWord {width : Nat} [NeZero width] : WordLocW width → BitVec width
  | .word w => w
  | .loc _ _ => 0

/-- Look up a previously built constant, defaulting to the zero word. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "lookup_mem_def"
  (words_as_type_indexed_bitvec)]
def lookupMem {width : Nat} [NeZero width] (memory : Spt (Bool × WordLocW width))
    (index : Nat) : Bool × WordLocW width :=
  (sptLookup index memory).getD (false, .word 0)

/-- Collect leading word values, leaving the first location and its suffix. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "getWords_def"
  (words_as_type_indexed_bitvec)]
def getWords {α : Type} {width : Nat} [NeZero width] :
    List (α × WordLocW width) → List (α × BitVec width) →
      List (α × BitVec width) × List (α × WordLocW width)
  | [], aux => (aux.reverse, [])
  | (b, .word w) :: rest, aux => getWords rest ((b, w) :: aux)
  | v :: rest, aux => (aux.reverse, v :: rest)

/-- The termination argument for `storeAnyConsts`; HOL proves this bound
inside the termination proof rather than declaring it separately. -/
theorem getWordsRestLength {α : Type} {width : Nat} [NeZero width]
    (values : List (α × WordLocW width)) (aux : List (α × BitVec width)) :
    (getWords values aux).2.length ≤ values.length := by
  induction values generalizing aux with
  | nil => simp [getWords]
  | cons value rest ih =>
    obtain ⟨b, value⟩ := value
    cases value with
    | word w =>
      simpa [getWords] using Nat.le_trans (ih ((b, w) :: aux)) (Nat.le_succ rest.length)
    | loc block offset => simp [getWords]

/-- Number of words allocated for a byte string, including its terminator. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "byte_len_def"
  (word_dimension_as_width := width)]
def byteLen (width : Nat) [NeZero width] (numBytes : Nat) : Nat :=
  if width = 32 then numBytes / 4 + 1 else numBytes / 8 + 1

/-- Construct the pointer to a constant at an offset from the allocation base. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "make_ptr_def"
  (words_as_type_indexed_bitvec)]
def makePtr {α β : Type} {width : Nat} [NeZero width] (conf : Config) (offset : BitVec width)
    (_tag : α) (_length : β) : WordLocW width :=
  .word ((offset <<< (shiftLength conf - wordShiftAmount width)) ||| 1)

/-- Lower a closure constant part against the preceding constant memory. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "part_to_words_def"
  (words_as_type_indexed_bitvec)]
def partWords {width : Nat} [NeZero width] (conf : Config) (memory : Spt (Value width))
    (part : ClosLang.ConstPart) (offset : BitVec width) : Option (Value width × List (Value width)) := do
  match part with
  | .int i =>
    if smallInt width i then
      some ((false, .word (smallnum i)), [])
    else
      let (sign, ws) := Misc.Multiword.i2mw (width := width) i
      let header ← encodeHeader (width := width) conf (if sign then 7 else 3) ws.length
      some ((true, makePtr conf offset (0 : BitVec width) ws.length), (header :: ws).map (fun w => (false, .word w)))
  | .con tag refs =>
    if refs.isEmpty then
      if tag < 2 ^ width / 16 then some ((false, .word (BitVec.ofNat width (16 * tag + 2))), []) else none
    else
      let header ← encodeHeader (width := width) conf (4 * tag) refs.length
      let addr := (offset <<< (shiftLength conf - wordShiftAmount width)) + (ptrBits conf tag refs.length ||| 1)
      let fields := refs.map (lookupMem memory)
      some ((true, .word addr), (false, .word header) :: fields)
  | .w64 word =>
    let ws : List (BitVec width) := if width < 64 then
      [BitVec.ofNat width (word.toNat / 2 ^ 32), BitVec.ofNat width (word.toNat % 2 ^ 32)]
      else [BitVec.ofNat width word.toNat]
    let header ← encodeHeader (width := width) conf 3 ws.length
    some ((true, makePtr conf offset (0 : BitVec width) ws.length), (header :: ws).map (fun w => (false, .word w)))
  | .str s =>
    let bs := s.explode
    let n := bs.length
    let k := byteLen width n
    if !(k < 2 ^ (width - 4) ∧ k < 2 ^ conf.lenSize) then none else
    let header := makeByteHeader (width := width) conf true n
    let ws := header :: writeBytes bs (List.replicate k 0) conf.be
    some ((true, makePtr conf offset (0 : BitVec width) k), ws.map (fun w => (false, .word w)))

/-- Convert parts while threading the sparse memory, index, and byte offset. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "parts_to_words_def"
  (words_as_type_indexed_bitvec)]
def partsToWords {width : Nat} [NeZero width] (conf : Config)
    (memory : Spt (Value width)) (index : Nat) :
    List ClosLang.ConstPart → BitVec width → Option (Value width × List (Value width))
  | [], _ => some (lookupMem memory (index - 1), [])
  | part :: parts, offset => do
      let (value, words) ← partWords conf memory part offset
      let (result, rest) ← partsToWords conf (sptInsert index value memory) (index + 1) parts
        (offset + wordSemBytesInWord * BitVec.ofNat width words.length)
      some (result, words ++ rest)

/-- Convert all constant parts from the empty initial memory. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "const_parts_to_words_def"
  (words_as_type_indexed_bitvec)]
def partsWords {width : Nat} [NeZero width] (conf : Config)
    (parts : List ClosLang.ConstPart) : Option ((Bool × WordLocW width) × List (Bool × WordLocW width)) :=
  partsToWords conf .ln 0 parts 0

end Flapjack.Compiler.Backend.DataToWord.Build
