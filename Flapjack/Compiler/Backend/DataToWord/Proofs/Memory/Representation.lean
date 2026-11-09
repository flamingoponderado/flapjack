module

public import Flapjack.Compiler.Backend.GcShared
public import Flapjack.Compiler.Backend.DataToWord.Header
public import Flapjack.AstHOL.BackendOperators
public import Flapjack.Misc.GoodDimindex

@[expose] public section

/-! Abstract heap representation used by data-to-word memory correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Tags attached to the abstract heap elements used by the source invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "tag"]
inductive HeapTag where
  | blockTag : Nat → HeapTag
  | refTag : HeapTag
  | bytesTag : Bool → Nat → HeapTag
  | thunkTag : AstHOL.ThunkMode → HeapTag
  | numTag : Bool → HeapTag
  | word64Tag : HeapTag
  deriving Repr

/-- Abstract representation of an immutable block. The address and auxiliary
payload types are independently polymorphic in the original declaration. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "BlockRep_def"]
def blockRep {α β : Type} (tag : Nat) (values : List (HeapAddress α)) :
    HeapElement α (HeapTag × List β) :=
  .dataElement values values.length (.blockTag tag, [])

/-- Immediate representation of a nullary block tag. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "BlockNil_def"
  (words_as_type_indexed_bitvec)]
def blockNil {width : Nat} [NeZero width] (tag : Nat) : BitVec width :=
  (BitVec.ofNat width tag <<< 4) + 2

/-- Abstract representation of a thunk and its single heap address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ThunkBlock_def"]
def thunkBlock {α β : Type} (mode : AstHOL.ThunkMode) (value : HeapAddress α) :
    HeapElement α (HeapTag × List β) :=
  .dataElement [value] 1 (.thunkTag mode, [])

/-- Encode an abstract pointer index while preserving its low tag bits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_addr_def"
  (words_as_type_indexed_bitvec)]
def getAddr {width : Nat} [NeZero width] (conf : Config) (index : Nat) (value : WordLocW width) : BitVec width :=
  (BitVec.ofNat width index <<< shiftLength conf) ||| getLowerBits conf value

/-- Project an abstract heap address to the corresponding word location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_addr_def"
  (words_as_type_indexed_bitvec)]
def wordAddr {width : Nat} [NeZero width] (conf : Config) : HeapAddress (WordLocW width) → WordLocW width
  | .data (.loc label _) => .loc label 0
  | .data (.word value) => .word (value &&& ~~~(1 : BitVec width))
  | .pointer index value => .word (getAddr conf index value)

/-- Encode a thunk's evaluation mode in the header tag bits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "thunk_tag_to_bits_def"
  (words_as_type_indexed_bitvec)]
def thunkTagToBits {width : Nat} [NeZero width] : AstHOL.ThunkMode → BitVec width
  | .evaluated => 1
  | .notEvaluated => 0

/-- Construct a concrete header and payload for an abstract heap element. The
header and payload word widths are independent in the original definition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_payload_def"
  (words_as_type_indexed_bitvec)]
def wordPayload {headerWidth : Nat} {payloadWidth : Nat} [NeZero headerWidth] [NeZero payloadWidth]
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (conf : Config) :
    BitVec headerWidth × List (WordLocW payloadWidth) × Bool :=
  match tag with
  | .blockTag n =>
      let header := makeHeader conf (BitVec.ofNat headerWidth n <<< (2 : Nat)) addresses.length
      (header, addresses.map (wordAddr conf),
        payload.isEmpty && decide (addresses.length = len ∧ encodeHeader conf (n * 4) addresses.length = some header))
  | .refTag =>
      (makeHeader conf 2 addresses.length, addresses.map (wordAddr conf),
        payload.isEmpty && decide (addresses.length = len))
  | .thunkTag mode =>
      (makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) addresses.length, addresses.map (wordAddr conf),
        payload.isEmpty && decide (addresses.length = 1 ∧ len = 1))
  | .word64Tag =>
      (makeHeader conf 3 len, payload,
        addresses.isEmpty && decide (payload.length = len) && (encodeHeader (width := headerWidth) conf 3 len).isSome)
  | .numTag negative =>
      let tagBits : BitVec headerWidth := ((if negative then 1 else 0) <<< 2) ||| 3
      (makeHeader conf tagBits payload.length, payload,
        addresses.isEmpty && decide (payload.length = len) && (encodeHeader (width := headerWidth) conf tagBits.toNat payload.length).isSome)
  | .bytesTag compareByContents n =>
      let k := if headerWidth = 32 then 2 else 3
      (makeByteHeader conf compareByContents n, payload,
        addresses.isEmpty && decide (payload.length = len ∧ n + 2 ^ k < 2 ^ (conf.lenSize + k)))

/-- Successful encoding produces exactly the declared number of payload words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_payload_IMP"
  (words_as_type_indexed_bitvec)]
theorem wordPayloadImp {headerWidth : Nat} {payloadWidth : Nat}
    [NeZero headerWidth] [NeZero payloadWidth]
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (conf : Config) (h : BitVec headerWidth)
    (ts : List (WordLocW payloadWidth))
    (encoded : wordPayload addresses len tag payload conf = (h, ts, true)) :
    ts.length = len := by
  cases tag <;> simp [wordPayload] at encoded
  all_goals rcases encoded with ⟨_, rfl, rest⟩
  all_goals simp_all

/-- A valid payload has the declared length; its header identifies whether
it contains raw words or projected heap addresses. The header and payload
widths remain independent, as in the original theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_payload_T_IMP"
  (words_as_type_indexed_bitvec)]
theorem wordPayloadTrueImp {headerWidth : Nat} {payloadWidth : Nat}
    [NeZero headerWidth] [NeZero payloadWidth]
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (conf : Config) (h : BitVec headerWidth)
    (ts : List (WordLocW payloadWidth)) :
    wordPayload addresses len tag payload conf = (h, ts, true) ∧
      goodDimindex headerWidth ∧ conf.lenSize + 2 < headerWidth →
    len = ts.length ∧ if h.getLsbD 2 then addresses = [] else ts = addresses.map (wordAddr conf) := by
  rintro ⟨eqn, good, bound⟩
  have hb : 2 < headerWidth - conf.lenSize := by omega
  rcases good with hw | hw <;> subst headerWidth
  all_goals cases tag <;> simp [wordPayload] at eqn
  all_goals rcases eqn with ⟨rfl, rfl, eqn⟩
  all_goals simp_all [makeHeader, makeByteHeader]
  all_goals split at * <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
