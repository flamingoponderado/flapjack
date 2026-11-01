import Flapjack.Compiler.Backend.GcShared
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.AstHOL.BackendOperators

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
