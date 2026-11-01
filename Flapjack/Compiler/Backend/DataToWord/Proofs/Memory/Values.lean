import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation
import Flapjack.Compiler.Backend.Semantics.DataSem.Value
import Flapjack.Misc.Sptree
import Flapjack.Misc.Multiword
import Flapjack.Compiler.Backend.DataToWord.Numbers
import Mathlib.Logic.Relation

/-! Value and reference traversals used by the abstract memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack
open Flapjack.Compiler.Backend.DataSem

/-- Abstract representation of a mutable reference block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "RefBlock_def"]
def refBlock {α β : Type} (values : List (HeapAddress α)) : HeapElement α (HeapTag × List β) :=
  .dataElement values values.length (.refTag, [])

/-- Abstract bignum cell; its unused address carrier is independent of the
payload word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Bignum_def"
  (words_as_type_indexed_bitvec)]
def bignumRep {width : Nat} [NeZero width] {α : Type} (i : Int) :
    HeapElement α (HeapTag × List (WordLocW width)) :=
  let (sign, payload) := Misc.Multiword.i2mw (width := width) i
  .dataElement [] payload.length (.numTag sign, payload.map .word)

/-- Pointer annotation for a reference, retaining the fully polymorphic
reference payload type inferred by the original definition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_ptr_annot_def"
  (words_as_type_indexed_bitvec)]
def refPtrAnnot {width : Nat} [NeZero width] {α : Type} (conf : Config) :
    Option (BvlSem.Ref α) → WordLocW width
  | some (.mutBlock tag _ left _ right) => .word (ptrBits conf tag (left.length + 1 + right.length))
  | _ => .word 0

/-- Abstract representation of a 64-bit value at an arbitrary positive word
width. Its unused heap-address carrier is independent of that width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Word64Rep_def"
  (words_as_type_indexed_bitvec)]
def word64Rep {width : Nat} [NeZero width] {α : Type} (w : BitVec 64) :
    HeapElement α (HeapTag × List (WordLocW width)) :=
  if width < 64 then
    .dataElement [] 2 (.word64Tag, [.word ((w >>> 32).setWidth width), .word (w.setWidth width)])
  else .dataElement [] 1 (.word64Tag, [.word (w.setWidth width)])

/-- The word64 representation is a data element with a matching payload length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Word64Rep_DataElement"
  (words_as_type_indexed_bitvec)]
theorem word64RepDataElement {width : Nat} [NeZero width] (w : BitVec 64) :
    ∃ words : List (WordLocW width),
      (word64Rep (α := WordLocW width) w) = .dataElement [] words.length (.word64Tag, words) := by
  by_cases h : width < 64 <;> simp [word64Rep, h]

/-- References occurring in a data value, traversing nested blocks in order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_refs_def"]
def getRefs : Value → List Nat
  | .refPtr _ ptr => [ptr]
  | .block _ _ values => values.flatMap getRefs
  | _ => []
termination_by value => sizeOf value
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem (by assumption)
  omega

/-- The tag and timestamp of the temporary Block in `ref_edge` do not affect
its references. The source uses an arbitrary tag; zero is an equal choice. -/
theorem getRefs_block_tag_irrelevant (timestamp tag tag' : Nat) (values : List Value) :
    getRefs (.block timestamp tag values) = getRefs (.block timestamp tag' values) := by
  simp only [getRefs]

/-- A direct edge between data-language references. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_def"]
def refEdge (refs : Spt (BvlSem.Ref Value)) (index target : Nat) : Prop :=
  match sptLookup index refs with
  | some (.valueArray values) => target ∈ getRefs (.block 0 0 values)
  | some (.thunk _ value) => target ∈ getRefs (.block 0 0 [value])
  | some (.mutBlock _ _ left value right) => target ∈ getRefs (.block 0 0 (left ++ [value] ++ right))
  | _ => False

/-- References reachable from roots by zero or more direct reference edges. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_def"]
def reachableRefs (roots : List Value) (refs : Spt (BvlSem.Ref Value)) (target : Nat) : Prop :=
  ∃ root start, root ∈ roots ∧ start ∈ getRefs root ∧ Relation.ReflTransGen (refEdge refs) start target

/-- Timestamps in a value and its nested blocks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_ts_def"]
def valueTimestamps : Value → List Nat
  | .block stamp _ values => stamp :: values.flatMap valueTimestamps
  | _ => []
termination_by value => sizeOf value
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem (by assumption)
  omega

/-- Whether a value occurs directly in a reference cell. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "find_ref_def"]
def findRef {α : Type} (cell : BvlSem.Ref α) (value : α) : Prop :=
  match cell with
  | .valueArray values => value ∈ values
  | .thunk _ child => child = value
  | .mutBlock _ _ left child right => value ∈ left ++ [child] ++ right
  | .byteArray .. => False

/-- All timestamps in stack values and directly stored reference values. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_def"]
def allTimestamps (refs : Spt (BvlSem.Ref Value)) (stack : List Value) : Nat → Prop :=
  fun stamp => ∃ value, ((∃ index cell, sptLookup index refs = some cell ∧ findRef cell value) ∨ value ∈ stack) ∧
    stamp ∈ valueTimestamps value

/-- The original endianness agreement predicate is polymorphic equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "be_ok_def"]
def beOk {α : Type} (left right : α) : Prop := left = right

/-- Preorder traversal of values and nested block contents. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_def"]
def valueListValues : List Value → List Value
  | .block stamp tag values :: rest => .block stamp tag values :: valueListValues values ++ valueListValues rest
  | value :: rest => value :: valueListValues rest
  | [] => []
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- All values nested in reference cells or the saved stack. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_vs_def"]
def allValues (refs : Spt (BvlSem.Ref Value)) (stack : List Value) : Value → Prop :=
  fun value =>
    (∃ index values, sptLookup index refs = some (.valueArray values) ∧ value ∈ valueListValues values) ∨
    (∃ index mode child, sptLookup index refs = some (.thunk mode child) ∧ value ∈ valueListValues [child]) ∨
    (∃ index tag finalised left child right,
      sptLookup index refs = some (.mutBlock tag finalised left child right) ∧
        value ∈ valueListValues (left ++ [child] ++ right)) ∨
    value ∈ valueListValues stack

/-- Nonempty blocks sharing a timestamp have identical tag and contents, and
their timestamp is below the next available timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_def"]
def blocksUnique (next : Nat) (values : Value → Prop) : Prop :=
  ∀ stamp tag1 xs1 tag2 xs2,
    values (.block stamp tag1 xs1) ∧ xs1 ≠ [] ∧ values (.block stamp tag2 xs2) ∧ xs2 ≠ [] →
      tag1 = tag2 ∧ xs1 = xs2 ∧ stamp < next

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
