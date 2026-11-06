import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation
import Flapjack.Compiler.Backend.GcCombined

/-! Abstract heap and generation conditions used by data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.GcCombined

/-- Every element before this exact heap boundary is a data element. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_up_to_def"]
def dataUpTo {α β : Type} (offset : Nat) (heap : List (HeapElement α β)) : Prop :=
  ∃ first second, heapSplit offset heap = some (first, second) ∧ ∀ element ∈ first, isDataElement element

/-- The designated unused region has its source length and follows data. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "unused_space_inv_def"]
def unusedSpaceInv {α β : Type} (offset length : Nat) (heap : List (HeapElement α β)) : Prop :=
  (length ≠ 0 → heapLookup offset heap = some (.unused (length - 1))) ∧
    offset + length ≤ heapLength heap ∧ dataUpTo offset heap

/-- Mutable tags are references and thunks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isMutTag_def"]
def isMutTag (tag : HeapTag) : Prop :=
  tag = .refTag ∨ ∃ mode, tag = .thunkTag mode

/-- Recognize a data element with a mutable tag; its address and auxiliary
payload carriers are independent. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isRef_def"]
def isRef {α β : Type} : HeapElement α (HeapTag × β) → Prop
  | .dataElement _ _ (tag, _) => isMutTag tag
  | _ => False

/-- Pointers from a generation's preceding heap do not target the region
between that generation's start and the references boundary. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_start_ok_def"]
def genStartOk {α β : Type} (heap : List (HeapElement α β)) (refsStart genStart : Nat) : Prop :=
  ∃ first second, heapSplit genStart heap = some (first, second) ∧
    ∀ xs len data ptr value, .dataElement xs len data ∈ first ∧ .pointer ptr value ∈ xs →
      ptr < genStart ∨ refsStart ≤ ptr

/-- Generation starts lie before the allocation point and meet the
corresponding pointer restriction. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_state_ok_def"]
def genStateOk {α β : Type} (a refsStart : Nat) (heap : List (HeapElement α β)) : GenState → Prop
  | .genState _ starts => (∀ start ∈ starts, start ≤ a) ∧ ∀ start ∈ starts, genStartOk heap refsStart start

/-- Heap separation and generation conditions for the selected GC kind. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_kind_inv_def"]
def gcKindInv {α β : Type} (conf : Config) (a sp sp1 : Nat) (gens : GenState)
    (heap : List (HeapElement α (HeapTag × β))) : Prop :=
  match conf.gcKind with
  | .none | .simple => sp1 = 0
  | .generational _ =>
      genStateOk a (a + sp + sp1) heap gens ∧
        ∃ first second, heapSplit (a + sp + sp1) heap = some (first, second) ∧
          (∀ element ∈ first, ¬ isRef element) ∧ ∀ element ∈ second, isRef element

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
