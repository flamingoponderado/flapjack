import Flapjack.HolRef

/-!
# Exact `gc_shared` heap carriers

Counterpart of the HOL `gc_shared` data structures
(`cakeml/compiler/backend/gc/gc_sharedScript.sml`).

The HOL definitions are

```
Datatype: heap_address = Pointer num 'a | Data 'a End
Datatype: heap_element =
  Unused num | ForwardPointer num 'a num | DataElement (('a heap_address) list) num 'b End
```

`num` is rendered as `Nat` and `('a heap_address) list` as `List (HeapAddress α)`.
The carriers and their element/heap length definitions are ported here; the
`gc_state` record remains to be ported for GC simulation.
-/

namespace Flapjack
namespace Compiler
namespace Backend

/-- Exact Lean rendering of the HOL `heap_address` datatype
`heap_address = Pointer num 'a | Data 'a`. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_address"]
inductive HeapAddress (α : Type) : Type where
  /-- `Pointer num 'a`: a pointer with an index and an address value. -/
  | pointer (index : Nat) (addr : α)
  /-- `Data 'a`: a direct data address. -/
  | data (addr : α)
  deriving Repr

/-- Exact Lean rendering of the HOL `heap_element` datatype
`Unused num | ForwardPointer num 'a num | DataElement (('a heap_address) list) num 'b`. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_element"]
inductive HeapElement (α β : Type) : Type where
  /-- `Unused num`. -/
  | unused (n : Nat)
  /-- `ForwardPointer num 'a num`. -/
  | forwardPointer (n : Nat) (addr : α) (ptr : Nat)
  /-- `DataElement (('a heap_address) list) num 'b`. -/
  | dataElement (ptrs : List (HeapAddress α)) (n : Nat) (data : β)
  deriving Repr

/-- Number of words occupied by an abstract heap element, including its
header. Both address and payload carriers are independently polymorphic. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "el_length_def"]
def elLength {α β : Type} : HeapElement α β → Nat
  | .unused len => len + 1
  | .forwardPointer _ _ len => len + 1
  | .dataElement _ len _ => len + 1

/-- Total word length of a heap, preserving the source's polymorphic
element carriers. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_length_def"]
def heapLength {α β : Type} (heap : List (HeapElement α β)) : Nat :=
  (heap.map elLength).sum

/-- An unused heap region of the given word length. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_expand_def"]
def heapExpand {α β : Type} (length : Nat) : List (HeapElement α β) :=
  if length = 0 then [] else [.unused (length - 1)]

/-- Look up an element at a heap offset; an offset inside an element fails. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_lookup_def"]
def heapLookup {α β : Type} (offset : Nat) : List (HeapElement α β) → Option (HeapElement α β)
  | [] => none
  | x :: xs =>
      if offset = 0 then some x
      else if offset < elLength x then none
      else heapLookup (offset - elLength x) xs

/-- Split a heap exactly at an element boundary. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_split_def"]
def heapSplit {α β : Type} (offset : Nat) :
    List (HeapElement α β) → Option (List (HeapElement α β) × List (HeapElement α β))
  | [] => if offset = 0 then some ([], []) else none
  | x :: xs =>
      if offset = 0 then some ([], x :: xs)
      else if offset < elLength x then none
      else (heapSplit (offset - elLength x) xs).map fun (first, second) => (x :: first, second)

/-- Recognize an abstract data element. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isDataElement_def"]
def isDataElement {α β : Type} (element : HeapElement α β) : Prop :=
  ∃ xs len data, element = .dataElement xs len data

/-- Recognize a successful lookup of an abstract data element. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isSomeDataElement_def"]
def isSomeDataElement {α β : Type} (element : Option (HeapElement α β)) : Prop :=
  ∃ xs len data, element = some (.dataElement xs len data)

/-- Recognize a forwarding pointer. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isForwardPointer_def"]
def isForwardPointer {α β : Type} : HeapElement α β → Bool
  | .forwardPointer .. => true
  | _ => false

/-- Every pointer in the roots names a data element in the heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "roots_ok_def"]
def rootsOk {α β γ : Type} (roots : List (HeapAddress α)) (heap : List (HeapElement β γ)) : Prop :=
  ∀ ptr value, .pointer ptr value ∈ roots → isSomeDataElement (heapLookup ptr heap)

/-- Heap length, absence of forwarding pointers, and validity of data-element
pointers, with both element carriers independently polymorphic. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_ok_def"]
def heapOk {α β : Type} (heap : List (HeapElement α β)) (limit : Nat) : Prop :=
  heapLength heap = limit ∧ heap.filter isForwardPointer = [] ∧
    ∀ xs len data ptr value, .dataElement xs len data ∈ heap ∧ .pointer ptr value ∈ xs →
      isSomeDataElement (heapLookup ptr heap)

end Backend
end Compiler
end Flapjack
