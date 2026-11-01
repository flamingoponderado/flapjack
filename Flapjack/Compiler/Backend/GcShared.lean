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

end Backend
end Compiler
end Flapjack
