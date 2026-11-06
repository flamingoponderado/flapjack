import Flapjack.Compiler.Backend.GcShared

/-! Address renaming for abstract heap roots. -/
namespace Flapjack.Compiler.Backend

/-- Rename pointer offsets while preserving attached values and data. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "ADDR_MAP_def"]
def addrMap {α : Type} (f : Nat → Nat) : List (HeapAddress α) → List (HeapAddress α)
  | [] => []
  | .data value :: tail => .data value :: addrMap f tail
  | .pointer address value :: tail => .pointer (f address) value :: addrMap f tail

/-- Apply an address renaming to one root. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "ADDR_APPLY_def"]
def addrApply {α : Type} (f : Nat → Nat) : HeapAddress α → HeapAddress α
  | .pointer address value => .pointer (f address) value
  | .data value => .data value

/-- Renamings agreeing at every pointer in a list give identical results. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "ADDR_MAP_EQ"]
theorem addrMap_eq {α : Type} (xs : List (HeapAddress α)) (f g : Nat → Nat)
    (agree : ∀ p d, .pointer p d ∈ xs → f p = g p) : addrMap f xs = addrMap g xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    have tailAgree : ∀ p d, .pointer p d ∈ tail → f p = g p := by
      intro p d member
      exact agree p d (by simp [member])
    cases head with
    | data value => simp [addrMap, ih tailAgree]
    | pointer address value =>
      have headAgree := agree address value (by simp)
      simp [addrMap, headAgree, ih tailAgree]

/-- Address renaming preserves the number of roots. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "ADDR_MAP_LENGTH"]
theorem addrMap_length {α : Type} (xs : List (HeapAddress α)) (f : Nat → Nat) :
    xs.length = (addrMap f xs).length := by
  induction xs with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [addrMap, ← ih]

/-- Address renaming distributes over concatenation. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "ADDR_MAP_APPEND"]
theorem addrMap_append {α : Type} (xs ys : List (HeapAddress α)) (f : Nat → Nat) :
    addrMap f (xs ++ ys) = addrMap f xs ++ addrMap f ys := by
  induction xs with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [addrMap, ih]

/-- Every renamed pointer comes from a pointer carrying the same value. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "MEM_ADDR_MAP"]
theorem mem_addrMap {α : Type} (xs : List (HeapAddress α)) (f : Nat → Nat) (ptr : Nat) (u : α)
    (member : .pointer ptr u ∈ addrMap f xs) :
    ∃ y, .pointer y u ∈ xs ∧ f y = ptr := by
  induction xs with
  | nil => simp [addrMap] at member
  | cons head tail ih =>
    cases head with
    | data value =>
      have memberTail : .pointer ptr u ∈ addrMap f tail := by simpa [addrMap] using member
      obtain ⟨y, hy, eq⟩ := ih memberTail
      exact ⟨y, by simp [hy], eq⟩
    | pointer address value =>
      simp only [addrMap, List.mem_cons, HeapAddress.pointer.injEq] at member
      rcases member with ⟨eqPtr, eqVal⟩ | member
      · subst value
        exact ⟨address, by simp, eqPtr.symm⟩
      · obtain ⟨y, hy, eq⟩ := ih member
        exact ⟨y, by simp [hy], eq⟩

end Flapjack.Compiler.Backend
