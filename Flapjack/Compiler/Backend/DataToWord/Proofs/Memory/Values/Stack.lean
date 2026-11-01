import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values

/-! Stack membership and reachability facts for the memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Every value on a stack appears in its recursive value traversal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs"]
theorem mem_valueListValues (values : List Value) (value : Value)
    (member : value ∈ values) : value ∈ valueListValues values := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      cases head <;> simp_all [valueListValues] <;> rcases member with h | h
      all_goals first | exact Or.inl h | exact Or.inr (ih h) | exact Or.inr (Or.inr (ih h))

/-- A stack value belongs to the set of all values in the memory invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_stack_all_vs"]
theorem mem_stack_allValues (value : Value) (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (member : value ∈ stack) : allValues refs stack value := by
  exact Or.inr (Or.inr (Or.inr (mem_valueListValues stack value member)))

/-- Recursive traversal distributes over list append. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_append"]
theorem valueListValues_append (xs ys : List Value) :
    valueListValues (xs ++ ys) = valueListValues xs ++ valueListValues ys := by
  induction xs with
  | nil => simp [valueListValues]
  | cons head tail ih => cases head <;> simp [valueListValues, ih, List.append_assoc]

/-- A nested value of a member remains in the traversal of the whole list.
This is Flapjack list infrastructure. -/
theorem valueListValues_singleton_subset (values : List Value) (child value : Value)
    (member : child ∈ values) (nested : value ∈ valueListValues [child]) :
    value ∈ valueListValues values := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      have split : valueListValues (head :: tail) = valueListValues [head] ++ valueListValues tail := by
        simpa using valueListValues_append [head] tail
      rw [split, List.mem_append]
      rcases List.mem_cons.mp member with equal | inTail
      · subst head
        exact Or.inl nested
      · exact Or.inr (ih inTail)

/-- Every value found by the recursive traversal comes from one list member.
This is Flapjack list infrastructure. -/
theorem valueListValues_member_origin (values : List Value) (value : Value)
    (member : value ∈ valueListValues values) :
    ∃ child, child ∈ values ∧ value ∈ valueListValues [child] := by
  induction values with
  | nil => simp [valueListValues] at member
  | cons head tail ih =>
      have split : valueListValues (head :: tail) = valueListValues [head] ++ valueListValues tail := by
        simpa using valueListValues_append [head] tail
      rw [split, List.mem_append] at member
      rcases member with nested | nested
      · exact ⟨head, by simp, nested⟩
      · obtain ⟨child, member, nested⟩ := ih nested
        exact ⟨child, List.mem_cons_of_mem head member, nested⟩

/-- A nested value of a pair's first component occurs in the traversal of all
first components. The pair's second component remains polymorphic. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_FST"]
theorem mem_valueListValues_fst {α : Type} (xs : List (Value × α)) (first : Value) (second : α)
    (value : Value) (h : (first, second) ∈ xs ∧ value ∈ valueListValues [first]) :
    value ∈ valueListValues (xs.map Prod.fst) := by
  apply valueListValues_singleton_subset _ first value
  · exact List.mem_map.mpr ⟨(first, second), h.1, rfl⟩
  · exact h.2

/-- Restricting a list of pairs restricts the traversal of first components. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_SUBSET"]
theorem mem_valueListValues_subset {α : Type} (ys xs : List (Value × α)) (value : Value)
    (h : (∀ pair, pair ∈ ys → pair ∈ xs) ∧ value ∈ valueListValues (ys.map Prod.fst)) :
    value ∈ valueListValues (xs.map Prod.fst) := by
  obtain ⟨child, mapped, nested⟩ := valueListValues_member_origin _ value h.2
  obtain ⟨pair, pairMember, eq⟩ := List.mem_map.mp mapped
  cases pair with
  | mk first second =>
      simp only at eq
      subst child
      exact mem_valueListValues_fst xs first second value ⟨h.1 _ pairMember, nested⟩

/-- Block uniqueness is preserved when stack pairs are restricted by membership. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_stack_permute"]
theorem blocksUnique_stackPermute {α : Type} (ys xs : List (Value × α)) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (h : (∀ pair, pair ∈ ys → pair ∈ xs) ∧
      blocksUnique next (allValues refs (xs.map Prod.fst ++ stack))) :
    blocksUnique next (allValues refs (ys.map Prod.fst ++ stack)) := by
  have subset : ∀ value, allValues refs (ys.map Prod.fst ++ stack) value →
      allValues refs (xs.map Prod.fst ++ stack) value := by
    intro value member
    rcases member with left | middle | right | fromStack
    · exact Or.inl left
    · exact Or.inr (Or.inl middle)
    · exact Or.inr (Or.inr (Or.inl right))
    · apply Or.inr (Or.inr (Or.inr ?_))
      rw [valueListValues_append, List.mem_append] at fromStack ⊢
      rcases fromStack with fromPrefix | fromTail
      · exact Or.inl (mem_valueListValues_subset ys xs value ⟨h.1, fromPrefix⟩)
      · exact Or.inr fromTail
  intro stamp tag1 xs1 tag2 xs2 premises
  exact h.2 stamp tag1 xs1 tag2 xs2
    ⟨subset _ premises.1, premises.2.1, subset _ premises.2.2.1, premises.2.2.2⟩

/-- Extending a stack cannot remove a reference reachable from it. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_stack_subset"]
theorem reachableRefs_stackSubset (xs ys : List Value) (refs : Spt (BvlSem.Ref Value)) (n : Nat)
    (h : reachableRefs ys refs n ∧ ∀ value, value ∈ ys → value ∈ xs) :
    reachableRefs xs refs n := by
  obtain ⟨⟨value, index, member, found, path⟩, subset⟩ := h
  exact ⟨value, index, subset value member, found, path⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
