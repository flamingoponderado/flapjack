module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack

@[expose] public section

/-! Block uniqueness when a thunk's contents are added to the stack. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A thunk's contents already occur in the reference-cell part of `allValues`.
This support fact is used to prove the two source block-uniqueness lemmas. -/
theorem allValues_addThunk (refs : Spt (BvlSem.Ref Value))
    (index : Nat) (mode : AstHOL.ThunkMode) (child : Value) (stack : List Value)
    (found : sptLookup index refs = some (.thunk mode child)) (value : Value)
    (member : allValues refs (child :: stack) value) : allValues refs stack value := by
  rcases member with array | thunk | mutable | inStack
  · exact Or.inl array
  · exact Or.inr (Or.inl thunk)
  · exact Or.inr (Or.inr (Or.inl mutable))
  · have split : valueListValues (child :: stack) = valueListValues [child] ++ valueListValues stack := by
      simpa using valueListValues_append [child] stack
    rw [split, List.mem_append] at inStack
    rcases inStack with nested | rest
    · exact Or.inr (Or.inl ⟨index, mode, child, found, nested⟩)
    · exact Or.inr (Or.inr (Or.inr rest))

/-- A referenced thunk's contents can replace its pointer in the stack. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_Thunk"]
theorem blocksUnique_thunk {α : Type} (index : Nat) (refs : Spt (BvlSem.Ref Value))
    (mode : AstHOL.ThunkMode) (child : Value) (next : Nat) (bit : Bool)
    (vars : List (Value × α))
    (h : sptLookup index refs = some (.thunk mode child) ∧
      blocksUnique next (allValues refs (.refPtr bit index :: vars.map Prod.fst))) :
    blocksUnique next (allValues refs (child :: vars.map Prod.fst)) := by
  have extended : blocksUnique next (allValues refs (child :: .refPtr bit index :: vars.map Prod.fst)) := by
    intro stamp tag1 xs1 tag2 xs2 premises
    apply h.2 stamp tag1 xs1 tag2 xs2
    exact ⟨allValues_addThunk refs index mode child _ h.1 _ premises.1, premises.2.1,
      allValues_addThunk refs index mode child _ h.1 _ premises.2.2.1, premises.2.2.2⟩
  have result := blocksUnique_stackSubset [child] [child, .refPtr bit index] next refs
    (vars.map Prod.fst) (by simp) (by simpa using extended)
  simpa using result

/-- A referenced thunk's contents can be added without removing its pointer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_Thunk2"]
theorem blocksUnique_thunk2 {α : Type} (index : Nat) (refs : Spt (BvlSem.Ref Value))
    (mode : AstHOL.ThunkMode) (child : Value) (next : Nat) (vars : List (Value × α))
    (h : sptLookup index refs = some (.thunk mode child) ∧
      blocksUnique next (allValues refs (.refPtr false index :: vars.map Prod.fst))) :
    blocksUnique next (allValues refs (child :: .refPtr false index :: vars.map Prod.fst)) := by
  intro stamp tag1 xs1 tag2 xs2 premises
  apply h.2 stamp tag1 xs1 tag2 xs2
  exact ⟨allValues_addThunk refs index mode child _ h.1 _ premises.1, premises.2.1,
    allValues_addThunk refs index mode child _ h.1 _ premises.2.2.1, premises.2.2.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
