import Flapjack.Misc.SetSep

namespace Flapjack.Test.SetSepElementary
open Flapjack.SetSep

-- Generic kernel fixtures exercise the full heaps and witness types, rather
-- than imposing finite sets, machine words or distinctness on the definitions.
example {α : Type} (element : α) : one element (fun entry => entry = element) := rfl
example {α : Type} : emp (α := α) (fun _ => False) := rfl
example {α : Type} : cond (α := α) True (fun _ => False) := ⟨rfl, trivial⟩
example {α : Type} (heap : α → Prop) : ¬ cond False heap := fun h => h.2
example {α : Type} (element : α) : ¬ cond True (fun entry => entry = element) := by
  intro h
  have impossible := congrFun h.1 element
  exact (iff_of_eq impossible).mp rfl
example {α : Type} (heap : α → Prop) : split heap (heap, fun _ => False) := by
  constructor
  · funext entry
    exact or_false _
  · intro entry h
    exact h.2
example {α : Type} (element : α) :
    ¬ split (fun entry => entry = element)
      ((fun entry => entry = element), (fun entry => entry = element)) := by
  intro h
  exact h.2 element ⟨rfl, rfl⟩
example : ¬ split (fun _ : Bool => False)
    ((fun entry => entry = true), (fun _ => False)) := by
  intro h
  exact (iff_of_eq (congrFun h.1 true)).mp (Or.inl rfl)
example {α : Type} : star (emp (α := α)) emp (fun _ => False) := by
  refine ⟨(fun _ => False), (fun _ => False), ?_, rfl, rfl⟩
  constructor
  · funext entry
    exact or_false _
  · intro entry h
    exact h.1
example (heap : Bool → Prop) : star emp emp heap → emp heap := by
  rintro ⟨first, second, partition, rfl, rfl⟩
  exact (show (fun _ => False) = heap by simpa using partition.1).symm
example : star (one true) (one false) (fun _ : Bool => True) := by
  refine ⟨(fun entry => entry = true), (fun entry => entry = false), ?_, rfl, rfl⟩
  constructor
  · funext entry
    cases entry <;> simp
  · intro entry h
    exact Bool.noConfusion (h.1.symm.trans h.2)
example : ¬ star (one true) (one true) (fun entry : Bool => entry = true) := by
  rintro ⟨first, second, partition, rfl, rfl⟩
  exact partition.2 true ⟨rfl, rfl⟩
example : sepExists (fun witness : Nat => cond (witness = 7)) (fun _ : Bool => False) :=
  ⟨7, rfl, rfl⟩
example (heap : Nat → Prop) : ¬ sepExists (fun _ : Bool => cond False) heap := by
  rintro ⟨witness, _, impossible⟩
  exact impossible
example (heap : Nat → Prop) : sepExists (fun _ : Bool => fun actual => actual = heap) heap :=
  ⟨false, rfl⟩
-- Infinite heaps are valid; no finiteness requirement is hidden in split.
example : split (fun _ : Nat => True) ((fun _ => True), (fun _ => False)) := by
  constructor
  · funext entry
    simp
  · intro entry h
    exact h.2

end Flapjack.Test.SetSepElementary
