import Flapjack.Compiler.Backend.StackRemove.Proofs.Memory

namespace Flapjack.Test.StackRemoveMemory
open Flapjack.SetSep Flapjack.Compiler.Backend.StackRemove

-- Whole-heap equality is checked at independently typed addresses and values.
example {α β : Type} (m : α → β) (domain : α → Prop) :
    memoryHOL m domain (fun2Set (m, domain)) := rfl
example {α β : Type} (m : α → β) (domain : α → Prop)
    (first second : (α × β) → Prop)
    (hfirst : memoryHOL m domain first) (hsecond : memoryHOL m domain second) :
    first = second := hfirst.trans hsecond.symm
example {α β : Type} (m : α → β) : memoryHOL m (fun _ => False) (fun _ => False) := by
  funext entry
  apply propext
  simp [fun2Set]
example (m : Nat → Bool) :
    memoryHOL m (fun _ => True) (fun entry => entry.2 = m entry.1) := by
  funext entry
  rcases entry with ⟨address, value⟩
  apply propext
  simp [fun2SetThm, eq_comm]
example : memoryHOL (fun b : Bool => if b then 7 else 11) (fun _ => True)
    (fun entry => entry = (true, 7) ∨ entry = (false, 11)) := by
  funext entry
  rcases entry with ⟨address, value⟩
  apply propext
  cases address <;> simp [fun2SetThm, eq_comm]
example (m : Bool → Nat × Bool) :
    memoryHOL m (fun _ => True) (fun entry => entry.2 = m entry.1) := by
  funext entry
  rcases entry with ⟨address, value⟩
  apply propext
  simp [fun2SetThm, eq_comm]
-- Missing valid entries and additional entries both violate full equality.
example : ¬ memoryHOL (fun _ : Nat => false) (fun n => n = 0) (fun _ => False) := by
  intro h
  have entryEq := congrFun h (0, false)
  exact (iff_of_eq entryEq).mpr ((fun2SetThm _ _ _ _).2 ⟨rfl, rfl⟩)
example : ¬ memoryHOL (fun _ : Nat => false) (fun _ => False)
    (fun entry => entry = (0, false)) := by
  intro h
  have entryEq := congrFun h (0, false)
  have member := (iff_of_eq entryEq).mp rfl
  simp [fun2SetThm] at member
example : ¬ memoryHOL (fun _ : Nat => false) (fun n => n = 0)
    (fun entry => entry = (0, true)) := by
  intro h
  have member := (iff_of_eq (congrFun h (0, true))).mp rfl
  simp [fun2SetThm] at member
example : ¬ memoryHOL (fun _ : Nat => false) (fun n => n = 0)
    (fun entry => entry = (1, false)) := by
  intro h
  have member := (iff_of_eq (congrFun h (1, false))).mp rfl
  simp [fun2SetThm] at member
-- Equal stored values at different addresses are not an injectivity failure.
example : memoryHOL (fun _ : Nat => false) (fun n => n = 1 ∨ n = 2)
    (fun entry => entry = (1, false) ∨ entry = (2, false)) := by
  funext entry
  rcases entry with ⟨address, value⟩
  apply propext
  simp only [fun2SetThm, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  · rintro ⟨rfl, rfl | rfl⟩ <;> simp

end Flapjack.Test.StackRemoveMemory
