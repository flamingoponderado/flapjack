module

public import Flapjack.HolRef

@[expose] public section

/-! Consecutive indexing from the CakeML misc theory. -/
namespace Flapjack

/-- Pair each list element with its index, starting at `offset`. -/
@[simp, hol "cakeml/misc/miscScript.sml" "enumerate_def"]
def enumerate {A : Type} : Nat → List A → List (Nat × A)
  | _, [] => []
  | offset, x :: xs => (offset, x) :: enumerate (offset + 1) xs

/-- Original `LENGTH_enumerate`: enumerating preserves the list length. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_enumerate"]
theorem length_enumerate {A : Type} (xs : List A) (k : Nat) :
    (enumerate k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => simp [enumerate]
  | cons x rest ih => simp only [enumerate, List.length_cons, ih]

/-- Original `MEM_enumerate_IMP`: an enumerated pair's second component is a
member of the list. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_enumerate_IMP"]
theorem mem_enumerate_imp {A : Type} (ls : List A) (k : Nat) (i : Nat) (e : A) :
    (i, e) ∈ enumerate k ls → e ∈ ls := by
  intro h
  induction ls generalizing k with
  | nil => simp [enumerate] at h
  | cons x rest ih =>
    simp only [enumerate, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl (Prod.mk.inj h).2
    · exact Or.inr (ih (k + 1) h)

end Flapjack
