import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Flapjack infrastructure for adjacent Boolean relation comparisons on a
native list. No separate CakeML declaration is attached to this generic helper. -/
def adjacentSorted {α : Type} (r : α → α → Bool) (xs : List α) : Prop :=
  (xs.zip xs.tail).all (fun (x, y) => r x y) = true

private theorem adjacentCons {α : Type} (r : α → α → Bool) (x y : α) (ys : List α) :
    adjacentSorted r (x :: y :: ys) ↔ r x y = true ∧ adjacentSorted r (y :: ys) := by
  simp [adjacentSorted]

/-- Full original sortedness weakening, with exactly the original distinctness
and member/inequality guarded relation-transfer hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_weaken2"]
theorem sortedWeaken2 {α : Type} (r r' : α → α → Bool) (xs : List α)
    (hs : adjacentSorted r xs) (hd : xs.Nodup)
    (hr : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → r x y = true → r' x y = true) :
    adjacentSorted r' xs := by
  induction xs with
  | nil => simp [adjacentSorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [adjacentSorted]
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := (adjacentCons r x y ys).mp hs
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hd
      apply (adjacentCons r' x y ys).mpr
      constructor
      · apply hr x y (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self)
        · intro heq
          apply hnot
          rw [heq]
          exact List.mem_cons_self
        · exact hxy
      · apply ih htail hnodup
        intro a b ha hb hne hab
        exact hr a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) hne hab

/-- Full original strict division order on even natural registers. EVEN is
remainder-zero at divisor two, with no finite-width bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_GT"]
theorem evenGt (a b : Nat) (ha : a % 2 = 0) (hb : b % 2 = 0) (hgt : a > b) :
    a / 2 > b / 2 := by omega

/-- Full original transitivity of strict natural greater-than. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "transitive_GT"]
theorem transitiveGt (a b c : Nat) (hab : a > b) (hbc : b > c) : a > c :=
  Nat.lt_trans hbc hab

end Flapjack.Compiler.Backend.WordToStack
