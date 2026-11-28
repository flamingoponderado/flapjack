module

public import Flapjack.HolRef
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! HOL's optional least natural satisfying a predicate. -/
namespace Flapjack

/-- Return the least witness when one exists, and none otherwise. HOL's
`LEAST` is rendered by `Nat.find` under the existence guard: the least witness
is unique by HOL's `LEAST_EXISTS_IMP` and Lean's `Nat.find_spec` and
`Nat.find_min`. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_def"]
noncomputable def holOLeast (p : Nat → Prop) : Option Nat := by
  classical
  exact if h : ∃ n, p n then some (Nat.find h) else none

/-- Reason by the empty case and by an arbitrary least witness. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_INTRO"]
theorem holOLeast_intro (p : Nat → Prop) (q : Option Nat → Prop)
    (premises : ((∀ n, ¬ p n) → q none) ∧
      (∀ n, p n ∧ (∀ m, m < n → ¬ p m) → q (some n))) :
    q (holOLeast p) := by
  classical
  unfold holOLeast
  split
  · rename_i h
    exact premises.2 (Nat.find h) ⟨Nat.find_spec h, fun m less => Nat.find_min h less⟩
  · rename_i h
    apply premises.1
    intro n hn
    exact h ⟨n, hn⟩

/-- Original `OLEAST_EQ_SOME`: a least witness is a satisfying index below
which nothing satisfies the predicate. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_EQ_SOME"]
theorem holOLeast_eq_some (p : Nat → Prop) (n : Nat) :
    holOLeast p = some n ↔ p n ∧ ∀ m, m < n → ¬ p m := by
  classical
  unfold holOLeast
  by_cases h : ∃ k, p k
  · rw [dif_pos h, Option.some.injEq, Nat.find_eq_iff h]
  · rw [dif_neg h]
    constructor
    · intro hx
      exact absurd hx (by simp)
    · rintro ⟨hn, _⟩
      exact absurd ⟨n, hn⟩ h

/-- Original `OLEAST_EQ_NONE`: there is no least witness exactly when the
predicate has no witness. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_EQ_NONE"]
theorem holOLeast_eq_none (p : Nat → Prop) :
    holOLeast p = none ↔ ∀ n, ¬ p n := by
  classical
  unfold holOLeast
  by_cases h : ∃ k, p k
  · rw [dif_pos h]
    constructor
    · intro hx
      exact absurd hx (by simp)
    · intro hn
      exact absurd (Nat.find_spec h) (hn (Nat.find h))
  · rw [dif_neg h]
    constructor
    · intro _ n hp
      exact h ⟨n, hp⟩
    · intro _
      rfl

/-- Flapjack infrastructure: pointwise-equivalent predicates have the same
optional least witness. It has no standalone HOL declaration; HOL derives the
same fact by applying `OLEAST_EQ_SOME` to both sides. -/
theorem holOLeast_congr {p q : Nat → Prop} (h : ∀ n, p n ↔ q n) :
    holOLeast p = holOLeast q := by
  classical
  unfold holOLeast
  by_cases hp : ∃ n, p n
  · have hq : ∃ n, q n := hp.imp fun n => (h n).mp
    rw [dif_pos hp, dif_pos hq, Option.some.injEq, Nat.find_congr' (hpq := fun {n} => h n)]
  · have hq : ¬ ∃ n, q n := fun hq => hp (hq.imp fun n => (h n).mpr)
    rw [dif_neg hp, dif_neg hq]

/-- Original `OLEAST_SOME_IMP`: a least witness satisfies the predicate and no
smaller number does. -/
@[hol "cakeml/misc/miscScript.sml" "OLEAST_SOME_IMP"]
theorem holOLeast_some_imp (P : Nat → Prop) (i : Nat) (h : holOLeast P = some i) :
    P i ∧ ∀ n, n < i → ¬ P n := by
  classical
  unfold holOLeast at h
  split at h
  · rename_i hex
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩
  · simp at h

end Flapjack
