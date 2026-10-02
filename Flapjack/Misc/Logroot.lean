import Flapjack.HolRef

/-!
# HOL `logroot`: the specified logarithm `LOG`

Counterpart of the pinned `hol4/src/num/extra_theories/logrootScript.sml` for `LOG`. HOL
introduces `LOG` by `new_specification("LOG", ["LOG"], LOG_exists)`: a constant about which
exactly the specification is known. The Lean rendering is the matching Hilbert choice
`Classical.choose LOG_exists`, as for the reviewed `float_some_qnan` rendering. The
specification does not constrain `holLOG a n` outside `1 < a ∧ 0 < n` (in particular
`holLOG 2 0`), as in HOL; this renders the HOL constant and is not a cross-language
equivalence proof. HOL `SUC p` is `p + 1`.
-/

namespace Flapjack

/-- Witness for `LOG_exists` (Flapjack infrastructure): repeated division by `a`. -/
def holLogWitness (a n : Nat) : Nat :=
  if h : 1 < a ∧ a ≤ n then holLogWitness a (n / a) + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) h.1

theorem holLogWitness_spec (a : Nat) (ha : 1 < a) :
    ∀ n, 0 < n → a ^ holLogWitness a n ≤ n ∧ n < a ^ (holLogWitness a n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro hn
  by_cases han : a ≤ n
  · rw [holLogWitness, dif_pos ⟨ha, han⟩]
    have hm : 0 < n / a := Nat.div_pos han (by omega)
    obtain ⟨h1, h2⟩ := ih (n / a) (Nat.div_lt_self hn ha) hm
    refine ⟨?_, ?_⟩
    · rw [Nat.pow_succ]
      exact Nat.le_trans (Nat.mul_le_mul_right a h1) (Nat.div_mul_le_self n a)
    · rw [Nat.pow_succ]
      have hlt : n < (n / a + 1) * a := by
        have := Nat.div_add_mod n a
        have := Nat.mod_lt n (show a > 0 by omega)
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / a) a]
        omega
      exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right a h2)
  · rw [holLogWitness, dif_neg (by omega)]
    simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one]
    omega

/-- Exact HOL `LOG_exists` (`logrootScript.sml:286-287`). -/
@[hol "HOL/src/num/extra_theories/logrootScript.sml" "LOG_exists"]
theorem holLOGExists : ∃ f : Nat → Nat → Nat, ∀ a n : Nat,
    1 < a ∧ 0 < n → a ^ f a n ≤ n ∧ n < a ^ (f a n + 1) :=
  ⟨holLogWitness, fun a n ⟨ha, hn⟩ => holLogWitness_spec a ha n hn⟩

/-- HOL `LOG` (`logrootScript.sml:289`), the constant of
`new_specification("LOG", ["LOG"], LOG_exists)`, rendered by the matching Hilbert choice. -/
@[hol "HOL/src/num/extra_theories/logrootScript.sml" "LOG"]
noncomputable def holLOG : Nat → Nat → Nat := Classical.choose holLOGExists

/-- Exact HOL `LOG` specification theorem (`logrootScript.sml:289`), the theorem returned by
`new_specification`. -/
@[hol "HOL/src/num/extra_theories/logrootScript.sml" "LOG"]
theorem holLOG_spec : ∀ a n : Nat,
    1 < a ∧ 0 < n → a ^ holLOG a n ≤ n ∧ n < a ^ (holLOG a n + 1) :=
  Classical.choose_spec holLOGExists

/-- Exact HOL `LOG_UNIQUE` (`logrootScript.sml:291-306`). -/
@[hol "HOL/src/num/extra_theories/logrootScript.sml" "LOG_UNIQUE"]
theorem holLOG_UNIQUE : ∀ a n p : Nat, a ^ p ≤ n ∧ n < a ^ (p + 1) → holLOG a n = p := by
  rintro a n p ⟨h1, h2⟩
  have ha : 1 < a := by
    rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
      · simp at h2
      · simp at h1 h2; omega
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.pow_pos (n := p) (by omega)) h1
  obtain ⟨l1, l2⟩ := holLOG_spec a n ⟨ha, hn⟩
  have hmono : ∀ i j, i ≤ j → a ^ i ≤ a ^ j := fun i j hij =>
    Nat.pow_le_pow_right (by omega) hij
  rcases Nat.lt_trichotomy (holLOG a n) p with h | h | h
  · have := hmono (holLOG a n + 1) p h; omega
  · exact h
  · have := hmono (p + 1) (holLOG a n) h; omega

end Flapjack
