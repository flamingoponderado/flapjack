module

public import Flapjack.Misc.Multiword
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Comparison of HOL multiword magnitudes. -/
namespace Flapjack.Misc.Multiword
open Flapjack
open Classical
noncomputable section

/-- HOL LAST of a snoc list (Flapjack helper). -/
private theorem lastSnoc {α : Type} [Nonempty α] (xs : List α) (x : α) : holLast (xs ++ [x]) = x := by
  induction xs with
  | nil => simp [holLast]
  | cons a xs ih =>
    cases xs with
    | nil => simp [holLast]
    | cons b xs => simpa [holLast] using ih

/-- Compare two lists by their final words (Flapjack helper). -/
private theorem cmpSnoc {width : Nat} [NeZero width] (xs ys : List (BitVec width)) (x y : BitVec width) :
    mwCmp (xs ++ [x]) (ys ++ [y]) = if x = y then mwCmp xs ys else some (decide (x < y)) := by
  rw [mwCmp]
  simp [lastSnoc]

/-- A multiword magnitude fits its number of digits (Flapjack helper). -/
private theorem bound {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    mw2n xs < (2 ^ width) ^ xs.length := by
  induction xs with
  | nil => simp [mw2n]
  | cons x xs ih =>
    simp only [mw2n, List.length_cons, pow_succ]
    have d := x.isLt
    have positive : 0 < 2 ^ width := Nat.two_pow_pos width
    nlinarith

/-- Decode a list after appending its most significant word (Flapjack helper). -/
private theorem snocVal {width : Nat} [NeZero width] (xs : List (BitVec width)) (x : BitVec width) :
    mw2n (xs ++ [x]) = mw2n xs + (2 ^ width) ^ xs.length * x.toNat := by
  induction xs with
  | nil => simp [mw2n]
  | cons y ys ih =>
    simp only [List.cons_append, mw2n, ih, List.length_cons, pow_succ]
    ring

/-- Equal-length multiword comparison agrees with the decoded magnitudes. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_cmp_thm"
  (words_as_type_indexed_bitvec)]
theorem mwCmpThm {width : Nat} [NeZero width] : ∀ xs ys : List (BitVec width),
    ys.length = xs.length → mwCmp xs ys =
      if mw2n xs = mw2n ys then none else some (decide (mw2n xs < mw2n ys)) := by
  intro xs ys
  induction n : xs.length using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
    intro len
    simp only [← n] at len ⊢
    rcases List.eq_nil_or_concat xs with empty | ⟨xs', x, eq⟩
    · subst xs
      have : ys = [] := by simpa using len
      subst ys
      rw [mwCmp]
      simp
    · simp only [List.concat_eq_append] at eq
      subst xs
      rcases List.eq_nil_or_concat ys with empty | ⟨ys', y, eq⟩
      · subst ys
        simp at len
      · simp only [List.concat_eq_append] at eq
        subst ys
        simp only [List.length_append, List.length_singleton] at len n
        have len' : ys'.length = xs'.length := by omega
        have recResult := ih xs'.length (by omega) xs' ys' rfl len'
        rw [cmpSnoc, snocVal, snocVal, len']
        by_cases eq : x = y
        · subst y
          simpa using recResult
        · have bx := bound xs'
          have bys := bound ys'
          rw [len'] at bys
          have bpos : 0 < (2 ^ width) ^ xs'.length := pow_pos (Nat.two_pow_pos _) _
          by_cases lt : x < y
          · have digits : x.toNat < y.toNat := lt
            have magnitude : mw2n xs' + (2 ^ width) ^ xs'.length * x.toNat <
                mw2n ys' + (2 ^ width) ^ xs'.length * y.toNat := by nlinarith
            simp [eq, lt, Nat.ne_of_lt magnitude, magnitude]
          · have digits : y.toNat < x.toNat := by
              have ne : x.toNat ≠ y.toNat := by intro h; exact eq (BitVec.eq_of_toNat_eq h)
              have notLt : ¬ x.toNat < y.toNat := lt
              omega
            have magnitude : mw2n ys' + (2 ^ width) ^ xs'.length * y.toNat <
                mw2n xs' + (2 ^ width) ^ xs'.length * x.toNat := by nlinarith
            simp [eq, lt, Nat.ne_of_gt magnitude, Nat.not_lt_of_ge (Nat.le_of_lt magnitude)]

end
end Flapjack.Misc.Multiword
