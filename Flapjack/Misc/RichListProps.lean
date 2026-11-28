module

public import Flapjack.Misc.RichList
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# `splitP` position facts

Counterparts of `SPLITP_TAKE_DROP` and `FST_SPLITP_DROP` from
`cakeml/misc/miscScript.sml`. HOL's total `EL` is rendered by `holEl`, whose
`Flapjack.Misc.ListEl` import lives here rather than in `Flapjack.Misc.RichList`
so that the five modules importing the latter keep their simp sets.
-/

namespace Flapjack

/-- Original `SPLITP_TAKE_DROP`: a split at the first satisfying element is the
take/drop pair at that index. -/
@[hol "cakeml/misc/miscScript.sml" "SPLITP_TAKE_DROP"
  (total_function_inhabitants := [α])]
theorem splitpTakeDrop {α : Type} [Nonempty α] (P : α → Bool) (i : Nat) (l : List α)
    (h1 : (l.take i).all (fun x => !(P x)) = true) (h2 : P (holEl i l) = true) :
    splitP P l = (l.take i, l.drop i) := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp [splitP]
    | succ k =>
      simp [splitP]
  | cons a as ih =>
    cases i with
    | zero =>
      have hpa : P a = true := by simpa only [holEl, holHd] using h2
      rw [splitP, if_pos hpa]
      simp
    | succ k =>
      have hpk : P a = false := by
        simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at h1
        simpa using h1.1
      have h1' : (as.take k).all (fun x => !(P x)) = true := by
        simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at h1
        exact h1.2
      have h2' : P (holEl k as) = true := by
        simpa only [holEl_cons_succ] using h2
      rw [splitP, if_neg (by simp [hpk]), ih k h1' h2']
      simp only [List.take_succ_cons, List.drop_succ_cons]

/-- Original `FST_SPLITP_DROP`: the consumed prefix of a split continues through
the split of the dropped part. -/
@[hol "cakeml/misc/miscScript.sml" "FST_SPLITP_DROP"]
theorem fstSplitpDrop {α : Type} (P : α → Bool) (n : Nat) (l : List α)
    (h : (l.take n).all (fun x => !(P x)) = true) :
    (splitP P l).1 = l.take n ++ (splitP P (l.drop n)).1 := by
  induction n generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp [splitP]
    | cons a as =>
      have hpa : P a = false := by
        simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at h
        simpa using h.1
      have h' : (as.take k).all (fun x => !(P x)) = true := by
        simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at h
        exact h.2
      rw [splitP, if_neg (by simp [hpa])]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih as h']

end Flapjack
