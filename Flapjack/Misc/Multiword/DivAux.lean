module

public import Flapjack.Misc.Multiword.DivRange

@[expose] public section

/-! Length lemmas, normalisation clauses and the division main loop. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- A list splits at any position up to its length. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LESS_EQ_LENGTH"]
theorem less_eq_length {α : Type} :
    ∀ (xs : List α) (n : Nat), n ≤ xs.length → ∃ xs1 xs2, xs = xs1 ++ xs2 ∧ xs1.length = n := by
  intro xs n h
  exact ⟨xs.take n, xs.drop n, (List.take_append_drop n xs).symm, List.length_take_of_le h⟩

/-- Addition keeps the length of its first operand. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_add"
  (words_as_type_indexed_bitvec)]
theorem length_mwAdd {width : Nat} [NeZero width] :
    ∀ (xs1 ys : List (BitVec width)) (c : Bool) (qs1 : List (BitVec width)) (c1 : Bool),
      mwAdd xs1 ys c = (qs1, c1) → xs1.length = qs1.length := by
  intro xs1
  induction xs1 with
  | nil =>
    intro ys c qs1 c1 h
    simp only [mwAdd, Prod.mk.injEq] at h
    rw [← h.1]
  | cons x xs ih =>
    intro ys c qs1 c1 h
    simp only [mwAdd] at h
    rcases hz : singleAdd x (holHd ys) c with ⟨z, d⟩
    rcases hr : mwAdd xs ys.tail d with ⟨zs, e⟩
    simp only [hz, hr, Prod.mk.injEq] at h
    rw [← h.1, List.length_cons, List.length_cons, ih _ d zs e hr]

/-- `mw_fix` is no longer than any list of the same length. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_fix_IMP"
  (words_as_type_indexed_bitvec)]
theorem length_mwFix_IMP {width : Nat} [NeZero width] {β : Type} {xs : List (BitVec width)}
    {ys : List β} : xs.length = ys.length → (mwFix xs).length ≤ ys.length := by
  intro h
  rw [← h]
  exact length_mwFix xs

/-- Normalised subtraction is no longer than its first operand. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_subv"
  (words_as_type_indexed_bitvec)]
theorem length_mwSubv {width : Nat} [NeZero width] :
    ∀ (ys xs : List (BitVec width)), xs.length ≤ ys.length → (mwSubv ys xs).length ≤ ys.length := by
  intro ys xs _
  simp only [mwSubv]
  rcases h : mwSub ys xs true with ⟨zs, c⟩
  have := length_mwSub ys xs true zs c h
  exact length_mwFix_IMP this.symm

private theorem singleAdd_zero_false {width : Nat} [NeZero width] (x : BitVec width) :
    singleAdd x 0 false = (x, false) := by
  simp only [singleAdd, b2w, b2n, Prod.mk.injEq]
  have := x.isLt
  constructor
  · simp
  · simp; omega

/-- Adding zero without carry is the identity. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_add_F"
  (words_as_type_indexed_bitvec)]
theorem mwAdd_F {width : Nat} [NeZero width] :
    ∀ xs2 : List (BitVec width), mwAdd xs2 (xs2.map (fun _ => (0 : BitVec width))) false = (xs2, false) := by
  intro xs2
  induction xs2 with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, mwAdd, holHd, List.tail_cons]
    rw [singleAdd_zero_false]
    simp only
    rw [ih]

private theorem mwAddv_nil_false {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwAddv xs [] false = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mwAddv, if_true, singleAdd_zero_false]
    rw [ih]

private theorem length_mwAddv_le {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool), (mwAddv xs ys c).length ≤ xs.length + 1 := by
  intro xs
  induction xs with
  | nil => intro ys c; cases c <;> simp [mwAddv]
  | cons x xs ih =>
    intro ys c
    simp only [mwAddv, List.length_cons]
    have := ih (if ys = [] then ((0 : BitVec width), ys) else (holHd ys, ys.tail)).2
      (singleAdd x (if ys = [] then ((0 : BitVec width), ys) else (holHd ys, ys.tail)).1 c).2
    omega

/-- Addition with a shorter second operand adds at most its length in digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_addv"
  (words_as_type_indexed_bitvec)]
theorem length_mwAddv {width : Nat} [NeZero width] {ys xs : List (BitVec width)} :
    ys.length ≤ xs.length → (mwAddv xs ys false).length ≤ xs.length + ys.length := by
  intro _
  cases ys with
  | nil => rw [mwAddv_nil_false]; simp
  | cons y ys =>
    have := length_mwAddv_le xs (y :: ys) false
    simp only [List.length_cons] at this ⊢
    omega

/-- Multiplication produces the sum of the operand lengths. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_mul"
  (words_as_type_indexed_bitvec)]
theorem length_mwMul {width : Nat} [NeZero width] :
    ∀ (xs ys zs : List (BitVec width)), zs.length = ys.length →
      (mwMul xs ys zs).length = xs.length + ys.length := by
  intro xs
  induction xs with
  | nil => intro ys zs h; simp [mwMul, h]
  | cons x xs ih =>
    intro ys zs h
    simp only [mwMul]
    have l := length_mwMulPass ys zs x 0
    cases hp : mwMulPass x ys zs 0 with
    | nil => rw [hp] at l; simp at l
    | cons p ps =>
      rw [hp] at l
      simp only [List.length_cons, Nat.add_right_cancel_iff] at l
      simp only [holHd, List.tail_cons, List.length_cons, ih ys ps l]
      omega

/-- A list splits with a suffix of any length up to its length. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LESS_EQ_LENGTH_ALT"]
theorem less_eq_length_alt {α : Type} :
    ∀ (xs : List α) (n : Nat), n ≤ xs.length → ∃ ys1 ys2, xs = ys1 ++ ys2 ∧ ys2.length = n := by
  intro xs n h
  refine ⟨xs.take (xs.length - n), xs.drop (xs.length - n),
    (List.take_append_drop _ xs).symm, ?_⟩
  simp only [List.length_drop]
  omega

/-- The division main loop over the remaining low digits `zs1` and the current window `zs2`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_aux_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwDivAux {width : Nat} [NeZero width] (zs1 zs2 ys : List (BitVec width)) :
    List (BitVec width) × List (BitVec width) :=
  if zs1 = [] then ([], zs2) else
    let zs2' := holLast zs1 :: zs2
    let zs1' := zs1.dropLast
    let q := mwDivGuess zs2'.reverse ys.reverse
    let q' := mwDivAdjust q zs2' ys
    let zs2'' := (mwSub zs2' (mwMulBySingle q' ys) true).1
    let (qs, rs) := mwDivAux zs1' zs2''.dropLast ys
    (q' :: qs, rs)
termination_by zs1.length
decreasing_by
  rename_i h
  simp only [List.length_dropLast]
  have : zs1.length ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero e)
  omega

/-- The main loop returns one quotient digit per low digit and a window-length remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_div_aux"
  (words_as_type_indexed_bitvec)]
theorem length_mwDivAux {width : Nat} [NeZero width] :
    ∀ (ts1 ts2 ys qs rs : List (BitVec width)),
      mwDivAux ts1 ts2 ys = (qs, rs) ∧ ts2.length = ys.length →
      rs.length = ys.length ∧ qs.length = ts1.length := by
  intro ts1
  induction h : ts1.length using Nat.strong_induction_on generalizing ts1 with
  | _ n ih =>
    intro ts2 ys qs rs ⟨eq, len⟩
    rw [mwDivAux] at eq
    split at eq
    · rename_i e
      subst e
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      simp_all
    · rename_i ne
      simp only at eq
      generalize hq : mwDivAdjust _ _ ys = q' at eq
      rcases hs : mwSub (holLast ts1 :: ts2) (mwMulBySingle q' ys) true with ⟨w, c⟩
      have lw := length_mwSub _ _ _ _ _ hs
      rw [hs] at eq
      simp only at eq
      rcases hr : mwDivAux ts1.dropLast w.dropLast ys with ⟨qs1, rs1⟩
      rw [hr] at eq
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      have tl : ts1.length ≠ 0 := fun e => ne (List.eq_nil_of_length_eq_zero e)
      obtain ⟨a, b⟩ := ih ts1.dropLast.length (by simp; omega) ts1.dropLast rfl w.dropLast ys qs1 rs1
        ⟨hr, by simp [List.length_dropLast, ← lw, len]⟩
      refine ⟨a, ?_⟩
      simp only [List.length_cons, b, List.length_dropLast]
      omega

private theorem rev_cons_val {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mw2n (x :: xs).reverse = mw2n xs.reverse + dimwords width xs.length * x.toNat := by
  rw [List.reverse_cons, mw2n_msf, List.length_reverse]

/-- Normalisation keeps the divisor in its digits and sets the top bit of its leading digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_clauses"
  (words_as_type_indexed_bitvec)]
theorem d_clauses {width : Nat} [NeZero width] :
    ∀ (vs : List (BitVec width)) (v1 : BitVec width), 0 < v1.toNat →
      0 < (calcD (v1, 1)).toNat ∧
      mw2n (mwMulBySingle (calcD (v1, 1)) (v1 :: vs).reverse) =
        mw2n (mwMulBySingle (calcD (v1, 1)) (v1 :: vs).reverse).dropLast ∧
      2 ^ width / 2 ≤
        (holLast (mwMulBySingle (calcD (v1, 1)) (v1 :: vs).reverse).dropLast).toNat := by
  intro vs v1 vpos
  have v1ne : v1 ≠ 0 := fun e => by subst e; simp at vpos
  have dne := d_lemma2_bis v1 v1 v1ne
  have dpos : 0 < (calcD (v1, 1)).toNat := NOT_0w_bis dne
  generalize hd : calcD (v1, (1 : BitVec width)) = d at dne dpos ⊢
  have l2 := d_lemma2 v1 v1 v1ne
  have l3 := d_lemma3 v1 v1
  simp only at l2 l3
  rw [hd] at l2 l3
  have hb := Nat.two_pow_pos width
  have prod : (d * v1).toNat = d.toNat * v1.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt l3]
  rw [prod] at l2
  obtain ⟨val, len⟩ := mwMulBySingle_lemma d (v1 :: vs).reverse
  rw [rev_cons_val] at val
  simp only [List.length_reverse, List.length_cons] at len
  have hS := mw2n_lt vs.reverse
  rw [List.length_reverse] at hS
  have hD := dimwords_pos (width := width) vs.length
  generalize hM : mwMulBySingle d (v1 :: vs).reverse = M at val len
  -- the value fits below the top digit
  have small : mw2n M < dimwords width M.dropLast.length := by
    rw [List.length_dropLast, len, Nat.add_sub_cancel, dimwords_succ, val]
    have v1lt := v1.isLt
    rcases Nat.lt_or_ge d.toNat 2 with d1 | d2
    · have : d.toNat = 1 := by omega
      rw [this, Nat.one_mul]
      have : dimwords width vs.length * v1.toNat + dimwords width vs.length ≤
          2 ^ width * dimwords width vs.length := by
        rw [Nat.mul_comm (2 ^ width), ← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ v1lt
      omega
    · have l5 := d_lemma5 v1 v1 (by simp only; rw [hd]; exact d2)
      simp only at l5
      rw [hd] at l5
      calc d.toNat * (mw2n vs.reverse + dimwords width vs.length * v1.toNat)
          < d.toNat * (dimwords width vs.length + dimwords width vs.length * v1.toNat) :=
            Nat.mul_lt_mul_of_pos_left (by omega) dpos
        _ = dimwords width vs.length * (d.toNat * (v1.toNat + 1)) := by ring
        _ ≤ dimwords width vs.length * 2 ^ width := Nat.mul_le_mul_left _ l5
        _ = 2 ^ width * dimwords width vs.length := Nat.mul_comm _ _
  have Mne : M ≠ [] := by intro e; rw [e] at len; simp at len
  have front := mw2n_msf_NIL M ⟨Mne, small⟩
  refine ⟨dpos, front, ?_⟩
  -- the top digit of the front is the value divided by `dimwords (LENGTH vs)`
  have Fne : M.dropLast ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [List.length_dropLast, len] at this
    simp at this
  obtain ⟨F, t, hF⟩ := List.eq_nil_or_concat M.dropLast |>.resolve_left Fne
  rw [List.concat_eq_append] at hF
  have Flen : F.length = vs.length := by
    have := congrArg List.length hF
    rw [List.length_dropLast, len, List.length_append] at this
    simp at this; omega
  rw [hF, holLast_append_singleton]
  have v2 : mw2n M.dropLast = mw2n F + dimwords width vs.length * t.toNat := by
    rw [hF, mw2n_msf, Flen]
  have hF2 := mw2n_lt F
  rw [Flen] at hF2
  rw [← front, val] at v2
  -- d * v1 * D ≤ d * Y = F + D * t < D * (t + 1)
  have : dimwords width vs.length * (d.toNat * v1.toNat) <
      dimwords width vs.length * (t.toNat + 1) := by
    have e1 : dimwords width vs.length * (d.toNat * v1.toNat) ≤
        d.toNat * (mw2n vs.reverse + dimwords width vs.length * v1.toNat) := by
      rw [Nat.mul_add]
      have : dimwords width vs.length * (d.toNat * v1.toNat) =
          d.toNat * (dimwords width vs.length * v1.toNat) := by ring
      omega
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-- The normalised divisor keeps a nonzero leading digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml"
  "LAST_FRONT_mw_mul_by_single_NOT_ZERO" (words_as_type_indexed_bitvec)]
theorem last_front_mwMulBySingle_NOT_ZERO {width : Nat} [NeZero width] {ys : List (BitVec width)} :
    mwOk ys ∧ ys ≠ [] ∧ 2 < 2 ^ width →
      holLast (mwMulBySingle (calcD (holLast ys, 1)) ys).dropLast ≠ 0 := by
  rintro ⟨ok, ne, big⟩
  obtain ⟨vs', v1, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left ne
  rw [List.concat_eq_append] at ok ⊢
  have v1ne : v1 ≠ 0 := (mwOk_snoc vs' v1).mp ok
  rw [holLast_append_singleton]
  have := (d_clauses vs'.reverse v1 (NOT_0w_bis v1ne)).2.2
  rw [List.reverse_cons, List.reverse_reverse] at this
  intro z
  rw [z] at this
  simp at this
  omega

end Flapjack.Misc.Multiword
