module

public import Flapjack.Misc.Multiword.Div
public import Flapjack.Misc.Integer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Signed multiword division and the arithmetic operation dispatcher. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Signed division with remainder, rounding the quotient towards negative infinity. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_divmod_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiDivmod {width : Nat} [NeZero width] :
    Bool × List (BitVec width) → Bool × List (BitVec width) →
      Bool × (Bool × List (BitVec width)) × Bool × List (BitVec width)
  | (s, xs), (t, ys) =>
    let (res, mod, c) := mwDiv xs ys
    let res := mwFix res
    let mod := mwFix mod
    let res := if s = t then res else if mod = [] then res else mwAddv res [] true
    let res_sign := if res = [] then false else s != t
    let mod := if s = t then mod else if mod = [] then mod else mwSubv ys mod
    let mod_sign := if mod = [] then false else t
    (c, (res_sign, res), mod_sign, mod)

/-- Signed quotient. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_div_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiDiv {width : Nat} [NeZero width] (s_xs t_ys : Bool × List (BitVec width)) :
    Bool × List (BitVec width) :=
  (mwiDivmod s_xs t_ys).2.1

/-- Signed remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_mod_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiMod {width : Nat} [NeZero width] (s_xs t_ys : Bool × List (BitVec width)) :
    Bool × List (BitVec width) :=
  (mwiDivmod s_xs t_ys).2.2

private theorem mwFix_eq_n2mw {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    mwFix xs = n2mw (mw2n xs) := by
  rw [mwOk_eq_n2mw _ (mwOk_fix xs), mw2n_mwFix]

private theorem mwAddv_n2mw {width : Nat} [NeZero width] (n : Nat) :
    mwAddv (n2mw n : List (BitVec width)) [] true = n2mw (n + 1) := by
  have ok : mwOk (mwAddv (n2mw n : List (BitVec width)) [] true) :=
    mwOk_addv _ _ _ (mwOk_n2mw n) (by simp [mwOk])
  rw [mwOk_eq_n2mw _ ok, mwAddv_thm _ _ _ (by simp), mw2n_n2mw]
  simp [mw2n, b2n]

private theorem mwSubv_n2mw {width : Nat} [NeZero width] (a b : Nat) (h : b ≤ a) :
    mwSubv (n2mw a : List (BitVec width)) (n2mw b) = n2mw (a - b) := by
  have len : (n2mw b : List (BitVec width)).length ≤ (n2mw a).length :=
    mw2n_LESS _ _ ⟨mwOk_n2mw _, mwOk_n2mw _, by rw [mw2n_n2mw, mw2n_n2mw]; exact h⟩
  rw [mwOk_eq_n2mw (mwSubv _ _) (by simp only [mwSubv]; exact mwOk_fix _),
    mwSubv_thm _ _ (by rw [mw2n_n2mw, mw2n_n2mw]; exact h) len, mw2n_n2mw, mw2n_n2mw]

private theorem n2mw_eq_nil {width : Nat} [NeZero width] (n : Nat) :
    (n2mw n : List (BitVec width)) = [] ↔ n = 0 := n2mw_NIL n

/-- Signed division of `i2mw` numbers implements HOL's integer division and remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_divmod_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiDivmod_thm {width : Nat} [NeZero width] :
    ∀ (i j : Int), j ≠ 0 →
      mwiDivmod (i2mw i : Bool × List (BitVec width)) (i2mw j) =
        (true, i2mw (holIntDiv i j), i2mw (holIntMod i j)) := by
  intro i j jne
  have bpos : 0 < j.natAbs := Int.natAbs_pos.mpr jne
  rcases hd : mwDiv (n2mw i.natAbs : List (BitVec width)) (n2mw j.natAbs) with ⟨r1, r2, r3⟩
  obtain ⟨v1, v2, c, _⟩ := mwDiv_thm _ _ r2 r1 r3
    ⟨hd, by rw [mw2n_n2mw]; omega⟩
  rw [mw2n_n2mw, mw2n_n2mw] at v1 v2
  simp only [i2mw, mwiDivmod, hd, mwFix_eq_n2mw, v1, v2, c]
  rw [holIntMod_spec i j jne]
  generalize hDiv : holIntDiv i j = D
  have hdm := Nat.div_add_mod i.natAbs j.natAbs
  have hml := Nat.mod_lt i.natAbs bpos
  rcases Int.natAbs_eq i with hi | hi <;> rcases Int.natAbs_eq j with hj | hj <;>
    generalize i.natAbs = a at * <;> generalize j.natAbs = b at * <;> subst hi <;> subst hj
  all_goals
    first
      | rw [holIntDiv_ofNat_ofNat a b bpos] at hDiv
      | rw [holIntDiv_ofNat_neg a b bpos] at hDiv
      | rw [holIntDiv_neg_ofNat a b bpos] at hDiv
      | rw [holIntDiv_neg_neg a b bpos] at hDiv
    try simp only [← Int.natCast_div, ← Int.natCast_mod] at hDiv
    have em : (Nat.cast (b * (a / b) + a % b) : Int) = a := congrArg Nat.cast hdm
    generalize a / b = q at *
    generalize a % b = r at *
    push_cast at em
    simp only [Prod.mk.injEq, true_and]
  · -- nonnegative / positive
    have hD : D = (q : Int) := hDiv.symm
    subst hD
    have hM : (a : Int) - (q : Int) * b = r := by linarith
    have na : ¬ ((a : Int) < 0) := by omega
    have nb : ¬ ((b : Int) < 0) := by omega
    rw [hM]
    simp only [na, nb, decide_false, if_true, Int.natAbs_natCast, Nat.cast_nonneg,
      not_lt.mpr, decide_false]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
  · -- nonnegative / negative
    have na : ¬ ((a : Int) < 0) := by omega
    have nb : (-(b : Int)) < 0 := by omega
    simp only [na, nb, decide_false, decide_true]
    by_cases hr : r = 0
    · have hD : D = -(q : Int) := by rw [← hDiv, if_pos hr]; simp
      subst hD; subst hr
      have hM : (a : Int) - -(q : Int) * -(b : Int) = 0 := by linarith
      rw [hM]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
      cases q <;> simp
    · have hD : D = -((q + 1 : Nat) : Int) := by rw [← hDiv, if_neg hr]; push_cast; ring
      subst hD
      have hM : (a : Int) - -((q + 1 : Nat) : Int) * -(b : Int) = -((b - r : Nat) : Int) := by
        push_cast [Nat.cast_sub (Nat.le_of_lt hml)]; linarith
      rw [hM]
      have sub := mwSubv_n2mw (width := width) b r (Nat.le_of_lt hml)
      simp only [hr, n2mw_eq_nil, if_false, mwAddv_n2mw, sub, Int.natAbs_neg, Int.natAbs_natCast]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
      all_goals omega
  · -- nonpositive / positive
    have nb : ¬ ((b : Int) < 0) := by omega
    by_cases a0 : a = 0
    · subst a0
      have hq : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h | h
        · exact h
        · nlinarith
      have hr : r = 0 := by subst hq; omega
      subst hq; subst hr
      have hD : D = 0 := by rw [← hDiv]; simp
      subst hD
      simp [n2mw_eq_nil]
    have na : (-(a : Int)) < 0 := by omega
    simp only [na, nb, decide_false, decide_true]
    by_cases hr : r = 0
    · have hD : D = -(q : Int) := by rw [← hDiv, if_pos hr]; simp
      subst hD; subst hr
      have qpos : q ≠ 0 := by intro hq; subst hq; simp at em; omega
      have hM : -(a : Int) - -(q : Int) * (b : Int) = 0 := by linarith
      rw [hM]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
      omega
    · have hD : D = -((q + 1 : Nat) : Int) := by rw [← hDiv, if_neg hr]; push_cast; ring
      subst hD
      have hM : -(a : Int) - -((q + 1 : Nat) : Int) * (b : Int) = ((b - r : Nat) : Int) := by
        push_cast [Nat.cast_sub (Nat.le_of_lt hml)]; linarith
      rw [hM]
      have sub := mwSubv_n2mw (width := width) b r (Nat.le_of_lt hml)
      simp only [hr, n2mw_eq_nil, if_false, mwAddv_n2mw, sub, Int.natAbs_neg, Int.natAbs_natCast]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
      omega
  · -- nonpositive / negative
    have nb : (-(b : Int)) < 0 := by omega
    by_cases a0 : a = 0
    · subst a0
      have hq : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h | h
        · exact h
        · nlinarith
      have hr : r = 0 := by subst hq; omega
      subst hq; subst hr
      have hD : D = 0 := by rw [← hDiv]; simp
      subst hD
      simp [n2mw_eq_nil]
    have na : (-(a : Int)) < 0 := by omega
    have hD : D = (q : Int) := hDiv.symm
    subst hD
    have hM : -(a : Int) - (q : Int) * -(b : Int) = -(r : Int) := by linarith
    rw [hM]
    simp only [na, nb, decide_true, if_true, Int.natAbs_neg, Int.natAbs_natCast]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (try split) <;> simp_all [n2mw_eq_nil]
    omega

/-- Integer semantics of the multiword operations; HOL's `/` and `%` are the
specified `int_div` and `int_mod`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "int_op_def"]
noncomputable def mwIntOp : MwOp → Int → Int → Int
  | .add, i, j => i + j
  | .sub, i, j => i - j
  | .mul, i, j => i * j
  | .div, i, j => holIntDiv i j
  | .mod, i, j => holIntMod i j
  | .lt, i, j => if i < j then 1 else 0
  | .eq, i, j => if i = j then 1 else 0
  | .dec, _, _ => 0

open Classical in
/-- The multiword operation dispatcher; the decimal operation returns zero here. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_op_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiOp {width : Nat} [NeZero width] :
    MwOp → Bool × List (BitVec width) → Bool × List (BitVec width) → Bool × List (BitVec width)
  | .add, s_xs, t_ys => mwiAdd s_xs t_ys
  | .sub, s_xs, t_ys => mwiSub s_xs t_ys
  | .mul, s_xs, t_ys => mwiMul s_xs t_ys
  | .div, s_xs, t_ys => mwiDiv s_xs t_ys
  | .mod, s_xs, t_ys => mwiMod s_xs t_ys
  | .lt, s_xs, t_ys => i2mw (if mwiLt s_xs t_ys then 1 else 0)
  | .eq, s_xs, t_ys => i2mw (if mwiEq s_xs t_ys then 1 else 0)
  | .dec, _, _ => (false, [])

/-- Each multiword operation on `i2mw` operands implements its integer operation. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_op_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiOp_thm {width : Nat} [NeZero width] :
    ∀ (op : MwOp) (i j : Int), (op = .div ∨ op = .mod → j ≠ 0) →
      mwiOp op (i2mw i : Bool × List (BitVec width)) (i2mw j) = i2mw (mwIntOp op i j) := by
  intro op i j h
  cases op with
  | add => exact mwiAdd_thm i j
  | sub => exact mwiSub_thm i j
  | mul => exact mwiMul_thm i j
  | div => simp only [mwiOp, mwiDiv, mwiDivmod_thm i j (h (Or.inl rfl)), mwIntOp]
  | mod => simp only [mwiOp, mwiMod, mwiDivmod_thm i j (h (Or.inr rfl)), mwIntOp]
  | lt =>
    simp only [mwiOp, mwIntOp, mwiLt, mwiCompare_thm]
    by_cases e : i = j
    · simp [e]
    · by_cases l : i < j <;> simp [e, l]
  | eq =>
    simp only [mwiOp, mwIntOp, mwiEq, mwiCompare_thm]
    by_cases e : i = j <;> simp [e]
  | dec => simp [mwiOp, mwIntOp, i2mw, n2mw]

end Flapjack.Misc.Multiword
