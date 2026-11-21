module

public import Flapjack.Misc.Multiword.AddSub

@[expose] public section

/-! Multiword multiplication, unsigned and signed. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Multiply-accumulate of single words, through a two-word addition. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_mul_add_def"
  (words_as_type_indexed_bitvec)]
noncomputable def singleMulAdd {width : Nat} [NeZero width] (p q k s : BitVec width) :
    BitVec width × BitVec width :=
  let (x, kc) := singleMul p q k
  let (zs, _) := mwAdd [x, kc] [s, 0] false
  (holHd zs, holHd zs.tail)

/-- One row of schoolbook multiplication, accumulated into `zs`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_pass_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwMulPass {width : Nat} [NeZero width] (x : BitVec width) :
    List (BitVec width) → List (BitVec width) → BitVec width → List (BitVec width)
  | [], _, k => [k]
  | y :: ys, zs, k =>
    let (y1, k1) := singleMulAdd x y k (holHd zs)
    y1 :: mwMulPass x ys zs.tail k1

/-- Schoolbook multiplication accumulated into `zs`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwMul {width : Nat} [NeZero width] :
    List (BitVec width) → List (BitVec width) → List (BitVec width) → List (BitVec width)
  | [], _, zs => zs
  | x :: xs, ys, zs =>
    let zs2 := mwMulPass x ys zs 0
    holHd zs2 :: mwMul xs ys zs2.tail

open Classical in
/-- Signed multiplication; the sign type is arbitrary, as in HOL. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_mul_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiMul {width : Nat} [NeZero width] {β : Type} :
    β × List (BitVec width) → β × List (BitVec width) → Bool × List (BitVec width)
  | (s, xs), (t, ys) =>
    if xs = [] ∨ ys = [] then (false, [])
    else (decide (s ≠ t), mwFix (mwMul xs ys (ys.map (fun _ => (0 : BitVec width)))))

private theorem sq_bound (a : Nat) : a * a + 2 * a < (a + 1) * (a + 1) := by
  have : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  omega

private theorem word_sq_bound {width : Nat} :
    (2 ^ width - 1) * (2 ^ width - 1) + 2 * (2 ^ width - 1) < 2 ^ width * 2 ^ width := by
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ width = a + 1 := ⟨2 ^ width - 1, by omega⟩
  rw [ha, Nat.add_sub_cancel]
  exact sq_bound a

private theorem singleMul_thm {width : Nat} [NeZero width] (x y k z l : BitVec width)
    (h : singleMul x y k = (z, l)) :
    z.toNat + 2 ^ width * l.toNat = x.toNat * y.toNat + k.toNat := by
  simp only [singleMul, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  have hx := x.isLt
  have hy := y.isLt
  have hk := k.isLt
  have prod : x.toNat * y.toNat ≤ (2 ^ width - 1) * (2 ^ width - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have sq := word_sq_bound (width := width)
  have small : (x.toNat * y.toNat + k.toNat) / 2 ^ width < 2 ^ width :=
    (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_add_mod]
  exact Nat.mod_add_div _ _

/-- Single-word multiply-accumulate never overflows two words. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_mul_add_thm"
  (words_as_type_indexed_bitvec)]
theorem singleMulAdd_thm {width : Nat} [NeZero width] :
    ∀ (p q k1 k2 x1 x2 : BitVec width), singleMulAdd p q k1 k2 = (x1, x2) →
      x1.toNat + 2 ^ width * x2.toNat = p.toNat * q.toNat + k1.toNat + k2.toNat := by
  intro p q k1 k2 x1 x2 h
  rcases hm : singleMul p q k1 with ⟨x, kc⟩
  have mul := singleMul_thm p q k1 x kc hm
  rcases h1 : singleAdd x k2 false with ⟨z1, c1⟩
  rcases h2 : singleAdd kc 0 c1 with ⟨z2, c2⟩
  have a1 := singleAdd_thm x k2 z1 false c1 h1
  have a2 := singleAdd_thm kc 0 z2 c1 c2 h2
  simp only [singleMulAdd, hm, mwAdd, holHd, List.tail_cons, h1, h2, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  have hp := p.isLt
  have hq := q.isLt
  have hk1 := k1.isLt
  have hk2 := k2.isLt
  have prod : p.toNat * q.toNat ≤ (2 ^ width - 1) * (2 ^ width - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have sq := word_sq_bound (width := width)
  have z0 : (0 : BitVec width).toNat = 0 := by simp
  rw [z0, Nat.add_zero] at a2
  have scaled := congrArg (2 ^ width * ·) a2
  simp only [Nat.mul_add, ← Nat.mul_assoc] at scaled
  cases c1 <;> cases c2 <;> simp only [b2n, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at a1 a2 scaled ⊢ <;>
    omega

private theorem mwMulPass_thm {width : Nat} [NeZero width] (x : BitVec width) :
    ∀ (ys zs : List (BitVec width)) (k : BitVec width), ys.length = zs.length →
      mw2n (mwMulPass x ys zs k) = x.toNat * mw2n ys + mw2n zs + k.toNat ∧
        (mwMulPass x ys zs k).length = ys.length + 1 := by
  intro ys
  induction ys with
  | nil =>
    intro zs k len
    have : zs = [] := List.eq_nil_of_length_eq_zero len.symm
    subst this
    simp [mwMulPass, mw2n]
  | cons y ys ih =>
    intro zs k len
    cases zs with
    | nil => simp at len
    | cons z zs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [mwMulPass, holHd, List.tail_cons]
      rcases h : singleMulAdd x y k z with ⟨y1, k1⟩
      have one := singleMulAdd_thm x y k z y1 k1 h
      obtain ⟨val, l⟩ := ih zs k1 len
      refine ⟨?_, by simp [l]⟩
      simp only [mw2n, val]
      simp only [Nat.mul_add]
      have e : x.toNat * (2 ^ width * mw2n ys) = 2 ^ width * (x.toNat * mw2n ys) :=
        Nat.mul_left_comm _ _ _
      omega

/-- Schoolbook multiplication computes the accumulated product. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_thm"
  (words_as_type_indexed_bitvec)]
theorem mwMul_thm {width : Nat} [NeZero width] :
    ∀ (xs ys zs : List (BitVec width)), ys.length = zs.length →
      mw2n (mwMul xs ys zs) = mw2n xs * mw2n ys + mw2n zs := by
  intro xs
  induction xs with
  | nil => intro ys zs _; simp [mwMul, mw2n]
  | cons x xs ih =>
    intro ys zs len
    obtain ⟨val, l⟩ := mwMulPass_thm x ys zs 0 len
    simp only [mwMul]
    cases hq : mwMulPass x ys zs 0 with
    | nil => rw [hq] at l; simp at l
    | cons q qs =>
      rw [hq] at val l
      simp only [List.length_cons, Nat.add_right_cancel_iff] at l
      simp only [holHd, List.tail_cons, mw2n, ih ys qs (by omega)]
      have z0 : (0 : BitVec width).toNat = 0 := by simp
      simp only [mw2n, z0, Nat.add_zero] at val
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
      omega

private theorem mw2n_map_zero {width : Nat} [NeZero width] :
    ∀ ys : List (BitVec width), mw2n (ys.map (fun _ => (0 : BitVec width))) = 0 := by
  intro ys
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, mw2n, ih]; simp

/-- Signed multiword multiplication implements integer multiplication. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_mul_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiMul_thm {width : Nat} [NeZero width] :
    ∀ (i j : Int), mwiMul (i2mw i : Bool × List (BitVec width)) (i2mw j) = i2mw (i * j) := by
  intro i j
  simp only [i2mw, mwiMul]
  have n0 : (n2mw 0 : List (BitVec width)) = [] := (n2mw_NIL 0).mpr rfl
  by_cases i0 : i = 0
  · subst i0; simp [n0]
  by_cases j0 : j = 0
  · subst j0; simp [n0]
  have ne1 : (n2mw i.natAbs : List (BitVec width)) ≠ [] := by
    rw [ne_eq, n2mw_NIL]; omega
  have ne2 : (n2mw j.natAbs : List (BitVec width)) ≠ [] := by
    rw [ne_eq, n2mw_NIL]; omega
  simp only [ne1, ne2, or_self, if_false]
  congr 1
  · rcases Int.lt_or_gt_of_ne i0 with hi | hi <;> rcases Int.lt_or_gt_of_ne j0 with hj | hj
    · have := Int.mul_pos_of_neg_of_neg hi hj
      simp [hi, hj, show ¬ i * j < 0 by omega]
    · have := Int.mul_neg_of_neg_of_pos hi hj
      simp [hi, show ¬ j < 0 by omega, this]
    · have := Int.mul_neg_of_pos_of_neg hi hj
      simp [show ¬ i < 0 by omega, hj, this]
    · have := Int.mul_pos hi hj
      simp [show ¬ i < 0 by omega, show ¬ j < 0 by omega, show ¬ i * j < 0 by omega]
  · rw [mwOk_eq_n2mw _ (mwOk_fix _), mw2n_mwFix,
      mwMul_thm _ _ _ (by simp), mw2n_map_zero, Nat.add_zero, mw2n_n2mw, mw2n_n2mw,
      Int.natAbs_mul]
end Flapjack.Misc.Multiword
