module

public import Flapjack.Misc.Multiword.DivLemmas

@[expose] public section

/-! The combined multiplication by two single words of HOL's `multiword`
library. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Multiply by `x1` and then by `x2` in one pass, carrying both partial
products. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_by_single2_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwMulBySingle2 {width : Nat} [NeZero width] (x1 x2 : BitVec width) :
    List (BitVec width) → BitVec width → BitVec width → List (BitVec width)
  | [], _, k2 => [k2]
  | y :: ys, k1, k2 =>
    let (y1, k1) := singleMulAdd x1 y k1 0
    let (y2, k2) := singleMulAdd x2 y1 k2 0
    y2 :: mwMulBySingle2 x1 x2 ys k1 k2

/-- A multiplication pass is never empty (Flapjack helper). -/
theorem mwMulPass_ne_nil {width : Nat} [NeZero width] (x : BitVec width)
    (ys zs : List (BitVec width)) (k : BitVec width) : mwMulPass x ys zs k ≠ [] := by
  cases ys <;> simp [mwMulPass]

/-- The general accumulator form of `mw_mul_by_single2_thm` (Flapjack proof). -/
theorem mwMulBySingle2_eq_pass {width : Nat} [NeZero width] (x1 x2 : BitVec width) :
    ∀ (ys : List (BitVec width)) (k1 k2 : BitVec width),
      mwMulBySingle2 x1 x2 ys k1 k2 =
        mwMulPass x2 (mwMulPass x1 ys (k2mw ys.length 0) k1).dropLast
          (k2mw (mwMulPass x1 ys (k2mw ys.length 0) k1).dropLast.length 0) k2 := by
  intro ys
  induction ys with
  | nil => intro k1 k2; simp [mwMulBySingle2, mwMulPass, k2mw]
  | cons y ys ih =>
    intro k1 k2
    rcases h1 : singleMulAdd x1 y k1 0 with ⟨y1, k1'⟩
    rcases h2 : singleMulAdd x2 y1 k2 0 with ⟨y2, k2'⟩
    have ne := mwMulPass_ne_nil x1 ys (k2mw ys.length 0) k1'
    obtain ⟨p, ps, hp⟩ : ∃ p ps, mwMulPass x1 ys (k2mw ys.length 0) k1' = p :: ps := by
      cases e : mwMulPass x1 ys (k2mw ys.length 0) k1' with
      | nil => exact absurd e ne
      | cons a b => exact ⟨a, b, rfl⟩
    have k0 : ∀ n : Nat, (k2mw (n + 1) 0 : List (BitVec width)) = 0 :: k2mw n 0 := by
      intro n; simp [k2mw]
    simp only [mwMulBySingle2, h1, h2, ih, List.length_cons, k0, mwMulPass, holHd,
      List.tail_cons, hp, List.dropLast_cons_cons]

/-- Multiplying by two words in one pass is multiplying twice, dropping the
top digit of the first product. HOL's `FRONT` is rendered by `List.dropLast`;
its argument here, a single-word product, always has at least one digit, so
HOL's unspecified `FRONT []` does not arise. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_by_single2_thm"
  (words_as_type_indexed_bitvec)]
theorem mwMulBySingle2_thm {width : Nat} [NeZero width] {x1 x2 : BitVec width}
    {ys : List (BitVec width)} :
    mwMulBySingle2 x1 x2 ys 0 0 = mwMulBySingle x2 (mwMulBySingle x1 ys).dropLast := by
  rw [mwMulBySingle2_eq_pass]
  rfl

/-- The top three digits of a multiplication pass, computed without storing
the lower digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_pass_top_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwMulPassTop {width : Nat} [NeZero width] (x : BitVec width) :
    List (BitVec width) → BitVec width × BitVec width × BitVec width →
      BitVec width × BitVec width × BitVec width
  | [], (k, k1, k2) => (k, k1, k2)
  | y :: ys, (k, k1, _k2) =>
    let (y1, k') := singleMulAdd x y k 0
    mwMulPassTop x ys (k', y1, k1)

/-- The top three digits of a pass, as a prefix of its reversed digits
(Flapjack proof of the local HOL lemma `mw_mul_pass_top_lemma`). -/
theorem mwMulPassTop_lemma {width : Nat} [NeZero width] (x : BitVec width) :
    ∀ (ys : List (BitVec width)) (k1 k2 k3 : BitVec width),
      [(mwMulPassTop x ys (k1, k2, k3)).1, (mwMulPassTop x ys (k1, k2, k3)).2.1,
        (mwMulPassTop x ys (k1, k2, k3)).2.2] =
      ((mwMulPass x ys (ys.map fun _ => 0) k1).reverse ++ [k2, k3]).take 3 := by
  intro ys
  induction ys with
  | nil => intro k1 k2 k3; simp [mwMulPassTop, mwMulPass]
  | cons y ys ih =>
    intro k1 k2 k3
    rcases h : singleMulAdd x y k1 0 with ⟨y1, k'⟩
    simp only [mwMulPassTop, h, List.map_cons, mwMulPass, holHd, List.tail_cons, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]
    have ne := mwMulPass_ne_nil x ys (ys.map fun _ => 0) k'
    obtain ⟨R, r, hR⟩ : ∃ R r, (mwMulPass x ys (ys.map fun _ => 0) k').reverse = r :: R := by
      cases e : (mwMulPass x ys (ys.map fun _ => 0) k').reverse with
      | nil => simp at e; exact absurd e ne
      | cons a b => exact ⟨b, a, rfl⟩
    rw [hR]
    rcases R with _ | ⟨r2, _ | ⟨r3, R⟩⟩ <;> simp

/-- The leading digits of a multiplication by a single word. HOL's `LAST` is
the reviewed rendering `holLast` and `FRONT` is `List.dropLast`; under the
hypothesis the product has at least three digits, so neither is applied to an
empty list. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_pass_top_thm"
  (words_as_type_indexed_bitvec)]
theorem mwMulPassTop_thm {width : Nat} [NeZero width] {x : BitVec width}
    {ys : List (BitVec width)} :
    1 < ys.length →
      mwMulPassTop x ys (0, 0, 0) =
        (holLast (mwMulBySingle x ys), holLast (mwMulBySingle x ys).dropLast,
          holLast (mwMulBySingle x ys).dropLast.dropLast) := by
  intro h
  have lem := mwMulPassTop_lemma x ys 0 0 0
  have k0 : (k2mw ys.length 0 : List (BitVec width)) = ys.map fun _ => 0 := by
    clear lem h
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [k2mw, ih]
  have hM : mwMulPass x ys (ys.map fun _ => 0) 0 = mwMulBySingle x ys := by
    rw [mwMulBySingle, k0]
  rw [hM] at lem
  have len : (mwMulBySingle x ys).length = ys.length + 1 := length_mwMulBySingle
  generalize mwMulBySingle x ys = M at lem len
  obtain ⟨a, M1, rfl⟩ := List.eq_nil_or_concat M |>.resolve_left (by
    intro e; rw [e] at len; simp at len)
  obtain ⟨b, M2, rfl⟩ := List.eq_nil_or_concat a |>.resolve_left (by
    intro e; rw [e] at len
    simp only [List.concat_eq_append, List.length_append, List.length_nil,
      List.length_singleton] at len
    omega)
  obtain ⟨c, M3, rfl⟩ := List.eq_nil_or_concat b |>.resolve_left (by
    intro e; rw [e] at len
    simp only [List.concat_eq_append, List.length_append, List.length_nil,
      List.length_singleton] at len
    omega)
  simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
    List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.cons.injEq, and_true] at lem
  simp only [List.concat_eq_append, List.dropLast_concat, holLast_append_singleton]
  exact Prod.ext lem.1 (Prod.ext lem.2.1 lem.2.2)

end Flapjack.Misc.Multiword
