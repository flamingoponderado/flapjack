module

public import Flapjack.Misc.Multiword.CompareSigned
public import Flapjack.Misc.Tailrec
public import Flapjack.Misc.ListEl
public import Flapjack.Misc.Multiword.SingleWord

@[expose] public section

/-! Machine-code-style comparison functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_cmp` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCmpStep {width : Nat} [NeZero width] :
    Nat × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r10, xs, ys) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r10, xs, ys), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r8 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r10.toNat) < (ys.length))
      let r9 := holEl (r10.toNat) ys
      if r8 = r9 then
        (.inl (l - 1, r10, xs, ys), cond ∧ (l ≠ 0))
      else
        if r8 < r9 then
          (let r10 := (1 : BitVec width)
          (.inr (l, r10, xs, ys), cond))
        else
          (let r10 := (2 : BitVec width)
          (.inr (l, r10, xs, ys), cond)))

/-- HOL `mc_cmp`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCmp {width : Nat} [NeZero width] :
    Nat × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcCmpStep

/-- The precondition of `mc_cmp`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_pre"
  (words_as_type_indexed_bitvec)]
def mcCmpPre {width : Nat} [NeZero width] : Nat × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width)) mcCmpStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmp_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcCmp (l, r10, xs, ys) =
      if r10 = (0 : BitVec width) then
        (l, r10, xs, ys)
      else
        (let r10 := r10 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) xs
        let r9 := holEl (r10.toNat) ys
        if r8 = r9 then
          mcCmp (l - 1, r10, xs, ys)
        else
          if r8 < r9 then
            (let r10 := (1 : BitVec width)
            (l, r10, xs, ys))
          else
            (let r10 := (2 : BitVec width)
            (l, r10, xs, ys))) := by
  unfold mcCmp
  rw [holShortTailrec_eq_elim]
  simp only [mcCmpStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmpPre_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcCmpPre (l, r10, xs, ys) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r8 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r10.toNat) < (ys.length))
        let r9 := holEl (r10.toNat) ys
        if r8 = r9 then
          mcCmpPre (l - 1, r10, xs, ys) ∧ (cond ∧ (l ≠ 0))
        else
          if r8 < r9 then
            (let _r10 := (1 : BitVec width)
            cond)
          else
            (let _r10 := (2 : BitVec width)
            cond)) := by
  unfold mcCmpPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCmpStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_compare` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCompareStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r10, r11, xs, ys) =>
    if r10 < r11 then
      (let r10 := (1 : BitVec width)
      (.inr (l, r10, xs, ys), True))
    else
      if r11 < r10 then
        (let r10 := (2 : BitVec width)
        (.inr (l, r10, xs, ys), True))
      else
        (let cond := (mcCmpPre (l - 1, r10, xs, ys)) ∧ (l ≠ 0)
        let (l, r10, xs, ys) := mcCmp (l - 1, r10, xs, ys)
        (.inr (l, r10, xs, ys), cond))

/-- HOL `mc_compare`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_compare"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCompare {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcCompareStep

/-- The precondition of `mc_compare`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_compare_pre"
  (words_as_type_indexed_bitvec)]
def mcComparePre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width)) mcCompareStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_compare`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_compare_def"
  (words_as_type_indexed_bitvec)]
theorem mcCompare_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcCompare (l, r10, r11, xs, ys) =
      if r10 < r11 then
        (let r10 := (1 : BitVec width)
        (l, r10, xs, ys))
      else
        if r11 < r10 then
          (let r10 := (2 : BitVec width)
          (l, r10, xs, ys))
        else
          (let (l, r10, xs, ys) := mcCmp (l - 1, r10, xs, ys)
          (l, r10, xs, ys)) := by
  unfold mcCompare
  rw [holShortTailrec_eq_elim]
  simp only [mcCompareStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_compare`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_compare_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcComparePre_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcComparePre (l, r10, r11, xs, ys) ↔
      if r10 < r11 then
        (let _r10 := (1 : BitVec width)
        True)
      else
        if r11 < r10 then
          (let _r10 := (2 : BitVec width)
          True)
        else
          (let cond := (mcCmpPre (l - 1, r10, xs, ys)) ∧ (l ≠ 0)
          let (_l, _r10, _xs, _ys) := mcCmp (l - 1, r10, xs, ys)
          cond) := by
  unfold mcComparePre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCompareStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_icompare` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIcompareStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r10, r11, xs, ys) =>
    if (r10 &&& (1 : BitVec width)) = (0 : BitVec width) then
      if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
        (let r10 := r10 >>> 1
        let r11 := r11 >>> 1
        let cond := mcComparePre (l, r10, r11, xs, ys)
        let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
        (.inr (l, r10, xs, ys), cond))
      else
        (let r10 := (2 : BitVec width)
        (.inr (l, r10, xs, ys), True))
    else
      if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
        (let r10 := (1 : BitVec width)
        (.inr (l, r10, xs, ys), True))
      else
        (let r10 := r10 >>> 1
        let r11 := r11 >>> 1
        let cond := mcComparePre (l, r10, r11, xs, ys)
        let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
        if r10 = (0 : BitVec width) then
          (.inr (l, r10, xs, ys), cond)
        else
          (let r10 := r10 ^^^ (3 : BitVec width)
          (.inr (l, r10, xs, ys), cond)))

/-- HOL `mc_icompare`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icompare"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIcompare {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIcompareStep

/-- The precondition of `mc_icompare`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icompare_pre"
  (words_as_type_indexed_bitvec)]
def mcIcomparePre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width)) mcIcompareStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_icompare`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icompare_def"
  (words_as_type_indexed_bitvec)]
theorem mcIcompare_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIcompare (l, r10, r11, xs, ys) =
      if (r10 &&& (1 : BitVec width)) = (0 : BitVec width) then
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          (let r10 := r10 >>> 1
          let r11 := r11 >>> 1
          let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
          (l, r10, xs, ys))
        else
          (let r10 := (2 : BitVec width)
          (l, r10, xs, ys))
      else
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          (let r10 := (1 : BitVec width)
          (l, r10, xs, ys))
        else
          (let r10 := r10 >>> 1
          let r11 := r11 >>> 1
          let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
          if r10 = (0 : BitVec width) then
            (l, r10, xs, ys)
          else
            (let r10 := r10 ^^^ (3 : BitVec width)
            (l, r10, xs, ys))) := by
  unfold mcIcompare
  rw [holShortTailrec_eq_elim]
  simp only [mcIcompareStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_icompare`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icompare_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIcomparePre_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIcomparePre (l, r10, r11, xs, ys) ↔
      if (r10 &&& (1 : BitVec width)) = (0 : BitVec width) then
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          (let r10 := r10 >>> 1
          let r11 := r11 >>> 1
          let cond := mcComparePre (l, r10, r11, xs, ys)
          let (_l, _r10, _xs, _ys) := mcCompare (l, r10, r11, xs, ys)
          cond)
        else
          (let _r10 := (2 : BitVec width)
          True)
      else
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          (let _r10 := (1 : BitVec width)
          True)
        else
          (let r10 := r10 >>> 1
          let r11 := r11 >>> 1
          let cond := mcComparePre (l, r10, r11, xs, ys)
          let (_l, r10, _xs, _ys) := mcCompare (l, r10, r11, xs, ys)
          if r10 = (0 : BitVec width) then
            cond
          else
            (let _r10 := r10 ^^^ (3 : BitVec width)
            cond)) := by
  unfold mcIcomparePre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIcompareStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
