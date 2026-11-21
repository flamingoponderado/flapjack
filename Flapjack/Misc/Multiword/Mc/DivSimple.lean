module

public import Flapjack.Misc.Multiword.Mc.Mul

@[expose] public section

/-! Machine-code-style simple division and the normalisation factor functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_single_div` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSingleDivStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r2, r9) =>
    (let cond := singleDivPre r2 r0 r9
    let (r0, r2) := singleDiv r2 r0 r9
    (.inr (r0, r2, r9), cond))

/-- HOL `mc_single_div`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_div"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSingleDiv {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcSingleDivStep

/-- The precondition of `mc_single_div`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_div_pre"
  (words_as_type_indexed_bitvec)]
def mcSingleDivPre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcSingleDivStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_single_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_div_def" 1504
  (words_as_type_indexed_bitvec)]
theorem mcSingleDiv_def {width : Nat} [NeZero width] {r0 : BitVec width} {r2 : BitVec width} {r9 : BitVec width} :
    mcSingleDiv (r0, r2, r9) =
      (let (r0, r2) := singleDiv r2 r0 r9
      (r0, r2, r9)) := by
  unfold mcSingleDiv
  rw [holShortTailrec_eq_elim]
  simp only [mcSingleDivStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_single_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_div_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSingleDivPre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r2 : BitVec width} {r9 : BitVec width} :
    mcSingleDivPre (r0, r2, r9) ↔
      (let cond := singleDivPre r2 r0 r9
      let (_r0, _r2) := singleDiv r2 r0 r9
      cond) := by
  unfold mcSingleDivPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSingleDivStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_simple_div` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSimpleDivStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r2, r9, r10, xs, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r2, r9, r10, xs, zs), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r0 := holEl (r10.toNat) xs
      let cond := cond ∧ (mcSingleDivPre (r0, r2, r9))
      let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r0
      (.inl (l - 1, r2, r9, r10, xs, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_simple_div`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSimpleDiv {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcSimpleDivStep

/-- The precondition of `mc_simple_div`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div_pre"
  (words_as_type_indexed_bitvec)]
def mcSimpleDivPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcSimpleDivStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_simple_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div_def"
  (words_as_type_indexed_bitvec)]
theorem mcSimpleDiv_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcSimpleDiv (l, r2, r9, r10, xs, zs) =
      if r10 = (0 : BitVec width) then
        (l, r2, r9, r10, xs, zs)
      else
        (let r10 := r10 - (1 : BitVec width)
        let r0 := holEl (r10.toNat) xs
        let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
        let zs := zs.set (r10.toNat) r0
        mcSimpleDiv (l - 1, r2, r9, r10, xs, zs)) := by
  unfold mcSimpleDiv
  rw [holShortTailrec_eq_elim]
  simp only [mcSimpleDivStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_simple_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSimpleDivPre_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcSimpleDivPre (l, r2, r9, r10, xs, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r0 := holEl (r10.toNat) xs
        let cond := cond ∧ (mcSingleDivPre (r0, r2, r9))
        let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r0
        mcSimpleDivPre (l - 1, r2, r9, r10, xs, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcSimpleDivPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSimpleDivStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_simple_div1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSimpleDiv1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width)) × Prop
  | (l, r2, r9, r10, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r2, r9, r10, zs), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (zs.length)
      let r0 := holEl (r10.toNat) zs
      let cond := cond ∧ (mcSingleDivPre (r0, r2, r9))
      let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
      let zs := zs.set (r10.toNat) r0
      (.inl (l - 1, r2, r9, r10, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_simple_div1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSimpleDiv1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) :=
  holShortTailrec mcSimpleDiv1Step

/-- The precondition of `mc_simple_div1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div1_pre"
  (words_as_type_indexed_bitvec)]
def mcSimpleDiv1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width)) mcSimpleDiv1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_simple_div1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div1_def"
  (words_as_type_indexed_bitvec)]
theorem mcSimpleDiv1_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcSimpleDiv1 (l, r2, r9, r10, zs) =
      if r10 = (0 : BitVec width) then
        (l, r2, r9, r10, zs)
      else
        (let r10 := r10 - (1 : BitVec width)
        let r0 := holEl (r10.toNat) zs
        let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
        let zs := zs.set (r10.toNat) r0
        mcSimpleDiv1 (l - 1, r2, r9, r10, zs)) := by
  unfold mcSimpleDiv1
  rw [holShortTailrec_eq_elim]
  simp only [mcSimpleDiv1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_simple_div1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_simple_div1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSimpleDiv1Pre_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcSimpleDiv1Pre (l, r2, r9, r10, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (zs.length)
        let r0 := holEl (r10.toNat) zs
        let cond := cond ∧ (mcSingleDivPre (r0, r2, r9))
        let (r0, r2, r9) := mcSingleDiv (r0, r2, r9)
        let zs := zs.set (r10.toNat) r0
        mcSimpleDiv1Pre (l - 1, r2, r9, r10, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcSimpleDiv1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSimpleDiv1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_calc_d` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCalcDStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width → (Nat × BitVec width × BitVec width ⊕ Nat × BitVec width) × Prop
  | (l, r1, r2) =>
    (if (r1).slt (0 : BitVec width) then
      (.inr (l, r2), True)
    else
      (let r1 := r1 + r1
      let r2 := r2 + r2
      (.inl (l - 1, r1, r2), l ≠ 0)))

/-- HOL `mc_calc_d`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_calc_d"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCalcD {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width → Nat × BitVec width :=
  holShortTailrec mcCalcDStep

/-- The precondition of `mc_calc_d`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_calc_d_pre"
  (words_as_type_indexed_bitvec)]
def mcCalcDPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := Nat × BitVec width) mcCalcDStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_calc_d`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_calc_d_def"
  (words_as_type_indexed_bitvec)]
theorem mcCalcD_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} :
    mcCalcD (l, r1, r2) =
      (if (r1).slt (0 : BitVec width) then
        (l, r2)
      else
        (let r1 := r1 + r1
        let r2 := r2 + r2
        mcCalcD (l - 1, r1, r2))) := by
  unfold mcCalcD
  rw [holShortTailrec_eq_elim]
  simp only [mcCalcDStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_calc_d`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_calc_d_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCalcDPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} :
    mcCalcDPre (l, r1, r2) ↔
      (if (r1).slt (0 : BitVec width) then
        True
      else
        (let r1 := r1 + r1
        let r2 := r2 + r2
        mcCalcDPre (l - 1, r1, r2) ∧ (l ≠ 0))) := by
  unfold mcCalcDPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCalcDStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

end Flapjack.Misc.Multiword
