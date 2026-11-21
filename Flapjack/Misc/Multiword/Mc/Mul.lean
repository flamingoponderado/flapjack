module

public import Flapjack.Misc.Multiword.Mc.AddSub

@[expose] public section

/-! Machine-code-style multiplication functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_single_mul_add` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSingleMulAddStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r1, r2, r3) =>
    (let cond := True
    let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
    let (r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
    let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
    let (r0, r4) := singleAddWord r0 r3 (0 : BitVec width)
    let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
    (.inr (r0, r1, r2, r3), cond))

/-- HOL `mc_single_mul_add`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_add"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSingleMulAdd {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcSingleMulAddStep

/-- The precondition of `mc_single_mul_add`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_add_pre"
  (words_as_type_indexed_bitvec)]
def mcSingleMulAddPre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width) mcSingleMulAddStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_single_mul_add`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_add_def" 1162
  (words_as_type_indexed_bitvec)]
theorem mcSingleMulAdd_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} {r3 : BitVec width} :
    mcSingleMulAdd (r0, r1, r2, r3) =
      (let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
      let (r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
      let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      let (r0, r4) := singleAddWord r0 r3 (0 : BitVec width)
      let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      (r0, r1, r2, r3)) := by
  unfold mcSingleMulAdd
  rw [holShortTailrec_eq_elim]
  simp only [mcSingleMulAddStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_single_mul_add`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_add_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSingleMulAddPre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} {r3 : BitVec width} :
    mcSingleMulAddPre (r0, r1, r2, r3) ↔
      (let cond := True
      let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
      let (r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
      let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      let (_r0, r4) := singleAddWord r0 r3 (0 : BitVec width)
      let (_r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      cond) := by
  unfold mcSingleMulAddPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSingleMulAddStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_mul_pass` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcMulPassStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r8, r9, r10, r11, ys, zs) =>
    if r9 = r11 then
      (let cond := (r10.toNat) < (zs.length)
      let zs := zs.set (r10.toNat) r1
      let r10 := r10 + (1 : BitVec width)
      (.inr (l, r1, r9, r10, ys, zs), cond))
    else
      (let cond := (r10.toNat) < (zs.length)
      let r3 := holEl (r10.toNat) zs
      let cond := cond ∧ ((r11.toNat) < (ys.length))
      let r2 := holEl (r11.toNat) ys
      let r0 := r8
      let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
      let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
      let zs := zs.set (r10.toNat) r0
      let r1 := r2
      let r10 := r10 + (1 : BitVec width)
      let r11 := r11 + (1 : BitVec width)
      (.inl (l - 1, r1, r8, r9, r10, r11, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_mul_pass`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pass"
  (words_as_type_indexed_bitvec)]
noncomputable def mcMulPass {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcMulPassStep

/-- The precondition of `mc_mul_pass`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pass_pre"
  (words_as_type_indexed_bitvec)]
def mcMulPassPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcMulPassStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_mul_pass`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pass_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulPass_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcMulPass (l, r1, r8, r9, r10, r11, ys, zs) =
      if r9 = r11 then
        (let zs := zs.set (r10.toNat) r1
        let r10 := r10 + (1 : BitVec width)
        (l, r1, r9, r10, ys, zs))
      else
        (let r3 := holEl (r10.toNat) zs
        let r2 := holEl (r11.toNat) ys
        let r0 := r8
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let zs := zs.set (r10.toNat) r0
        let r1 := r2
        let r10 := r10 + (1 : BitVec width)
        let r11 := r11 + (1 : BitVec width)
        mcMulPass (l - 1, r1, r8, r9, r10, r11, ys, zs)) := by
  unfold mcMulPass
  rw [holShortTailrec_eq_elim]
  simp only [mcMulPassStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_mul_pass`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pass_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulPassPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcMulPassPre (l, r1, r8, r9, r10, r11, ys, zs) ↔
      if r9 = r11 then
        (let cond := (r10.toNat) < (zs.length)
        let _zs := zs.set (r10.toNat) r1
        let _r10 := r10 + (1 : BitVec width)
        cond)
      else
        (let cond := (r10.toNat) < (zs.length)
        let r3 := holEl (r10.toNat) zs
        let cond := cond ∧ ((r11.toNat) < (ys.length))
        let r2 := holEl (r11.toNat) ys
        let r0 := r8
        let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let zs := zs.set (r10.toNat) r0
        let r1 := r2
        let r10 := r10 + (1 : BitVec width)
        let r11 := r11 + (1 : BitVec width)
        mcMulPassPre (l - 1, r1, r8, r9, r10, r11, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcMulPassPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcMulPassStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_mul` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcMulStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r7, r9, r10, r12, xs, ys, zs) =>
    if r7 = (0 : BitVec width) then
      (let r10 := r10 + r9
      (.inr (l, r10, xs, ys, zs), True))
    else
      (let r7 := r7 - (1 : BitVec width)
      let cond := (r12.toNat) < (xs.length)
      let r8 := holEl (r12.toNat) xs
      let r12 := r12 + (1 : BitVec width)
      let r11 := (0 : BitVec width)
      let r1 := r11
      let cond := cond ∧ ((mcMulPassPre (l - 1, r1, r8, r9, r10, r11, ys, zs)) ∧ (l ≠ 0))
      let (l, _r1, r9, r10, ys, zs) := mcMulPass (l - 1, r1, r8, r9, r10, r11, ys, zs)
      let r10 := r10 - r9
      (.inl (l - 1, r7, r9, r10, r12, xs, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_mul`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul"
  (words_as_type_indexed_bitvec)]
noncomputable def mcMul {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcMulStep

/-- The precondition of `mc_mul`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pre"
  (words_as_type_indexed_bitvec)]
def mcMulPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcMulStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_mul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_def"
  (words_as_type_indexed_bitvec)]
theorem mcMul_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r12 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcMul (l, r7, r9, r10, r12, xs, ys, zs) =
      if r7 = (0 : BitVec width) then
        (let r10 := r10 + r9
        (l, r10, xs, ys, zs))
      else
        (let r7 := r7 - (1 : BitVec width)
        let r8 := holEl (r12.toNat) xs
        let r12 := r12 + (1 : BitVec width)
        let r11 := (0 : BitVec width)
        let r1 := r11
        let (l, _r1, r9, r10, ys, zs) := mcMulPass (l - 1, r1, r8, r9, r10, r11, ys, zs)
        let r10 := r10 - r9
        mcMul (l - 1, r7, r9, r10, r12, xs, ys, zs)) := by
  unfold mcMul
  rw [holShortTailrec_eq_elim]
  simp only [mcMulStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_mul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulPre_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r12 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcMulPre (l, r7, r9, r10, r12, xs, ys, zs) ↔
      if r7 = (0 : BitVec width) then
        (let _r10 := r10 + r9
        True)
      else
        (let r7 := r7 - (1 : BitVec width)
        let cond := (r12.toNat) < (xs.length)
        let r8 := holEl (r12.toNat) xs
        let r12 := r12 + (1 : BitVec width)
        let r11 := (0 : BitVec width)
        let r1 := r11
        let cond := cond ∧ ((mcMulPassPre (l - 1, r1, r8, r9, r10, r11, ys, zs)) ∧ (l ≠ 0))
        let (l, _r1, r9, r10, ys, zs) := mcMulPass (l - 1, r1, r8, r9, r10, r11, ys, zs)
        let r10 := r10 - r9
        mcMulPre (l - 1, r7, r9, r10, r12, xs, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcMulPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcMulStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_mul_zero` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcMulZeroStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width)) × Prop
  | (l, r0, r10, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r10, zs), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (zs.length)
      let zs := zs.set (r10.toNat) r0
      (.inl (l - 1, r0, r10, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_mul_zero`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_zero"
  (words_as_type_indexed_bitvec)]
noncomputable def mcMulZero {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × List (BitVec width) :=
  holShortTailrec mcMulZeroStep

/-- The precondition of `mc_mul_zero`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_zero_pre"
  (words_as_type_indexed_bitvec)]
def mcMulZeroPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width)) mcMulZeroStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_mul_zero`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_zero_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulZero_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcMulZero (l, r0, r10, zs) =
      if r10 = (0 : BitVec width) then
        (l, r10, zs)
      else
        (let r10 := r10 - (1 : BitVec width)
        let zs := zs.set (r10.toNat) r0
        mcMulZero (l - 1, r0, r10, zs)) := by
  unfold mcMulZero
  rw [holShortTailrec_eq_elim]
  simp only [mcMulZeroStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_mul_zero`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_zero_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulZeroPre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcMulZeroPre (l, r0, r10, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (zs.length)
        let zs := zs.set (r10.toNat) r0
        mcMulZeroPre (l - 1, r0, r10, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcMulZeroPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcMulZeroStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_imul1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcImul1Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width → (BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r10, r11) =>
    if r10 = r11 then
      let r13 := ((0 : BitVec width))
      (.inr (r10, r11, r13), True)
    else
      let r13 := ((1 : BitVec width))
      (.inr (r10, r11, r13), True)

/-- HOL `mc_imul1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcImul1 {width : Nat} [NeZero width] :
    BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcImul1Step

/-- The precondition of `mc_imul1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul1_pre"
  (words_as_type_indexed_bitvec)]
def mcImul1Pre {width : Nat} [NeZero width] : BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcImul1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_imul1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul1_def"
  (words_as_type_indexed_bitvec)]
theorem mcImul1_def {width : Nat} [NeZero width] {r10 : BitVec width} {r11 : BitVec width} :
    mcImul1 (r10, r11) =
      if r10 = r11 then
        let r13 := ((0 : BitVec width))
        (r10, r11, r13)
      else
        let r13 := ((1 : BitVec width))
        (r10, r11, r13) := by
  unfold mcImul1
  rw [holShortTailrec_eq_elim]
  simp only [mcImul1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_imul1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcImul1Pre_def {width : Nat} [NeZero width] {r10 : BitVec width} {r11 : BitVec width} :
    mcImul1Pre (r10, r11) ↔
      if r10 = r11 then
        let _r13 := ((0 : BitVec width))
        True
      else
        let _r13 := ((1 : BitVec width))
        True := by
  unfold mcImul1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcImul1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_imul` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcImulStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, xs, ys, zs) =>
    (let r10 := (0 : BitVec width)
    if r1 = (0 : BitVec width) then
      (.inr (l, r10, xs, ys, zs), True)
    else
      if r2 = (0 : BitVec width) then
        (.inr (l, r10, xs, ys, zs), True)
      else
        (let r0 := (0 : BitVec width)
        let r10 := r2
        let r10 := r10 >>> 1
        let cond := (mcMulZeroPre (l - 1, r0, r10, zs)) ∧ (l ≠ 0)
        let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
        let r10 := r1
        let r10 := r10 &&& (1 : BitVec width)
        let r11 := r2
        let r11 := r11 &&& (1 : BitVec width)
        let (_r10, _r11, r13) := mcImul1 (r10, r11)
        let r7 := r1
        let r7 := r7 >>> 1
        let r9 := r2
        let r9 := r9 >>> 1
        let r10 := (0 : BitVec width)
        let r12 := (0 : BitVec width)
        let cond := cond ∧ ((mcMulPre (l - 1, r7, r9, r10, r12, xs, ys, zs)) ∧ (l ≠ 0))
        let (l, r10, xs, ys, zs) := mcMul (l - 1, r7, r9, r10, r12, xs, ys, zs)
        let r8 := (0 : BitVec width)
        let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
        let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
        let r10 := r10 <<< 1
        let r10 := r10 + r13
        (.inr (l, r10, xs, ys, zs), cond)))

/-- HOL `mc_imul`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul"
  (words_as_type_indexed_bitvec)]
noncomputable def mcImul {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcImulStep

/-- The precondition of `mc_imul`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul_pre"
  (words_as_type_indexed_bitvec)]
def mcImulPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcImulStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_imul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul_def"
  (words_as_type_indexed_bitvec)]
theorem mcImul_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcImul (l, r1, r2, xs, ys, zs) =
      (let r10 := (0 : BitVec width)
      if r1 = (0 : BitVec width) then
        (l, r10, xs, ys, zs)
      else
        if r2 = (0 : BitVec width) then
          (l, r10, xs, ys, zs)
        else
          (let r0 := (0 : BitVec width)
          let r10 := r2
          let r10 := r10 >>> 1
          let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
          let r10 := r1
          let r10 := r10 &&& (1 : BitVec width)
          let r11 := r2
          let r11 := r11 &&& (1 : BitVec width)
          let (_r10, _r11, r13) := mcImul1 (r10, r11)
          let r7 := r1
          let r7 := r7 >>> 1
          let r9 := r2
          let r9 := r9 >>> 1
          let r10 := (0 : BitVec width)
          let r12 := (0 : BitVec width)
          let (l, r10, xs, ys, zs) := mcMul (l - 1, r7, r9, r10, r12, xs, ys, zs)
          let r8 := (0 : BitVec width)
          let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
          let r10 := r10 <<< 1
          let r10 := r10 + r13
          (l, r10, xs, ys, zs))) := by
  unfold mcImul
  rw [holShortTailrec_eq_elim]
  simp only [mcImulStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_imul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_imul_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcImulPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcImulPre (l, r1, r2, xs, ys, zs) ↔
      (let _r10 := (0 : BitVec width)
      if r1 = (0 : BitVec width) then
        True
      else
        if r2 = (0 : BitVec width) then
          True
        else
          (let r0 := (0 : BitVec width)
          let r10 := r2
          let r10 := r10 >>> 1
          let cond := (mcMulZeroPre (l - 1, r0, r10, zs)) ∧ (l ≠ 0)
          let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
          let r10 := r1
          let r10 := r10 &&& (1 : BitVec width)
          let r11 := r2
          let r11 := r11 &&& (1 : BitVec width)
          let (_r10, _r11, r13) := mcImul1 (r10, r11)
          let r7 := r1
          let r7 := r7 >>> 1
          let r9 := r2
          let r9 := r9 >>> 1
          let r10 := (0 : BitVec width)
          let r12 := (0 : BitVec width)
          let cond := cond ∧ ((mcMulPre (l - 1, r7, r9, r10, r12, xs, ys, zs)) ∧ (l ≠ 0))
          let (l, r10, _xs, _ys, zs) := mcMul (l - 1, r7, r9, r10, r12, xs, ys, zs)
          let r8 := (0 : BitVec width)
          let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
          let (_l, _r8, r10, _zs) := mcFix (l - 1, r8, r10, zs)
          let r10 := r10 <<< 1
          let _r10 := r10 + r13
          cond)) := by
  unfold mcImulPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcImulStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
