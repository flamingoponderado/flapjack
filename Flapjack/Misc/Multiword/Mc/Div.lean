module

public import Flapjack.Misc.Multiword.Mc.DivSimple

@[expose] public section

/-! Machine-code-style long division functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_single_mul` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSingleMulStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r1, r2) =>
    (let cond := True
    let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
    let (r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
    let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
    (.inr (r0, r1, r2), cond))

/-- HOL `mc_single_mul`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSingleMul {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcSingleMulStep

/-- The precondition of `mc_single_mul`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_pre"
  (words_as_type_indexed_bitvec)]
def mcSingleMulPre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcSingleMulStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_single_mul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_def" 1706
  (words_as_type_indexed_bitvec)]
theorem mcSingleMul_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} :
    mcSingleMul (r0, r1, r2) =
      (let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
      let (r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
      let (r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      (r0, r1, r2)) := by
  unfold mcSingleMul
  rw [holShortTailrec_eq_elim]
  simp only [mcSingleMulStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_single_mul`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_single_mul_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSingleMulPre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} :
    mcSingleMulPre (r0, r1, r2) ↔
      (let cond := True
      let (r0, r2) := singleMul r0 r2 (0 : BitVec width)
      let (_r0, r4) := singleAddWord r0 r1 (0 : BitVec width)
      let (_r2, _r4) := singleAddWord r2 (0 : BitVec width) r4
      cond) := by
  unfold mcSingleMulPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSingleMulStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_mul_by_single2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcMulBySingle2Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (r6, r7, r8) =>
    (let r0 := r6
    let r1 := (0 : BitVec width)
    let r2 := r7
    let cond := mcSingleMulPre (r0, r1, r2)
    let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
    let r12 := r0
    let r0 := r6
    let r1 := r2
    let r2 := r8
    let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
    let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
    let r3 := r2
    let r2 := r0
    let r1 := r12
    (.inr (r1, r2, r3, r6, r7, r8), cond))

/-- HOL `mc_mul_by_single2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcMulBySingle2 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcMulBySingle2Step

/-- The precondition of `mc_mul_by_single2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single2_pre"
  (words_as_type_indexed_bitvec)]
def mcMulBySingle2Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcMulBySingle2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_mul_by_single2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single2_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulBySingle2_def {width : Nat} [NeZero width] {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} :
    mcMulBySingle2 (r6, r7, r8) =
      (let r0 := r6
      let r1 := (0 : BitVec width)
      let r2 := r7
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r12 := r0
      let r0 := r6
      let r1 := r2
      let r2 := r8
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r3 := r2
      let r2 := r0
      let r1 := r12
      (r1, r2, r3, r6, r7, r8)) := by
  unfold mcMulBySingle2
  rw [holShortTailrec_eq_elim]
  simp only [mcMulBySingle2Step, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_mul_by_single2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulBySingle2Pre_def {width : Nat} [NeZero width] {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} :
    mcMulBySingle2Pre (r6, r7, r8) ↔
      (let r0 := r6
      let r1 := (0 : BitVec width)
      let r2 := r7
      let cond := mcSingleMulPre (r0, r1, r2)
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r12 := r0
      let r0 := r6
      let r1 := r2
      let r2 := r8
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let _r3 := r2
      let _r2 := r0
      let _r1 := r12
      cond) := by
  unfold mcMulBySingle2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcMulBySingle2Step, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_cmp3` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCmp3Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (r1, r2, r3, r9, r10, r11) =>
    (let r0 := (1 : BitVec width)
    if r3 = r11 then
      if r2 = r10 then
        if r1 = r9 then
          (let r0 := (0 : BitVec width)
          (.inr (r0, r1, r2, r3, r9, r10, r11), True))
        else
          if r9 < r1 then
            (.inr (r0, r1, r2, r3, r9, r10, r11), True)
          else
            (let r0 := (0 : BitVec width)
            (.inr (r0, r1, r2, r3, r9, r10, r11), True))
      else
        if r10 < r2 then
          (.inr (r0, r1, r2, r3, r9, r10, r11), True)
        else
          (let r0 := (0 : BitVec width)
          (.inr (r0, r1, r2, r3, r9, r10, r11), True))
    else
      if r11 < r3 then
        (.inr (r0, r1, r2, r3, r9, r10, r11), True)
      else
        (let r0 := (0 : BitVec width)
        (.inr (r0, r1, r2, r3, r9, r10, r11), True)))

/-- HOL `mc_cmp3`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp3"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCmp3 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcCmp3Step

/-- The precondition of `mc_cmp3`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp3_pre"
  (words_as_type_indexed_bitvec)]
def mcCmp3Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcCmp3Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_cmp3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp3_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmp3_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {r3 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmp3 (r1, r2, r3, r9, r10, r11) =
      (let r0 := (1 : BitVec width)
      if r3 = r11 then
        if r2 = r10 then
          if r1 = r9 then
            (let r0 := (0 : BitVec width)
            (r0, r1, r2, r3, r9, r10, r11))
          else
            if r9 < r1 then
              (r0, r1, r2, r3, r9, r10, r11)
            else
              (let r0 := (0 : BitVec width)
              (r0, r1, r2, r3, r9, r10, r11))
        else
          if r10 < r2 then
            (r0, r1, r2, r3, r9, r10, r11)
          else
            (let r0 := (0 : BitVec width)
            (r0, r1, r2, r3, r9, r10, r11))
      else
        if r11 < r3 then
          (r0, r1, r2, r3, r9, r10, r11)
        else
          (let r0 := (0 : BitVec width)
          (r0, r1, r2, r3, r9, r10, r11))) := by
  unfold mcCmp3
  rw [holShortTailrec_eq_elim]
  simp only [mcCmp3Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_cmp3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp3_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmp3Pre_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {r3 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmp3Pre (r1, r2, r3, r9, r10, r11) ↔
      (let _r0 := (1 : BitVec width)
      if r3 = r11 then
        if r2 = r10 then
          if r1 = r9 then
            (let _r0 := (0 : BitVec width)
            True)
          else
            if r9 < r1 then
              True
            else
              (let _r0 := (0 : BitVec width)
              True)
        else
          if r10 < r2 then
            True
          else
            (let _r0 := (0 : BitVec width)
            True)
      else
        if r11 < r3 then
          True
        else
          (let _r0 := (0 : BitVec width)
          True)) := by
  unfold mcCmp3Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCmp3Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_cmp_mul2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCmpMul2Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (r6, r7, r8, r9, r10, r11) =>
    (let cond := mcMulBySingle2Pre (r6, r7, r8)
    let (r1, r2, r3, r6, r7, r8) := mcMulBySingle2 (r6, r7, r8)
    let (r0, _r1, _r2, _r3, r9, r10, r11) := mcCmp3 (r1, r2, r3, r9, r10, r11)
    (.inr (r0, r6, r7, r8, r9, r10, r11), cond))

/-- HOL `mc_cmp_mul2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_mul2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCmpMul2 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcCmpMul2Step

/-- The precondition of `mc_cmp_mul2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_mul2_pre"
  (words_as_type_indexed_bitvec)]
def mcCmpMul2Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcCmpMul2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_cmp_mul2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_mul2_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmpMul2_def {width : Nat} [NeZero width] {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmpMul2 (r6, r7, r8, r9, r10, r11) =
      (let (r1, r2, r3, r6, r7, r8) := mcMulBySingle2 (r6, r7, r8)
      let (r0, _r1, _r2, _r3, r9, r10, r11) := mcCmp3 (r1, r2, r3, r9, r10, r11)
      (r0, r6, r7, r8, r9, r10, r11)) := by
  unfold mcCmpMul2
  rw [holShortTailrec_eq_elim]
  simp only [mcCmpMul2Step, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_cmp_mul2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp_mul2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmpMul2Pre_def {width : Nat} [NeZero width] {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmpMul2Pre (r6, r7, r8, r9, r10, r11) ↔
      (let cond := mcMulBySingle2Pre (r6, r7, r8)
      let (r1, r2, r3, _r6, _r7, _r8) := mcMulBySingle2 (r6, r7, r8)
      let (_r0, _r1, _r2, _r3, _r9, _r10, _r11) := mcCmp3 (r1, r2, r3, r9, r10, r11)
      cond) := by
  unfold mcCmpMul2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCmpMul2Step, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_sub1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSub1Step {width : Nat} [NeZero width] :
    BitVec width → (BitVec width ⊕ BitVec width) × Prop
  | r6 =>
    if r6 = (0 : BitVec width) then
      (.inr r6, True)
    else
      (let r6 := r6 - (1 : BitVec width)
      (.inr r6, True))

/-- HOL `mc_sub1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSub1 {width : Nat} [NeZero width] :
    BitVec width → BitVec width :=
  holShortTailrec mcSub1Step

/-- The precondition of `mc_sub1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub1_pre"
  (words_as_type_indexed_bitvec)]
def mcSub1Pre {width : Nat} [NeZero width] : BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width) mcSub1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_sub1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub1_def"
  (words_as_type_indexed_bitvec)]
theorem mcSub1_def {width : Nat} [NeZero width] {r6 : BitVec width} :
    mcSub1 r6 =
      if r6 = (0 : BitVec width) then
        r6
      else
        (let r6 := r6 - (1 : BitVec width)
        r6) := by
  unfold mcSub1
  rw [holShortTailrec_eq_elim]
  simp only [mcSub1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_sub1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSub1Pre_def {width : Nat} [NeZero width] {r6 : BitVec width} :
    mcSub1Pre r6 ↔
      if r6 = (0 : BitVec width) then
        True
      else
        (let _r6 := r6 - (1 : BitVec width)
        True) := by
  unfold mcSub1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSub1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_cmp2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCmp2Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r2, r10, r11) =>
    (let r1 := (1 : BitVec width)
    if r2 = r11 then
      if r0 = r10 then
        (let r1 := (0 : BitVec width)
        (.inr (r0, r1, r2, r10, r11), True))
      else
        if r10 < r0 then
          (.inr (r0, r1, r2, r10, r11), True)
        else
          (let r1 := (0 : BitVec width)
          (.inr (r0, r1, r2, r10, r11), True))
    else
      if r11 < r2 then
        (.inr (r0, r1, r2, r10, r11), True)
      else
        (let r1 := (0 : BitVec width)
        (.inr (r0, r1, r2, r10, r11), True)))

/-- HOL `mc_cmp2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCmp2 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcCmp2Step

/-- The precondition of `mc_cmp2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp2_pre"
  (words_as_type_indexed_bitvec)]
def mcCmp2Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcCmp2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_cmp2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp2_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmp2_def {width : Nat} [NeZero width] {r0 : BitVec width} {r2 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmp2 (r0, r2, r10, r11) =
      (let r1 := (1 : BitVec width)
      if r2 = r11 then
        if r0 = r10 then
          (let r1 := (0 : BitVec width)
          (r0, r1, r2, r10, r11))
        else
          if r10 < r0 then
            (r0, r1, r2, r10, r11)
          else
            (let r1 := (0 : BitVec width)
            (r0, r1, r2, r10, r11))
      else
        if r11 < r2 then
          (r0, r1, r2, r10, r11)
        else
          (let r1 := (0 : BitVec width)
          (r0, r1, r2, r10, r11))) := by
  unfold mcCmp2
  rw [holShortTailrec_eq_elim]
  simp only [mcCmp2Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_cmp2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_cmp2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCmp2Pre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r2 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcCmp2Pre (r0, r2, r10, r11) ↔
      (let _r1 := (1 : BitVec width)
      if r2 = r11 then
        if r0 = r10 then
          (let _r1 := (0 : BitVec width)
          True)
        else
          if r10 < r0 then
            True
          else
            (let _r1 := (0 : BitVec width)
            True)
      else
        if r11 < r2 then
          True
        else
          (let _r1 := (0 : BitVec width)
          True)) := by
  unfold mcCmp2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCmp2Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_test` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivTestStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (l, r6, r7, r8, r9, r10, r11) =>
    (let cond := mcCmpMul2Pre (r6, r7, r8, r9, r10, r11)
    let (r0, r6, r7, r8, r9, r10, r11) := mcCmpMul2 (r6, r7, r8, r9, r10, r11)
    if r0 = (0 : BitVec width) then
      (.inr (l, r6, r7, r8, r9, r10, r11), cond)
    else
      (let r6 := mcSub1 r6
      let r0 := r6
      let r1 := (0 : BitVec width)
      let r2 := r8
      let r3 := r1
      let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
      let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
      let r2 := r2 + (1 : BitVec width)
      let (_r0, r1, _r2, r10, r11) := mcCmp2 (r0, r2, r10, r11)
      if r1 = (0 : BitVec width) then
        (.inr (l, r6, r7, r8, r9, r10, r11), cond)
      else
        (.inl (l - 1, r6, r7, r8, r9, r10, r11), cond ∧ (l ≠ 0))))

/-- HOL `mc_div_test`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_test"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivTest {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcDivTestStep

/-- The precondition of `mc_div_test`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_test_pre"
  (words_as_type_indexed_bitvec)]
def mcDivTestPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcDivTestStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_test`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_test_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivTest_def {width : Nat} [NeZero width] {l : Nat} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcDivTest (l, r6, r7, r8, r9, r10, r11) =
      (let (r0, r6, r7, r8, r9, r10, r11) := mcCmpMul2 (r6, r7, r8, r9, r10, r11)
      if r0 = (0 : BitVec width) then
        (l, r6, r7, r8, r9, r10, r11)
      else
        (let r6 := mcSub1 r6
        let r0 := r6
        let r1 := (0 : BitVec width)
        let r2 := r8
        let r3 := r1
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let r2 := r2 + (1 : BitVec width)
        let (_r0, r1, _r2, r10, r11) := mcCmp2 (r0, r2, r10, r11)
        if r1 = (0 : BitVec width) then
          (l, r6, r7, r8, r9, r10, r11)
        else
          mcDivTest (l - 1, r6, r7, r8, r9, r10, r11))) := by
  unfold mcDivTest
  rw [holShortTailrec_eq_elim]
  simp only [mcDivTestStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_test`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_test_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivTestPre_def {width : Nat} [NeZero width] {l : Nat} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcDivTestPre (l, r6, r7, r8, r9, r10, r11) ↔
      (let cond := mcCmpMul2Pre (r6, r7, r8, r9, r10, r11)
      let (r0, r6, r7, r8, r9, r10, r11) := mcCmpMul2 (r6, r7, r8, r9, r10, r11)
      if r0 = (0 : BitVec width) then
        cond
      else
        (let r6 := mcSub1 r6
        let r0 := r6
        let r1 := (0 : BitVec width)
        let r2 := r8
        let r3 := r1
        let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let r2 := r2 + (1 : BitVec width)
        let (_r0, r1, _r2, r10, r11) := mcCmp2 (r0, r2, r10, r11)
        if r1 = (0 : BitVec width) then
          cond
        else
          mcDivTestPre (l - 1, r6, r7, r8, r9, r10, r11) ∧ (cond ∧ (l ≠ 0)))) := by
  unfold mcDivTestPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivTestStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_div_r1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivR1Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r1, r2) =>
    if r2 < r1 then
      (let cond := singleDivPre r2 r0 r1
      let (r0, r2) := singleDiv r2 r0 r1
      (.inr (r0, r1, r2), cond))
    else
      (let r0 := (0 : BitVec width)
      let r0 := ~~~r0
      (.inr (r0, r1, r2), True))

/-- HOL `mc_div_r1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_r1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivR1 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcDivR1Step

/-- The precondition of `mc_div_r1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_r1_pre"
  (words_as_type_indexed_bitvec)]
def mcDivR1Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcDivR1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_r1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_r1_def" 1965
  (words_as_type_indexed_bitvec)]
theorem mcDivR1_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} :
    mcDivR1 (r0, r1, r2) =
      if r2 < r1 then
        (let (r0, r2) := singleDiv r2 r0 r1
        (r0, r1, r2))
      else
        (let r0 := (0 : BitVec width)
        let r0 := ~~~r0
        (r0, r1, r2)) := by
  unfold mcDivR1
  rw [holShortTailrec_eq_elim]
  simp only [mcDivR1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_r1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_r1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivR1Pre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r1 : BitVec width} {r2 : BitVec width} :
    mcDivR1Pre (r0, r1, r2) ↔
      if r2 < r1 then
        (let cond := singleDivPre r2 r0 r1
        let (_r0, _r2) := singleDiv r2 r0 r1
        cond)
      else
        (let r0 := (0 : BitVec width)
        let _r0 := ~~~r0
        True) := by
  unfold mcDivR1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivR1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_guess` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivGuessStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) × Prop
  | (l, r7, r8, r9, r10, r11) =>
    (let r0 := r10
    let r1 := r8
    let r2 := r11
    let cond := mcDivR1Pre (r0, r1, r2)
    let (r0, _r1, _r2) := mcDivR1 (r0, r1, r2)
    let r6 := r0
    let cond := cond ∧ ((mcDivTestPre (l - 1, r6, r7, r8, r9, r10, r11)) ∧ (l ≠ 0))
    let (l, r6, r7, r8, r9, r10, r11) := mcDivTest (l - 1, r6, r7, r8, r9, r10, r11)
    (.inr (l, r6, r7, r8, r9, r10, r11), cond))

/-- HOL `mc_div_guess`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_guess"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivGuess {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcDivGuessStep

/-- The precondition of `mc_div_guess`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_guess_pre"
  (words_as_type_indexed_bitvec)]
def mcDivGuessPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width) mcDivGuessStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_guess`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_guess_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivGuess_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcDivGuess (l, r7, r8, r9, r10, r11) =
      (let r0 := r10
      let r1 := r8
      let r2 := r11
      let (r0, _r1, _r2) := mcDivR1 (r0, r1, r2)
      let r6 := r0
      let (l, r6, r7, r8, r9, r10, r11) := mcDivTest (l - 1, r6, r7, r8, r9, r10, r11)
      (l, r6, r7, r8, r9, r10, r11)) := by
  unfold mcDivGuess
  rw [holShortTailrec_eq_elim]
  simp only [mcDivGuessStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_guess`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_guess_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivGuessPre_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} :
    mcDivGuessPre (l, r7, r8, r9, r10, r11) ↔
      (let r0 := r10
      let r1 := r8
      let r2 := r11
      let cond := mcDivR1Pre (r0, r1, r2)
      let (r0, _r1, _r2) := mcDivR1 (r0, r1, r2)
      let r6 := r0
      let cond := cond ∧ ((mcDivTestPre (l - 1, r6, r7, r8, r9, r10, r11)) ∧ (l ≠ 0))
      let (_l, _r6, _r7, _r8, _r9, _r10, _r11) := mcDivTest (l - 1, r6, r7, r8, r9, r10, r11)
      cond) := by
  unfold mcDivGuessPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivGuessStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_adj_cmp` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAdjCmpStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r3, r8) =>
    if r0 = r3 then
      (.inr (r0, r3, r8), True)
    else
      (let r8 := (1 : BitVec width)
      if r3 < r0 then
        (.inr (r0, r3, r8), True)
      else
        (let r8 := (0 : BitVec width)
        (.inr (r0, r3, r8), True)))

/-- HOL `mc_adj_cmp`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adj_cmp"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAdjCmp {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcAdjCmpStep

/-- The precondition of `mc_adj_cmp`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adj_cmp_pre"
  (words_as_type_indexed_bitvec)]
def mcAdjCmpPre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcAdjCmpStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_adj_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adj_cmp_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdjCmp_def {width : Nat} [NeZero width] {r0 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} :
    mcAdjCmp (r0, r3, r8) =
      if r0 = r3 then
        (r0, r3, r8)
      else
        (let r8 := (1 : BitVec width)
        if r3 < r0 then
          (r0, r3, r8)
        else
          (let r8 := (0 : BitVec width)
          (r0, r3, r8))) := by
  unfold mcAdjCmp
  rw [holShortTailrec_eq_elim]
  simp only [mcAdjCmpStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_adj_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adj_cmp_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdjCmpPre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} :
    mcAdjCmpPre (r0, r3, r8) ↔
      if r0 = r3 then
        True
      else
        (let _r8 := (1 : BitVec width)
        if r3 < r0 then
          True
        else
          (let _r8 := (0 : BitVec width)
          True)) := by
  unfold mcAdjCmpPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAdjCmpStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_adjust_aux` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAdjustAuxStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) =>
    if r9 = r11 then
      (let r0 := r12
      let cond := (r10.toNat) < (zs.length)
      let r3 := holEl (r10.toNat) zs
      let r10 := r10 + (1 : BitVec width)
      let (_r0, _r3, r8) := mcAdjCmp (r0, r3, r8)
      (.inr (l, r6, r7, r8, r9, r10, r11, ys, zs), cond))
    else
      (let r0 := r6
      let cond := (r11.toNat) < (ys.length)
      let r2 := holEl (r11.toNat) ys
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r1 := r12
      let r12 := r2
      let r2 := r0
      let r0 := r7
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r1 := r12
      let r12 := r2
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let r3 := holEl (r10.toNat) zs
      let (_r0, _r3, r8) := mcAdjCmp (r0, r3, r8)
      let r11 := r11 + (1 : BitVec width)
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_adjust_aux`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adjust_aux"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAdjustAux {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcAdjustAuxStep

/-- The precondition of `mc_adjust_aux`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adjust_aux_pre"
  (words_as_type_indexed_bitvec)]
def mcAdjustAuxPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcAdjustAuxStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_adjust_aux`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adjust_aux_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdjustAux_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r12 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAdjustAux (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) =
      if r9 = r11 then
        (let r0 := r12
        let r3 := holEl (r10.toNat) zs
        let r10 := r10 + (1 : BitVec width)
        let (_r0, _r3, r8) := mcAdjCmp (r0, r3, r8)
        (l, r6, r7, r8, r9, r10, r11, ys, zs))
      else
        (let r0 := r6
        let r2 := holEl (r11.toNat) ys
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r2 := r0
        let r0 := r7
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r3 := holEl (r10.toNat) zs
        let (_r0, _r3, r8) := mcAdjCmp (r0, r3, r8)
        let r11 := r11 + (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        mcAdjustAux (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) := by
  unfold mcAdjustAux
  rw [holShortTailrec_eq_elim]
  simp only [mcAdjustAuxStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_adjust_aux`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_adjust_aux_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdjustAuxPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r12 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAdjustAuxPre (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) ↔
      if r9 = r11 then
        (let r0 := r12
        let cond := (r10.toNat) < (zs.length)
        let r3 := holEl (r10.toNat) zs
        let _r10 := r10 + (1 : BitVec width)
        let (_r0, _r3, _r8) := mcAdjCmp (r0, r3, r8)
        cond)
      else
        (let r0 := r6
        let cond := (r11.toNat) < (ys.length)
        let r2 := holEl (r11.toNat) ys
        let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r2 := r0
        let r0 := r7
        let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let r3 := holEl (r10.toNat) zs
        let (_r0, _r3, r8) := mcAdjCmp (r0, r3, r8)
        let r11 := r11 + (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        mcAdjustAuxPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcAdjustAuxPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAdjustAuxStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_div_adjust` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivAdjustStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r6, r7, r9, r10, ys, zs) =>
    (let r1 := (0 : BitVec width)
    let r8 := r1
    let r11 := r1
    let r12 := r1
    let cond := (mcAdjustAuxPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) ∧ (l ≠ 0)
    let (l, r6, r7, r8, r9, r10, r11, ys, zs) := mcAdjustAux (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
    if r7 = (0 : BitVec width) then
      (.inr (l, r6, r7, r9, r10, r11, ys, zs), cond)
    else
      if r8 = (0 : BitVec width) then
        (.inr (l, r6, r7, r9, r10, r11, ys, zs), cond)
      else
        (let r7 := r7 - (1 : BitVec width)
        (.inr (l, r6, r7, r9, r10, r11, ys, zs), cond)))

/-- HOL `mc_div_adjust`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_adjust"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivAdjust {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivAdjustStep

/-- The precondition of `mc_div_adjust`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_adjust_pre"
  (words_as_type_indexed_bitvec)]
def mcDivAdjustPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivAdjustStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_adjust`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_adjust_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivAdjust_def {width : Nat} [NeZero width] {l : Nat} {r6 : BitVec width} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivAdjust (l, r6, r7, r9, r10, ys, zs) =
      (let r1 := (0 : BitVec width)
      let r8 := r1
      let r11 := r1
      let r12 := r1
      let (l, r6, r7, r8, r9, r10, r11, ys, zs) := mcAdjustAux (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
      if r7 = (0 : BitVec width) then
        (l, r6, r7, r9, r10, r11, ys, zs)
      else
        if r8 = (0 : BitVec width) then
          (l, r6, r7, r9, r10, r11, ys, zs)
        else
          (let r7 := r7 - (1 : BitVec width)
          (l, r6, r7, r9, r10, r11, ys, zs))) := by
  unfold mcDivAdjust
  rw [holShortTailrec_eq_elim]
  simp only [mcDivAdjustStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_adjust`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_adjust_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivAdjustPre_def {width : Nat} [NeZero width] {l : Nat} {r6 : BitVec width} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivAdjustPre (l, r6, r7, r9, r10, ys, zs) ↔
      (let r1 := (0 : BitVec width)
      let r8 := r1
      let r11 := r1
      let r12 := r1
      let cond := (mcAdjustAuxPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) ∧ (l ≠ 0)
      let (_l, _r6, r7, r8, _r9, _r10, _r11, _ys, _zs) := mcAdjustAux (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
      if r7 = (0 : BitVec width) then
        cond
      else
        if r8 = (0 : BitVec width) then
          cond
        else
          (let _r7 := r7 - (1 : BitVec width)
          cond)) := by
  unfold mcDivAdjustPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivAdjustStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSubStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → (BitVec width × BitVec width × BitVec width ⊕ BitVec width × BitVec width × BitVec width) × Prop
  | (r0, r3, r8) =>
    (let cond := ((r8 ≠ (0 : BitVec width)) → (r8 = (1 : BitVec width)))
    let (r3, r8) := singleSubWord r3 r0 r8
    (.inr (r0, r3, r8), cond))

/-- HOL `mc_div_sub`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSub {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width → BitVec width × BitVec width × BitVec width :=
  holShortTailrec mcDivSubStep

/-- The precondition of `mc_div_sub`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSubPre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width) mcDivSubStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_def" 2238
  (words_as_type_indexed_bitvec)]
theorem mcDivSub_def {width : Nat} [NeZero width] {r0 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} :
    mcDivSub (r0, r3, r8) =
      (let (r3, r8) := singleSubWord r3 r0 r8
      (r0, r3, r8)) := by
  unfold mcDivSub
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSubStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubPre_def {width : Nat} [NeZero width] {r0 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} :
    mcDivSubPre (r0, r3, r8) ↔
      (let cond := ((r8 ≠ (0 : BitVec width)) → (r8 = (1 : BitVec width)))
      let (_r3, _r8) := singleSubWord r3 r0 r8
      cond) := by
  unfold mcDivSubPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSubStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub_loop` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSubLoopStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) =>
    if r9 = r11 then
      (let r0 := r12
      let cond := (r10.toNat) < (zs.length)
      let r3 := holEl (r10.toNat) zs
      let cond := cond ∧ (mcDivSubPre (r0, r3, r8))
      let (_r0, r3, _r8) := mcDivSub (r0, r3, r8)
      let r1 := r3
      let zs := zs.set (r10.toNat) r1
      let r10 := r10 + (1 : BitVec width)
      (.inr (l, r6, r7, r9, r10, r11, ys, zs), cond))
    else
      (let r0 := r6
      let cond := (r11.toNat) < (ys.length)
      let r2 := holEl (r11.toNat) ys
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r1 := r12
      let r12 := r2
      let r2 := r0
      let r0 := r7
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r1 := r12
      let r12 := r2
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let r3 := holEl (r10.toNat) zs
      let cond := cond ∧ (mcDivSubPre (r0, r3, r8))
      let (_r0, r3, r8) := mcDivSub (r0, r3, r8)
      let r0 := r1
      let r1 := r3
      let zs := zs.set (r10.toNat) r1
      let r1 := r0
      let r11 := r11 + (1 : BitVec width)
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_div_sub_loop`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_loop"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSubLoop {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivSubLoopStep

/-- The precondition of `mc_div_sub_loop`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_loop_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSubLoopPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivSubLoopStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_loop_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubLoop_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r12 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubLoop (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) =
      if r9 = r11 then
        (let r0 := r12
        let r3 := holEl (r10.toNat) zs
        let (_r0, r3, _r8) := mcDivSub (r0, r3, r8)
        let r1 := r3
        let zs := zs.set (r10.toNat) r1
        let r10 := r10 + (1 : BitVec width)
        (l, r6, r7, r9, r10, r11, ys, zs))
      else
        (let r0 := r6
        let r2 := holEl (r11.toNat) ys
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r2 := r0
        let r0 := r7
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r3 := holEl (r10.toNat) zs
        let (_r0, r3, r8) := mcDivSub (r0, r3, r8)
        let r0 := r1
        let r1 := r3
        let zs := zs.set (r10.toNat) r1
        let r1 := r0
        let r11 := r11 + (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        mcDivSubLoop (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) := by
  unfold mcDivSubLoop
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSubLoopStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_loop_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubLoopPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r6 : BitVec width} {r7 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r12 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubLoopPre (l, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) ↔
      if r9 = r11 then
        (let r0 := r12
        let cond := (r10.toNat) < (zs.length)
        let r3 := holEl (r10.toNat) zs
        let cond := cond ∧ (mcDivSubPre (r0, r3, r8))
        let (_r0, r3, _r8) := mcDivSub (r0, r3, r8)
        let r1 := r3
        let _zs := zs.set (r10.toNat) r1
        let _r10 := r10 + (1 : BitVec width)
        cond)
      else
        (let r0 := r6
        let cond := (r11.toNat) < (ys.length)
        let r2 := holEl (r11.toNat) ys
        let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let r2 := r0
        let r0 := r7
        let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r12
        let r12 := r2
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let r3 := holEl (r10.toNat) zs
        let cond := cond ∧ (mcDivSubPre (r0, r3, r8))
        let (_r0, r3, r8) := mcDivSub (r0, r3, r8)
        let r0 := r1
        let r1 := r3
        let zs := zs.set (r10.toNat) r1
        let r1 := r0
        let r11 := r11 + (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        mcDivSubLoopPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcDivSubLoopPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSubLoopStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_div_loop` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivLoopStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r7, r9, r10, r11, r14, r15, ys, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r7, r9, r10, r11, r14, r15, ys, zs), True)
    else
      (let r6 := r14
      let r3 := r15
      let r14 := r7
      let r15 := r9
      let r16 := r10
      let r10 := r10 + r9
      let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (zs.length)
      let r0 := holEl (r10.toNat) zs
      let r10 := r10 - (1 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let r1 := holEl (r10.toNat) zs
      let r10 := r10 - (1 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let r2 := holEl (r10.toNat) zs
      let r11 := r0
      let r10 := r1
      let r9 := r2
      let r7 := r3
      let r8 := r6
      let cond := cond ∧ (mcDivGuessPre (l, r7, r8, r9, r10, r11))
      let (l, r6, r7, r8, _r9, _r10, _r11) := mcDivGuess (l, r7, r8, r9, r10, r11)
      let r0 := r6
      let r6 := r14
      let r9 := r15
      let r10 := r16
      let r10 := r10 - (1 : BitVec width)
      let r15 := r7
      let r14 := r8
      let r7 := r0
      let cond := cond ∧ (mcDivAdjustPre (l, r6, r7, r9, r10, ys, zs))
      let (l, r6, r7, r9, r10, _r11, ys, zs) := mcDivAdjust (l, r6, r7, r9, r10, ys, zs)
      let r10 := r10 - r9
      let r10 := r10 - (1 : BitVec width)
      let r1 := (0 : BitVec width)
      let _r8 := r1
      let r8 := (1 : BitVec width)
      let r11 := r1
      let r12 := r1
      let cond := cond ∧ ((mcDivSubLoopPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) ∧ (l ≠ 0))
      let (l, r6, r7, r9, r10, r11, ys, zs) := mcDivSubLoop (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
      let r10 := r10 - (1 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r7
      let r10 := r10 - r9
      let r7 := r6
      (.inl (l - 1, r7, r9, r10, r11, r14, r15, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_div_loop`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_loop"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivLoop {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivLoopStep

/-- The precondition of `mc_div_loop`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_loop_pre"
  (words_as_type_indexed_bitvec)]
def mcDivLoopPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivLoopStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_loop_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivLoop_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r14 : BitVec width} {r15 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivLoop (l, r7, r9, r10, r11, r14, r15, ys, zs) =
      if r10 = (0 : BitVec width) then
        (l, r7, r9, r10, r11, r14, r15, ys, zs)
      else
        (let r6 := r14
        let r3 := r15
        let r14 := r7
        let r15 := r9
        let r16 := r10
        let r10 := r10 + r9
        let r10 := r10 - (1 : BitVec width)
        let r0 := holEl (r10.toNat) zs
        let r10 := r10 - (1 : BitVec width)
        let r1 := holEl (r10.toNat) zs
        let r10 := r10 - (1 : BitVec width)
        let r2 := holEl (r10.toNat) zs
        let r11 := r0
        let r10 := r1
        let r9 := r2
        let r7 := r3
        let r8 := r6
        let (l, r6, r7, r8, _r9, _r10, _r11) := mcDivGuess (l, r7, r8, r9, r10, r11)
        let r0 := r6
        let r6 := r14
        let r9 := r15
        let r10 := r16
        let r10 := r10 - (1 : BitVec width)
        let r15 := r7
        let r14 := r8
        let r7 := r0
        let (l, r6, r7, r9, r10, _r11, ys, zs) := mcDivAdjust (l, r6, r7, r9, r10, ys, zs)
        let r10 := r10 - r9
        let r10 := r10 - (1 : BitVec width)
        let r1 := (0 : BitVec width)
        let _r8 := r1
        let r8 := (1 : BitVec width)
        let r11 := r1
        let r12 := r1
        let (l, r6, r7, r9, r10, r11, ys, zs) := mcDivSubLoop (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
        let r10 := r10 - (1 : BitVec width)
        let zs := zs.set (r10.toNat) r7
        let r10 := r10 - r9
        let r7 := r6
        mcDivLoop (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)) := by
  unfold mcDivLoop
  rw [holShortTailrec_eq_elim]
  simp only [mcDivLoopStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_loop_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivLoopPre_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r14 : BitVec width} {r15 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivLoopPre (l, r7, r9, r10, r11, r14, r15, ys, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r6 := r14
        let r3 := r15
        let r14 := r7
        let r15 := r9
        let r16 := r10
        let r10 := r10 + r9
        let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (zs.length)
        let r0 := holEl (r10.toNat) zs
        let r10 := r10 - (1 : BitVec width)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let r1 := holEl (r10.toNat) zs
        let r10 := r10 - (1 : BitVec width)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let r2 := holEl (r10.toNat) zs
        let r11 := r0
        let r10 := r1
        let r9 := r2
        let r7 := r3
        let r8 := r6
        let cond := cond ∧ (mcDivGuessPre (l, r7, r8, r9, r10, r11))
        let (l, r6, r7, r8, _r9, _r10, _r11) := mcDivGuess (l, r7, r8, r9, r10, r11)
        let r0 := r6
        let r6 := r14
        let r9 := r15
        let r10 := r16
        let r10 := r10 - (1 : BitVec width)
        let r15 := r7
        let r14 := r8
        let r7 := r0
        let cond := cond ∧ (mcDivAdjustPre (l, r6, r7, r9, r10, ys, zs))
        let (l, r6, r7, r9, r10, _r11, ys, zs) := mcDivAdjust (l, r6, r7, r9, r10, ys, zs)
        let r10 := r10 - r9
        let r10 := r10 - (1 : BitVec width)
        let r1 := (0 : BitVec width)
        let _r8 := r1
        let r8 := (1 : BitVec width)
        let r11 := r1
        let r12 := r1
        let cond := cond ∧ ((mcDivSubLoopPre (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)) ∧ (l ≠ 0))
        let (l, r6, r7, r9, r10, r11, ys, zs) := mcDivSubLoop (l - 1, r1, r6, r7, r8, r9, r10, r11, r12, ys, zs)
        let r10 := r10 - (1 : BitVec width)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r7
        let r10 := r10 - r9
        let r7 := r6
        mcDivLoopPre (l - 1, r7, r9, r10, r11, r14, r15, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcDivLoopPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivLoopStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_mul_by_single` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcMulBySingleStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r8, r9, r10, r11, xs, zs) =>
    if r9 = r11 then
      (let cond := (r10.toNat) < (zs.length)
      let zs := zs.set (r10.toNat) r1
      let r10 := r10 + (1 : BitVec width)
      (.inr (l, r1, r8, r9, r10, xs, zs), cond))
    else
      (let cond := (r11.toNat) < (xs.length)
      let r2 := holEl (r11.toNat) xs
      let r0 := r8
      let r3 := (0 : BitVec width)
      let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
      let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r0
      let r1 := r2
      let r10 := r10 + (1 : BitVec width)
      let r11 := r11 + (1 : BitVec width)
      (.inl (l - 1, r1, r8, r9, r10, r11, xs, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_mul_by_single`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single"
  (words_as_type_indexed_bitvec)]
noncomputable def mcMulBySingle {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcMulBySingleStep

/-- The precondition of `mc_mul_by_single`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single_pre"
  (words_as_type_indexed_bitvec)]
def mcMulBySinglePre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcMulBySingleStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_mul_by_single`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulBySingle_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcMulBySingle (l, r1, r8, r9, r10, r11, xs, zs) =
      if r9 = r11 then
        (let zs := zs.set (r10.toNat) r1
        let r10 := r10 + (1 : BitVec width)
        (l, r1, r8, r9, r10, xs, zs))
      else
        (let r2 := holEl (r11.toNat) xs
        let r0 := r8
        let r3 := (0 : BitVec width)
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let zs := zs.set (r10.toNat) r0
        let r1 := r2
        let r10 := r10 + (1 : BitVec width)
        let r11 := r11 + (1 : BitVec width)
        mcMulBySingle (l - 1, r1, r8, r9, r10, r11, xs, zs)) := by
  unfold mcMulBySingle
  rw [holShortTailrec_eq_elim]
  simp only [mcMulBySingleStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_mul_by_single`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_mul_by_single_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcMulBySinglePre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcMulBySinglePre (l, r1, r8, r9, r10, r11, xs, zs) ↔
      if r9 = r11 then
        (let cond := (r10.toNat) < (zs.length)
        let _zs := zs.set (r10.toNat) r1
        let _r10 := r10 + (1 : BitVec width)
        cond)
      else
        (let cond := (r11.toNat) < (xs.length)
        let r2 := holEl (r11.toNat) xs
        let r0 := r8
        let r3 := (0 : BitVec width)
        let cond := cond ∧ (mcSingleMulAddPre (r0, r1, r2, r3))
        let (r0, _r1, r2, _r3) := mcSingleMulAdd (r0, r1, r2, r3)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r0
        let r1 := r2
        let r10 := r10 + (1 : BitVec width)
        let r11 := r11 + (1 : BitVec width)
        mcMulBySinglePre (l - 1, r1, r8, r9, r10, r11, xs, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcMulBySinglePre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcMulBySingleStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_top_two` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcTopTwoStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width)) × Prop
  | (l, r0, r1, r3, r8, r9, r11, ys) =>
    if r9 = r11 then
      (let r1 := r3
      (.inr (l, r0, r1, r8, r9, r11, ys), True))
    else
      (let r3 := r0
      let cond := (r11.toNat) < (ys.length)
      let r2 := holEl (r11.toNat) ys
      let r0 := r8
      let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
      let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
      let r1 := r2
      let r11 := r11 + (1 : BitVec width)
      (.inl (l - 1, r0, r1, r3, r8, r9, r11, ys), cond ∧ (l ≠ 0)))

/-- HOL `mc_top_two`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_top_two"
  (words_as_type_indexed_bitvec)]
noncomputable def mcTopTwo {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) :=
  holShortTailrec mcTopTwoStep

/-- The precondition of `mc_top_two`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_top_two_pre"
  (words_as_type_indexed_bitvec)]
def mcTopTwoPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width)) mcTopTwoStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_top_two`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_top_two_def"
  (words_as_type_indexed_bitvec)]
theorem mcTopTwo_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r11 : BitVec width} {ys : List (BitVec width)} :
    mcTopTwo (l, r0, r1, r3, r8, r9, r11, ys) =
      if r9 = r11 then
        (let r1 := r3
        (l, r0, r1, r8, r9, r11, ys))
      else
        (let r3 := r0
        let r2 := holEl (r11.toNat) ys
        let r0 := r8
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r2
        let r11 := r11 + (1 : BitVec width)
        mcTopTwo (l - 1, r0, r1, r3, r8, r9, r11, ys)) := by
  unfold mcTopTwo
  rw [holShortTailrec_eq_elim]
  simp only [mcTopTwoStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_top_two`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_top_two_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcTopTwoPre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r11 : BitVec width} {ys : List (BitVec width)} :
    mcTopTwoPre (l, r0, r1, r3, r8, r9, r11, ys) ↔
      if r9 = r11 then
        (let _r1 := r3
        True)
      else
        (let r3 := r0
        let cond := (r11.toNat) < (ys.length)
        let r2 := holEl (r11.toNat) ys
        let r0 := r8
        let cond := cond ∧ (mcSingleMulPre (r0, r1, r2))
        let (r0, _r1, r2) := mcSingleMul (r0, r1, r2)
        let r1 := r2
        let r11 := r11 + (1 : BitVec width)
        mcTopTwoPre (l - 1, r0, r1, r3, r8, r9, r11, ys) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcTopTwoPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcTopTwoStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_copy_down` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCopyDownStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × List (BitVec width)) × Prop
  | (l, r8, r10, r11, zs) =>
    if r8 = (0 : BitVec width) then
      (.inr (l, zs), True)
    else
      (let cond := (r10.toNat) < (zs.length)
      let r0 := holEl (r10.toNat) zs
      let r8 := r8 - (1 : BitVec width)
      let r10 := r10 + (1 : BitVec width)
      let cond := cond ∧ ((r11.toNat) < (zs.length))
      let zs := zs.set (r11.toNat) r0
      let r11 := r11 + (1 : BitVec width)
      (.inl (l - 1, r8, r10, r11, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_copy_down`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_down"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCopyDown {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Nat × List (BitVec width) :=
  holShortTailrec mcCopyDownStep

/-- The precondition of `mc_copy_down`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_down_pre"
  (words_as_type_indexed_bitvec)]
def mcCopyDownPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × List (BitVec width)) mcCopyDownStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_copy_down`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_down_def"
  (words_as_type_indexed_bitvec)]
theorem mcCopyDown_def {width : Nat} [NeZero width] {l : Nat} {r8 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcCopyDown (l, r8, r10, r11, zs) =
      if r8 = (0 : BitVec width) then
        (l, zs)
      else
        (let r0 := holEl (r10.toNat) zs
        let r8 := r8 - (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        let zs := zs.set (r11.toNat) r0
        let r11 := r11 + (1 : BitVec width)
        mcCopyDown (l - 1, r8, r10, r11, zs)) := by
  unfold mcCopyDown
  rw [holShortTailrec_eq_elim]
  simp only [mcCopyDownStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_copy_down`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_down_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCopyDownPre_def {width : Nat} [NeZero width] {l : Nat} {r8 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcCopyDownPre (l, r8, r10, r11, zs) ↔
      if r8 = (0 : BitVec width) then
        True
      else
        (let cond := (r10.toNat) < (zs.length)
        let r0 := holEl (r10.toNat) zs
        let r8 := r8 - (1 : BitVec width)
        let r10 := r10 + (1 : BitVec width)
        let cond := cond ∧ ((r11.toNat) < (zs.length))
        let zs := zs.set (r11.toNat) r0
        let r11 := r11 + (1 : BitVec width)
        mcCopyDownPre (l - 1, r8, r10, r11, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcCopyDownPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCopyDownStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_copy_over` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcCopyOverStep {width : Nat} [NeZero width] :
    Nat × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r10, xs, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, xs, zs), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r0 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r0
      (.inl (l - 1, r10, xs, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_copy_over`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_over"
  (words_as_type_indexed_bitvec)]
noncomputable def mcCopyOver {width : Nat} [NeZero width] :
    Nat × BitVec width × List (BitVec width) × List (BitVec width) → Nat × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcCopyOverStep

/-- The precondition of `mc_copy_over`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_over_pre"
  (words_as_type_indexed_bitvec)]
def mcCopyOverPre {width : Nat} [NeZero width] : Nat × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × List (BitVec width) × List (BitVec width)) mcCopyOverStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_copy_over`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_over_def"
  (words_as_type_indexed_bitvec)]
theorem mcCopyOver_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcCopyOver (l, r10, xs, zs) =
      if r10 = (0 : BitVec width) then
        (l, xs, zs)
      else
        (let r10 := r10 - (1 : BitVec width)
        let r0 := holEl (r10.toNat) xs
        let zs := zs.set (r10.toNat) r0
        mcCopyOver (l - 1, r10, xs, zs)) := by
  unfold mcCopyOver
  rw [holShortTailrec_eq_elim]
  simp only [mcCopyOverStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_copy_over`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_copy_over_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcCopyOverPre_def {width : Nat} [NeZero width] {l : Nat} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcCopyOverPre (l, r10, xs, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r0 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r0
        mcCopyOverPre (l - 1, r10, xs, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcCopyOverPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcCopyOverStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_div0` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDiv0Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r0, r1, r3, xs, ys, zs) =>
    let r6 := r0
    if r3 = (0 : BitVec width) then
      (let r0 := (0 : BitVec width)
      (.inr (l, r0, r3, r6, xs, ys, zs), True))
    else
      (let r11 := r0
      let r10 := r1
      let r0 := (0 : BitVec width)
      let cond := (mcMulZeroPre (l - 1, r0, r10, zs)) ∧ (l ≠ 0)
      let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
      let r10 := r11
      let cond := cond ∧ ((mcCopyOverPre (l - 1, r10, xs, zs)) ∧ (l ≠ 0))
      let (l, xs, zs) := mcCopyOver (l - 1, r10, xs, zs)
      let r0 := r1
      (.inr (l, r0, r3, r6, xs, ys, zs), cond))

/-- HOL `mc_div0`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div0"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDiv0 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDiv0Step

/-- The precondition of `mc_div0`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div0_pre"
  (words_as_type_indexed_bitvec)]
def mcDiv0Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcDiv0Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div0`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div0_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv0_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv0 (l, r0, r1, r3, xs, ys, zs) =
      let r6 := r0
      if r3 = (0 : BitVec width) then
        (let r0 := (0 : BitVec width)
        (l, r0, r3, r6, xs, ys, zs))
      else
        (let r11 := r0
        let r10 := r1
        let r0 := (0 : BitVec width)
        let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
        let r10 := r11
        let (l, xs, zs) := mcCopyOver (l - 1, r10, xs, zs)
        let r0 := r1
        (l, r0, r3, r6, xs, ys, zs)) := by
  unfold mcDiv0
  rw [holShortTailrec_eq_elim]
  simp only [mcDiv0Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div0`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div0_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv0Pre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv0Pre (l, r0, r1, r3, xs, ys, zs) ↔
      let _r6 := r0
      if r3 = (0 : BitVec width) then
        (let _r0 := (0 : BitVec width)
        True)
      else
        (let r11 := r0
        let r10 := r1
        let r0 := (0 : BitVec width)
        let cond := (mcMulZeroPre (l - 1, r0, r10, zs)) ∧ (l ≠ 0)
        let (l, _r10, zs) := mcMulZero (l - 1, r0, r10, zs)
        let r10 := r11
        let cond := cond ∧ ((mcCopyOverPre (l - 1, r10, xs, zs)) ∧ (l ≠ 0))
        let (_l, _xs, _zs) := mcCopyOver (l - 1, r10, xs, zs)
        let _r0 := r1
        cond) := by
  unfold mcDiv0Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDiv0Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDiv1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r0, _r1, r3, xs, ys, zs) =>
    (let r14 := r3
    let r2 := (0 : BitVec width)
    let r10 := r2
    let cond := (r10.toNat) < (ys.length)
    let r9 := holEl (r10.toNat) ys
    let r10 := r0
    let r8 := r0
    let cond := cond ∧ ((mcSimpleDivPre (l - 1, r2, r9, r10, xs, zs)) ∧ (l ≠ 0))
    let (l, r2, _r9, _r10, xs, zs) := mcSimpleDiv (l - 1, r2, r9, r10, xs, zs)
    let r6 := (0 : BitVec width)
    let r0 := r8
    let r3 := r14
    if r3 = (0 : BitVec width) then
      if r2 = (0 : BitVec width) then
        (.inr (l, r0, r3, r6, xs, ys, zs), cond)
      else
        (let r6 := (1 : BitVec width)
        (.inr (l, r0, r3, r6, xs, ys, zs), cond))
    else
      (let r0 := (1 : BitVec width)
      let r10 := (0 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r2
      if r2 = (0 : BitVec width) then
        (.inr (l, r0, r3, r6, xs, ys, zs), cond)
      else
        (let r6 := (1 : BitVec width)
        (.inr (l, r0, r3, r6, xs, ys, zs), cond))))

/-- HOL `mc_div1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDiv1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDiv1Step

/-- The precondition of `mc_div1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div1_pre"
  (words_as_type_indexed_bitvec)]
def mcDiv1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcDiv1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div1_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv1_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv1 (l, r0, r1, r3, xs, ys, zs) =
      (let r14 := r3
      let r2 := (0 : BitVec width)
      let r10 := r2
      let r9 := holEl (r10.toNat) ys
      let r10 := r0
      let r8 := r0
      let (l, r2, _r9, _r10, xs, zs) := mcSimpleDiv (l - 1, r2, r9, r10, xs, zs)
      let r6 := (0 : BitVec width)
      let r0 := r8
      let r3 := r14
      if r3 = (0 : BitVec width) then
        if r2 = (0 : BitVec width) then
          (l, r0, r3, r6, xs, ys, zs)
        else
          (let r6 := (1 : BitVec width)
          (l, r0, r3, r6, xs, ys, zs))
      else
        (let r0 := (1 : BitVec width)
        let r10 := (0 : BitVec width)
        let zs := zs.set (r10.toNat) r2
        if r2 = (0 : BitVec width) then
          (l, r0, r3, r6, xs, ys, zs)
        else
          (let r6 := (1 : BitVec width)
          (l, r0, r3, r6, xs, ys, zs)))) := by
  unfold mcDiv1
  rw [holShortTailrec_eq_elim]
  simp only [mcDiv1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv1Pre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv1Pre (l, r0, r1, r3, xs, ys, zs) ↔
      (let r14 := r3
      let r2 := (0 : BitVec width)
      let r10 := r2
      let cond := (r10.toNat) < (ys.length)
      let r9 := holEl (r10.toNat) ys
      let r10 := r0
      let r8 := r0
      let cond := cond ∧ ((mcSimpleDivPre (l - 1, r2, r9, r10, xs, zs)) ∧ (l ≠ 0))
      let (_l, r2, _r9, _r10, _xs, zs) := mcSimpleDiv (l - 1, r2, r9, r10, xs, zs)
      let _r6 := (0 : BitVec width)
      let _r0 := r8
      let r3 := r14
      if r3 = (0 : BitVec width) then
        if r2 = (0 : BitVec width) then
          cond
        else
          (let _r6 := (1 : BitVec width)
          cond)
      else
        (let _r0 := (1 : BitVec width)
        let r10 := (0 : BitVec width)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let _zs := zs.set (r10.toNat) r2
        if r2 = (0 : BitVec width) then
          cond
        else
          (let _r6 := (1 : BitVec width)
          cond))) := by
  unfold mcDiv1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDiv1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDiv2Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r7, r8, r10, r11, r18, xs, ys, zs) =>
    let r9 := r7
    let r2 := (0 : BitVec width)
    let cond := (mcSimpleDiv1Pre (l - 1, r2, r9, r10, zs)) ∧ (l ≠ 0)
    let (l, _r2, _r9, _r10, zs) := mcSimpleDiv1 (l - 1, r2, r9, r10, zs)
    let r9 := r11
    let r10 := r9
    let r7 := r8
    let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
    let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
    let r6 := r10
    let r10 := r9
    let r3 := r18
    let r8 := r7
    if r3 = (0 : BitVec width) then
      (let r11 := (0 : BitVec width)
      let cond := cond ∧ ((mcCopyDownPre (l - 1, r8, r10, r11, zs)) ∧ (l ≠ 0))
      let (l, zs) := mcCopyDown (l - 1, r8, r10, r11, zs)
      let r0 := r7
      (.inr (l, r0, r3, r6, xs, ys, zs), cond))
    else
      (let r0 := r9
      (.inr (l, r0, r3, r6, xs, ys, zs), cond))

/-- HOL `mc_div2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDiv2 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDiv2Step

/-- The precondition of `mc_div2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div2_pre"
  (words_as_type_indexed_bitvec)]
def mcDiv2Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcDiv2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div2_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv2_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r8 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r18 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv2 (l, r7, r8, r10, r11, r18, xs, ys, zs) =
      let r9 := r7
      let r2 := (0 : BitVec width)
      let (l, _r2, _r9, _r10, zs) := mcSimpleDiv1 (l - 1, r2, r9, r10, zs)
      let r9 := r11
      let r10 := r9
      let r7 := r8
      let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
      let r6 := r10
      let r10 := r9
      let r3 := r18
      let r8 := r7
      if r3 = (0 : BitVec width) then
        (let r11 := (0 : BitVec width)
        let (l, zs) := mcCopyDown (l - 1, r8, r10, r11, zs)
        let r0 := r7
        (l, r0, r3, r6, xs, ys, zs))
      else
        (let r0 := r9
        (l, r0, r3, r6, xs, ys, zs)) := by
  unfold mcDiv2
  rw [holShortTailrec_eq_elim]
  simp only [mcDiv2Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv2Pre_def {width : Nat} [NeZero width] {l : Nat} {r7 : BitVec width} {r8 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {r18 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv2Pre (l, r7, r8, r10, r11, r18, xs, ys, zs) ↔
      let r9 := r7
      let r2 := (0 : BitVec width)
      let cond := (mcSimpleDiv1Pre (l - 1, r2, r9, r10, zs)) ∧ (l ≠ 0)
      let (l, _r2, _r9, _r10, zs) := mcSimpleDiv1 (l - 1, r2, r9, r10, zs)
      let r9 := r11
      let r10 := r9
      let r7 := r8
      let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
      let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
      let _r6 := r10
      let r10 := r9
      let r3 := r18
      let r8 := r7
      if r3 = (0 : BitVec width) then
        (let r11 := (0 : BitVec width)
        let cond := cond ∧ ((mcCopyDownPre (l - 1, r8, r10, r11, zs)) ∧ (l ≠ 0))
        let (_l, _zs) := mcCopyDown (l - 1, r8, r10, r11, zs)
        let _r0 := r7
        cond)
      else
        (let _r0 := r9
        cond) := by
  unfold mcDiv2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDiv2Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div3` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDiv3Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r2, r7, r9, r18, r19, xs, ys, zs) =>
    let r1 := (0 : BitVec width)
    let r8 := r2
    let r10 := r1
    let r11 := r1
    let cond := (mcMulBySinglePre (l - 1, r1, r8, r9, r10, r11, xs, zs)) ∧ (l ≠ 0)
    let (l, _r1, r8, _r9, r10, xs, zs) := mcMulBySingle (l - 1, r1, r8, r9, r10, r11, xs, zs)
    let r1 := (0 : BitVec width)
    let cond := cond ∧ ((r10.toNat) < (zs.length))
    let zs := zs.set (r10.toNat) r1
    let r0 := (0 : BitVec width)
    let r1 := r0
    let r3 := r0
    let r11 := r0
    let r9 := r7
    let cond := cond ∧ ((mcTopTwoPre (l - 1, r0, r1, r3, r8, r9, r11, ys)) ∧ (l ≠ 0))
    let (l, r0, r1, r8, r9, _r11, ys) := mcTopTwo (l - 1, r0, r1, r3, r8, r9, r11, ys)
    let r7 := r8
    let r11 := r9
    let r10 := r19
    let r10 := r10 - r9
    let r10 := r10 + (2 : BitVec width)
    let r14 := r0
    let r15 := r1
    let r17 := r10
    let cond := cond ∧ ((mcDivLoopPre (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)) ∧ (l ≠ 0))
    let (l, r7, r9, _r10, _r11, _r14, _r15, ys, zs) := mcDivLoop (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)
    let r8 := r17
    let r11 := r9
    let r10 := r9
    let cond := cond ∧ (mcDiv2Pre (l, r7, r8, r10, r11, r18, xs, ys, zs))
    let (l, r0, r3, r6, xs, ys, zs) := mcDiv2 (l, r7, r8, r10, r11, r18, xs, ys, zs)
    (.inr (l, r0, r3, r6, xs, ys, zs), cond)

/-- HOL `mc_div3`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div3"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDiv3 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDiv3Step

/-- The precondition of `mc_div3`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div3_pre"
  (words_as_type_indexed_bitvec)]
def mcDiv3Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcDiv3Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div3_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv3_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r7 : BitVec width} {r9 : BitVec width} {r18 : BitVec width} {r19 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv3 (l, r2, r7, r9, r18, r19, xs, ys, zs) =
      let r1 := (0 : BitVec width)
      let r8 := r2
      let r10 := r1
      let r11 := r1
      let (l, _r1, r8, _r9, r10, xs, zs) := mcMulBySingle (l - 1, r1, r8, r9, r10, r11, xs, zs)
      let r1 := (0 : BitVec width)
      let zs := zs.set (r10.toNat) r1
      let r0 := (0 : BitVec width)
      let r1 := r0
      let r3 := r0
      let r11 := r0
      let r9 := r7
      let (l, r0, r1, r8, r9, _r11, ys) := mcTopTwo (l - 1, r0, r1, r3, r8, r9, r11, ys)
      let r7 := r8
      let r11 := r9
      let r10 := r19
      let r10 := r10 - r9
      let r10 := r10 + (2 : BitVec width)
      let r14 := r0
      let r15 := r1
      let r17 := r10
      let (l, r7, r9, _r10, _r11, _r14, _r15, ys, zs) := mcDivLoop (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)
      let r8 := r17
      let r11 := r9
      let r10 := r9
      let (l, r0, r3, r6, xs, ys, zs) := mcDiv2 (l, r7, r8, r10, r11, r18, xs, ys, zs)
      (l, r0, r3, r6, xs, ys, zs) := by
  unfold mcDiv3
  rw [holShortTailrec_eq_elim]
  simp only [mcDiv3Step, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div3_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDiv3Pre_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r7 : BitVec width} {r9 : BitVec width} {r18 : BitVec width} {r19 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv3Pre (l, r2, r7, r9, r18, r19, xs, ys, zs) ↔
      let r1 := (0 : BitVec width)
      let r8 := r2
      let r10 := r1
      let r11 := r1
      let cond := (mcMulBySinglePre (l - 1, r1, r8, r9, r10, r11, xs, zs)) ∧ (l ≠ 0)
      let (l, _r1, r8, _r9, r10, xs, zs) := mcMulBySingle (l - 1, r1, r8, r9, r10, r11, xs, zs)
      let r1 := (0 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r1
      let r0 := (0 : BitVec width)
      let r1 := r0
      let r3 := r0
      let r11 := r0
      let r9 := r7
      let cond := cond ∧ ((mcTopTwoPre (l - 1, r0, r1, r3, r8, r9, r11, ys)) ∧ (l ≠ 0))
      let (l, r0, r1, r8, r9, _r11, ys) := mcTopTwo (l - 1, r0, r1, r3, r8, r9, r11, ys)
      let r7 := r8
      let r11 := r9
      let r10 := r19
      let r10 := r10 - r9
      let r10 := r10 + (2 : BitVec width)
      let r14 := r0
      let r15 := r1
      let r17 := r10
      let cond := cond ∧ ((mcDivLoopPre (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)) ∧ (l ≠ 0))
      let (l, r7, r9, _r10, _r11, _r14, _r15, ys, zs) := mcDivLoop (l - 1, r7, r9, r10, r11, r14, r15, ys, zs)
      let r8 := r17
      let r11 := r9
      let r10 := r9
      let cond := cond ∧ (mcDiv2Pre (l, r7, r8, r10, r11, r18, xs, ys, zs))
      let (_l, _r0, _r3, _r6, _xs, _ys, _zs) := mcDiv2 (l, r7, r8, r10, r11, r18, xs, ys, zs)
      cond := by
  unfold mcDiv3Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDiv3Step, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r0, r1, r3, xs, ys, zs) =>
    if r0 < r1 then
      (let cond := mcDiv0Pre (l, r0, r1, r3, xs, ys, zs)
      let (l, r0, r3, r6, xs, ys, zs) := mcDiv0 (l, r0, r1, r3, xs, ys, zs)
      (.inr (l, r0, r3, r6, xs, ys, zs), cond))
    else
      if r1 = (1 : BitVec width) then
        (let cond := mcDiv1Pre (l, r0, r1, r3, xs, ys, zs)
        let (l, r0, r3, r6, xs, ys, zs) := mcDiv1 (l, r0, r1, r3, xs, ys, zs)
        (.inr (l, r0, r3, r6, xs, ys, zs), cond))
      else
        (let r18 := r3
        let r19 := r0
        let r7 := r1
        let r9 := r0
        let r10 := r1
        let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (ys.length)
        let r1 := holEl (r10.toNat) ys
        let r2 := (1 : BitVec width)
        let cond := cond ∧ ((mcCalcDPre (l - 1, r1, r2)) ∧ (l ≠ 0))
        let (l, r2) := mcCalcD (l - 1, r1, r2)
        let cond := cond ∧ (mcDiv3Pre (l, r2, r7, r9, r18, r19, xs, ys, zs))
        let (l, r0, r3, r6, xs, ys, zs) := mcDiv3 (l, r2, r7, r9, r18, r19, xs, ys, zs)
        (.inr (l, r0, r3, r6, xs, ys, zs), cond))

/-- HOL `mc_div`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDiv {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivStep

/-- The precondition of `mc_div`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_pre"
  (words_as_type_indexed_bitvec)]
def mcDivPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcDivStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_def" 2991
  (words_as_type_indexed_bitvec)]
theorem mcDiv_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDiv (l, r0, r1, r3, xs, ys, zs) =
      if r0 < r1 then
        (let (l, r0, r3, r6, xs, ys, zs) := mcDiv0 (l, r0, r1, r3, xs, ys, zs)
        (l, r0, r3, r6, xs, ys, zs))
      else
        if r1 = (1 : BitVec width) then
          (let (l, r0, r3, r6, xs, ys, zs) := mcDiv1 (l, r0, r1, r3, xs, ys, zs)
          (l, r0, r3, r6, xs, ys, zs))
        else
          (let r18 := r3
          let r19 := r0
          let r7 := r1
          let r9 := r0
          let r10 := r1
          let r10 := r10 - (1 : BitVec width)
          let r1 := holEl (r10.toNat) ys
          let r2 := (1 : BitVec width)
          let (l, r2) := mcCalcD (l - 1, r1, r2)
          let (l, r0, r3, r6, xs, ys, zs) := mcDiv3 (l, r2, r7, r9, r18, r19, xs, ys, zs)
          (l, r0, r3, r6, xs, ys, zs)) := by
  unfold mcDiv
  rw [holShortTailrec_eq_elim]
  simp only [mcDivStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_pre_def" 2991
  (words_as_type_indexed_bitvec)]
theorem mcDivPre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivPre (l, r0, r1, r3, xs, ys, zs) ↔
      if r0 < r1 then
        (let cond := mcDiv0Pre (l, r0, r1, r3, xs, ys, zs)
        let (_l, _r0, _r3, _r6, _xs, _ys, _zs) := mcDiv0 (l, r0, r1, r3, xs, ys, zs)
        cond)
      else
        if r1 = (1 : BitVec width) then
          (let cond := mcDiv1Pre (l, r0, r1, r3, xs, ys, zs)
          let (_l, _r0, _r3, _r6, _xs, _ys, _zs) := mcDiv1 (l, r0, r1, r3, xs, ys, zs)
          cond)
        else
          (let r18 := r3
          let r19 := r0
          let r7 := r1
          let r9 := r0
          let r10 := r1
          let r10 := r10 - (1 : BitVec width)
          let cond := (r10.toNat) < (ys.length)
          let r1 := holEl (r10.toNat) ys
          let r2 := (1 : BitVec width)
          let cond := cond ∧ ((mcCalcDPre (l - 1, r1, r2)) ∧ (l ≠ 0))
          let (l, r2) := mcCalcD (l - 1, r1, r2)
          let cond := cond ∧ (mcDiv3Pre (l, r2, r7, r9, r18, r19, xs, ys, zs))
          let (_l, _r0, _r3, _r6, _xs, _ys, _zs) := mcDiv3 (l, r2, r7, r9, r18, r19, xs, ys, zs)
          cond) := by
  unfold mcDivPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
