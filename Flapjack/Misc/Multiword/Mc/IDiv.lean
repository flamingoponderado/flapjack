module

public import Flapjack.Misc.Multiword.Mc.Div

@[expose] public section

/-! Machine-code-style signed division functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_add1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAdd1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width)) × Prop
  | (l, r2, r10, r11, zs) =>
    if r10 = r11 then
      (let r0 := (1 : BitVec width)
      let cond := (r10.toNat) < (zs.length)
      let zs := zs.set (r10.toNat) r0
      let r11 := r11 + (1 : BitVec width)
      (.inr (l, r11, zs), cond))
    else
      (let cond := (r10.toNat) < (zs.length)
      let r0 := holEl (r10.toNat) zs
      if r0 = r2 then
        (let r0 := (0 : BitVec width)
        let zs := zs.set (r10.toNat) r0
        let r10 := r10 + (1 : BitVec width)
        (.inl (l - 1, r2, r10, r11, zs), cond ∧ (l ≠ 0)))
      else
        (let r0 := r0 + (1 : BitVec width)
        let zs := zs.set (r10.toNat) r0
        (.inr (l, r11, zs), cond)))

/-- HOL `mc_add1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAdd1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × List (BitVec width) :=
  holShortTailrec mcAdd1Step

/-- The precondition of `mc_add1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_pre"
  (words_as_type_indexed_bitvec)]
def mcAdd1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width)) mcAdd1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdd1_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcAdd1 (l, r2, r10, r11, zs) =
      if r10 = r11 then
        (let r0 := (1 : BitVec width)
        let zs := zs.set (r10.toNat) r0
        let r11 := r11 + (1 : BitVec width)
        (l, r11, zs))
      else
        (let r0 := holEl (r10.toNat) zs
        if r0 = r2 then
          (let r0 := (0 : BitVec width)
          let zs := zs.set (r10.toNat) r0
          let r10 := r10 + (1 : BitVec width)
          mcAdd1 (l - 1, r2, r10, r11, zs))
        else
          (let r0 := r0 + (1 : BitVec width)
          let zs := zs.set (r10.toNat) r0
          (l, r11, zs))) := by
  unfold mcAdd1
  rw [holShortTailrec_eq_elim]
  simp only [mcAdd1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdd1Pre_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcAdd1Pre (l, r2, r10, r11, zs) ↔
      if r10 = r11 then
        (let r0 := (1 : BitVec width)
        let cond := (r10.toNat) < (zs.length)
        let _zs := zs.set (r10.toNat) r0
        let _r11 := r11 + (1 : BitVec width)
        cond)
      else
        (let cond := (r10.toNat) < (zs.length)
        let r0 := holEl (r10.toNat) zs
        if r0 = r2 then
          (let r0 := (0 : BitVec width)
          let zs := zs.set (r10.toNat) r0
          let r10 := r10 + (1 : BitVec width)
          mcAdd1Pre (l - 1, r2, r10, r11, zs) ∧ (cond ∧ (l ≠ 0)))
        else
          (let r0 := r0 + (1 : BitVec width)
          let _zs := zs.set (r10.toNat) r0
          cond)) := by
  unfold mcAdd1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAdd1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_add1_call` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAdd1CallStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width)) × Prop
  | (l, r2, r6, r11, zs) =>
    if r2 = (0 : BitVec width) then
      (.inr (l, r11, zs), True)
    else
      if r6 = (0 : BitVec width) then
        (.inr (l, r11, zs), True)
      else
        (let r2 := (0 : BitVec width)
        let r10 := r2
        let r2 := ~~~r2
        let cond := (mcAdd1Pre (l - 1, r2, r10, r11, zs)) ∧ (l ≠ 0)
        let (l, r11, zs) := mcAdd1 (l - 1, r2, r10, r11, zs)
        (.inr (l, r11, zs), cond))

/-- HOL `mc_add1_call`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_call"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAdd1Call {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × List (BitVec width) :=
  holShortTailrec mcAdd1CallStep

/-- The precondition of `mc_add1_call`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_call_pre"
  (words_as_type_indexed_bitvec)]
def mcAdd1CallPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width)) mcAdd1CallStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add1_call`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_call_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdd1Call_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r6 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcAdd1Call (l, r2, r6, r11, zs) =
      if r2 = (0 : BitVec width) then
        (l, r11, zs)
      else
        if r6 = (0 : BitVec width) then
          (l, r11, zs)
        else
          (let r2 := (0 : BitVec width)
          let r10 := r2
          let r2 := ~~~r2
          let (l, r11, zs) := mcAdd1 (l - 1, r2, r10, r11, zs)
          (l, r11, zs)) := by
  unfold mcAdd1Call
  rw [holShortTailrec_eq_elim]
  simp only [mcAdd1CallStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add1_call`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add1_call_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdd1CallPre_def {width : Nat} [NeZero width] {l : Nat} {r2 : BitVec width} {r6 : BitVec width} {r11 : BitVec width} {zs : List (BitVec width)} :
    mcAdd1CallPre (l, r2, r6, r11, zs) ↔
      if r2 = (0 : BitVec width) then
        True
      else
        if r6 = (0 : BitVec width) then
          True
        else
          (let r2 := (0 : BitVec width)
          let r10 := r2
          let r2 := ~~~r2
          let cond := (mcAdd1Pre (l - 1, r2, r10, r11, zs)) ∧ (l ≠ 0)
          let (_l, _r11, _zs) := mcAdd1 (l - 1, r2, r10, r11, zs)
          cond) := by
  unfold mcAdd1CallPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAdd1CallStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub_aux1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSubAux1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r4, r8, r9, r10, ys, zs) =>
    if r1 = (1 : BitVec width) then
      (let r1 := (0 : BitVec width)
      (.inr (l, r1, r4, r8, r9, r10, ys, zs), True))
    else
      (let r1 := r1 - (1 : BitVec width)
      let cond := (r10.toNat) < (ys.length)
      let r8 := holEl (r10.toNat) ys
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let r9 := holEl (r10.toNat) zs
      let cond := cond ∧ ((r4 ≠ (0 : BitVec width)) → (r4 = (1 : BitVec width)))
      let (r8, r4) := singleSubWord r8 r9 r4
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r4, r8, r9, r10, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_div_sub_aux1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSubAux1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivSubAux1Step

/-- The precondition of `mc_div_sub_aux1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux1_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSubAux1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivSubAux1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub_aux1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux1_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubAux1_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r4 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubAux1 (l, r1, r4, r8, r9, r10, ys, zs) =
      if r1 = (1 : BitVec width) then
        (let r1 := (0 : BitVec width)
        (l, r1, r4, r8, r9, r10, ys, zs))
      else
        (let r1 := r1 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) ys
        let r9 := holEl (r10.toNat) zs
        let (r8, r4) := singleSubWord r8 r9 r4
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcDivSubAux1 (l - 1, r1, r4, r8, r9, r10, ys, zs)) := by
  unfold mcDivSubAux1
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSubAux1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub_aux1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubAux1Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r4 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubAux1Pre (l, r1, r4, r8, r9, r10, ys, zs) ↔
      if r1 = (1 : BitVec width) then
        (let _r1 := (0 : BitVec width)
        True)
      else
        (let r1 := r1 - (1 : BitVec width)
        let cond := (r10.toNat) < (ys.length)
        let r8 := holEl (r10.toNat) ys
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let r9 := holEl (r10.toNat) zs
        let cond := cond ∧ ((r4 ≠ (0 : BitVec width)) → (r4 = (1 : BitVec width)))
        let (r8, r4) := singleSubWord r8 r9 r4
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcDivSubAux1Pre (l - 1, r1, r4, r8, r9, r10, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcDivSubAux1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSubAux1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub_aux` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSubAuxStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r8, r9, ys, zs) =>
    (let r10 := (0 : BitVec width)
    let r1 := r1 + (1 : BitVec width)
    let r4 := (1 : BitVec width)
    let cond := (mcDivSubAux1Pre (l - 1, r1, r4, r8, r9, r10, ys, zs)) ∧ (l ≠ 0)
    let (l, r1, r4, r8, r9, r10, ys, zs) := mcDivSubAux1 (l - 1, r1, r4, r8, r9, r10, ys, zs)
    (.inr (l, r1, r4, r8, r9, r10, ys, zs), cond))

/-- HOL `mc_div_sub_aux`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSubAux {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivSubAuxStep

/-- The precondition of `mc_div_sub_aux`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSubAuxPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivSubAuxStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub_aux`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux_def" 3431
  (words_as_type_indexed_bitvec)]
theorem mcDivSubAux_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubAux (l, r1, r8, r9, ys, zs) =
      (let r10 := (0 : BitVec width)
      let r1 := r1 + (1 : BitVec width)
      let r4 := (1 : BitVec width)
      let (l, r1, r4, r8, r9, r10, ys, zs) := mcDivSubAux1 (l - 1, r1, r4, r8, r9, r10, ys, zs)
      (l, r1, r4, r8, r9, r10, ys, zs)) := by
  unfold mcDivSubAux
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSubAuxStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub_aux`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_aux_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubAuxPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubAuxPre (l, r1, r8, r9, ys, zs) ↔
      (let r10 := (0 : BitVec width)
      let r1 := r1 + (1 : BitVec width)
      let r4 := (1 : BitVec width)
      let cond := (mcDivSubAux1Pre (l - 1, r1, r4, r8, r9, r10, ys, zs)) ∧ (l ≠ 0)
      let (_l, _r1, _r4, _r8, _r9, _r10, _ys, _zs) := mcDivSubAux1 (l - 1, r1, r4, r8, r9, r10, ys, zs)
      cond) := by
  unfold mcDivSubAuxPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSubAuxStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSub1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r8, r9, ys, zs) =>
    (let cond := mcDivSubAuxPre (l, r1, r8, r9, ys, zs)
    let (l, r1, _r4, r8, r9, r10, ys, zs) := mcDivSubAux (l, r1, r8, r9, ys, zs)
    (.inr (l, r1, r8, r9, r10, ys, zs), cond))

/-- HOL `mc_div_sub1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSub1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivSub1Step

/-- The precondition of `mc_div_sub1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub1_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSub1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcDivSub1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub1_def" 3451
  (words_as_type_indexed_bitvec)]
theorem mcDivSub1_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSub1 (l, r1, r8, r9, ys, zs) =
      (let (l, r1, _r4, r8, r9, r10, ys, zs) := mcDivSubAux (l, r1, r8, r9, ys, zs)
      (l, r1, r8, r9, r10, ys, zs)) := by
  unfold mcDivSub1
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSub1Step, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSub1Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSub1Pre (l, r1, r8, r9, ys, zs) ↔
      (let cond := mcDivSubAuxPre (l, r1, r8, r9, ys, zs)
      let (_l, _r1, _r4, _r8, _r9, _r10, _ys, _zs) := mcDivSubAux (l, r1, r8, r9, ys, zs)
      cond) := by
  unfold mcDivSub1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSub1Step, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_div_sub_call` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcDivSubCallStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, r6, ys, zs) =>
    if r2 = (0 : BitVec width) then
      (.inr (l, r6, ys, zs), True)
    else
      if r6 = (0 : BitVec width) then
        (.inr (l, r6, ys, zs), True)
      else
        (let r8 := r6
        let r9 := r6
        let r3 := r1
        let cond := mcDivSub1Pre (l, r1, r8, r9, ys, zs)
        let (l, _r1, r8, _r9, _r10, ys, zs) := mcDivSub1 (l, r1, r8, r9, ys, zs)
        let r10 := r3
        let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
        let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
        let r6 := r10
        (.inr (l, r6, ys, zs), cond))

/-- HOL `mc_div_sub_call`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_call"
  (words_as_type_indexed_bitvec)]
noncomputable def mcDivSubCall {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcDivSubCallStep

/-- The precondition of `mc_div_sub_call`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_call_pre"
  (words_as_type_indexed_bitvec)]
def mcDivSubCallPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width)) mcDivSubCallStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_div_sub_call`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_call_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubCall_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r6 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubCall (l, r1, r2, r6, ys, zs) =
      if r2 = (0 : BitVec width) then
        (l, r6, ys, zs)
      else
        if r6 = (0 : BitVec width) then
          (l, r6, ys, zs)
        else
          (let r8 := r6
          let r9 := r6
          let r3 := r1
          let (l, _r1, r8, _r9, _r10, ys, zs) := mcDivSub1 (l, r1, r8, r9, ys, zs)
          let r10 := r3
          let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
          let r6 := r10
          (l, r6, ys, zs)) := by
  unfold mcDivSubCall
  rw [holShortTailrec_eq_elim]
  simp only [mcDivSubCallStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_div_sub_call`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_sub_call_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcDivSubCallPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r6 : BitVec width} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcDivSubCallPre (l, r1, r2, r6, ys, zs) ↔
      if r2 = (0 : BitVec width) then
        True
      else
        if r6 = (0 : BitVec width) then
          True
        else
          (let r8 := r6
          let r9 := r6
          let r3 := r1
          let cond := mcDivSub1Pre (l, r1, r8, r9, ys, zs)
          let (l, _r1, r8, _r9, _r10, _ys, zs) := mcDivSub1 (l, r1, r8, r9, ys, zs)
          let r10 := r3
          let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
          let (_l, _r8, r10, _zs) := mcFix (l - 1, r8, r10, zs)
          let _r6 := r10
          cond) := by
  unfold mcDivSubCallPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcDivSubCallStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_idiv_mod_header` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIdivModHeaderStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width → (BitVec width × BitVec width ⊕ BitVec width) × Prop
  | (r6, r11) =>
    if r6 = (0 : BitVec width) then
      (.inr r6, True)
    else
      (let r6 := r6 <<< 1
      if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
        (.inr r6, True)
      else
        (let r6 := r6 + (1 : BitVec width)
        (.inr r6, True)))

/-- HOL `mc_idiv_mod_header`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_mod_header"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIdivModHeader {width : Nat} [NeZero width] :
    BitVec width × BitVec width → BitVec width :=
  holShortTailrec mcIdivModHeaderStep

/-- The precondition of `mc_idiv_mod_header`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_mod_header_pre"
  (words_as_type_indexed_bitvec)]
def mcIdivModHeaderPre {width : Nat} [NeZero width] : BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width) mcIdivModHeaderStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_idiv_mod_header`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_mod_header_def"
  (words_as_type_indexed_bitvec)]
theorem mcIdivModHeader_def {width : Nat} [NeZero width] {r6 : BitVec width} {r11 : BitVec width} :
    mcIdivModHeader (r6, r11) =
      if r6 = (0 : BitVec width) then
        r6
      else
        (let r6 := r6 <<< 1
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          r6
        else
          (let r6 := r6 + (1 : BitVec width)
          r6)) := by
  unfold mcIdivModHeader
  rw [holShortTailrec_eq_elim]
  simp only [mcIdivModHeaderStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_idiv_mod_header`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_mod_header_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIdivModHeaderPre_def {width : Nat} [NeZero width] {r6 : BitVec width} {r11 : BitVec width} :
    mcIdivModHeaderPre (r6, r11) ↔
      if r6 = (0 : BitVec width) then
        True
      else
        (let r6 := r6 <<< 1
        if (r11 &&& (1 : BitVec width)) = (0 : BitVec width) then
          True
        else
          (let _r6 := r6 + (1 : BitVec width)
          True)) := by
  unfold mcIdivModHeaderPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIdivModHeaderStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_idiv0` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIdiv0Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r0, r3, r6, r11, r20, xs, ys, zs) =>
    if r3 = (0 : BitVec width) then
      (let r10 := r0
      let r8 := r10
      let cond := (mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0)
      let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
      let r11 := r10
      let r2 := r20
      let r3 := r2
      let cond := cond ∧ (mcAdd1CallPre (l, r2, r6, r11, zs))
      let (l, r11, zs) := mcAdd1Call (l, r2, r6, r11, zs)
      if r11 = (0 : BitVec width) then
        (.inr (l, r11, xs, ys, zs), cond)
      else
        (let r11 := r11 <<< 1
        let r11 := r11 + r3
        (.inr (l, r11, xs, ys, zs), cond)))
    else
      (let r2 := r20
      let r1 := r11
      let r1 := r1 >>> 1
      let cond := mcDivSubCallPre (l, r1, r2, r6, ys, zs)
      let (l, r6, ys, zs) := mcDivSubCall (l, r1, r2, r6, ys, zs)
      let r6 := mcIdivModHeader (r6, r11)
      let r11 := r6
      (.inr (l, r11, xs, ys, zs), cond))

/-- HOL `mc_idiv0`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv0"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIdiv0 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIdiv0Step

/-- The precondition of `mc_idiv0`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv0_pre"
  (words_as_type_indexed_bitvec)]
def mcIdiv0Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcIdiv0Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_idiv0`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv0_def"
  (words_as_type_indexed_bitvec)]
theorem mcIdiv0_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r3 : BitVec width} {r6 : BitVec width} {r11 : BitVec width} {r20 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIdiv0 (l, r0, r3, r6, r11, r20, xs, ys, zs) =
      if r3 = (0 : BitVec width) then
        (let r10 := r0
        let r8 := r10
        let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
        let r11 := r10
        let r2 := r20
        let r3 := r2
        let (l, r11, zs) := mcAdd1Call (l, r2, r6, r11, zs)
        if r11 = (0 : BitVec width) then
          (l, r11, xs, ys, zs)
        else
          (let r11 := r11 <<< 1
          let r11 := r11 + r3
          (l, r11, xs, ys, zs)))
      else
        (let r2 := r20
        let r1 := r11
        let r1 := r1 >>> 1
        let (l, r6, ys, zs) := mcDivSubCall (l, r1, r2, r6, ys, zs)
        let r6 := mcIdivModHeader (r6, r11)
        let r11 := r6
        (l, r11, xs, ys, zs)) := by
  unfold mcIdiv0
  rw [holShortTailrec_eq_elim]
  simp only [mcIdiv0Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_idiv0`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv0_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIdiv0Pre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r3 : BitVec width} {r6 : BitVec width} {r11 : BitVec width} {r20 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIdiv0Pre (l, r0, r3, r6, r11, r20, xs, ys, zs) ↔
      if r3 = (0 : BitVec width) then
        (let r10 := r0
        let r8 := r10
        let cond := (mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0)
        let (l, _r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
        let r11 := r10
        let r2 := r20
        let r3 := r2
        let cond := cond ∧ (mcAdd1CallPre (l, r2, r6, r11, zs))
        let (_l, r11, _zs) := mcAdd1Call (l, r2, r6, r11, zs)
        if r11 = (0 : BitVec width) then
          cond
        else
          (let r11 := r11 <<< 1
          let _r11 := r11 + r3
          cond))
      else
        (let r2 := r20
        let r1 := r11
        let r1 := r1 >>> 1
        let cond := mcDivSubCallPre (l, r1, r2, r6, ys, zs)
        let (_l, r6, _ys, _zs) := mcDivSubCall (l, r1, r2, r6, ys, zs)
        let r6 := mcIdivModHeader (r6, r11)
        let _r11 := r6
        cond) := by
  unfold mcIdiv0Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIdiv0Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_idiv` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIdivStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r3, r10, r11, xs, ys, zs) =>
    (let r0 := r10 >>> 1
    let r1 := r11 >>> 1
    let r10 := r10 ^^^ r11
    let r10 := r10 &&& (1 : BitVec width)
    let r20 := r10
    let r21 := r11
    let cond := mcDivPre (l, r0, r1, r3, xs, ys, zs)
    let (l, r0, r3, r6, xs, ys, zs) := mcDiv (l, r0, r1, r3, xs, ys, zs)
    let r11 := r21
    let cond := cond ∧ (mcIdiv0Pre (l, r0, r3, r6, r11, r20, xs, ys, zs))
    let (l, r11, xs, ys, zs) := mcIdiv0 (l, r0, r3, r6, r11, r20, xs, ys, zs)
    (.inr (l, r11, xs, ys, zs), cond))

/-- HOL `mc_idiv`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIdiv {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIdivStep

/-- The precondition of `mc_idiv`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_pre"
  (words_as_type_indexed_bitvec)]
def mcIdivPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcIdivStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_idiv`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_def" 3616
  (words_as_type_indexed_bitvec)]
theorem mcIdiv_def {width : Nat} [NeZero width] {l : Nat} {r3 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIdiv (l, r3, r10, r11, xs, ys, zs) =
      (let r0 := r10 >>> 1
      let r1 := r11 >>> 1
      let r10 := r10 ^^^ r11
      let r10 := r10 &&& (1 : BitVec width)
      let r20 := r10
      let r21 := r11
      let (l, r0, r3, r6, xs, ys, zs) := mcDiv (l, r0, r1, r3, xs, ys, zs)
      let r11 := r21
      let (l, r11, xs, ys, zs) := mcIdiv0 (l, r0, r3, r6, r11, r20, xs, ys, zs)
      (l, r11, xs, ys, zs)) := by
  unfold mcIdiv
  rw [holShortTailrec_eq_elim]
  simp only [mcIdivStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_idiv`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_idiv_pre_def" 3616
  (words_as_type_indexed_bitvec)]
theorem mcIdivPre_def {width : Nat} [NeZero width] {l : Nat} {r3 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIdivPre (l, r3, r10, r11, xs, ys, zs) ↔
      (let r0 := r10 >>> 1
      let r1 := r11 >>> 1
      let r10 := r10 ^^^ r11
      let r10 := r10 &&& (1 : BitVec width)
      let r20 := r10
      let r21 := r11
      let cond := mcDivPre (l, r0, r1, r3, xs, ys, zs)
      let (l, r0, r3, r6, xs, ys, zs) := mcDiv (l, r0, r1, r3, xs, ys, zs)
      let r11 := r21
      let cond := cond ∧ (mcIdiv0Pre (l, r0, r3, r6, r11, r20, xs, ys, zs))
      let (_l, _r11, _xs, _ys, _zs) := mcIdiv0 (l, r0, r3, r6, r11, r20, xs, ys, zs)
      cond) := by
  unfold mcIdivPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIdivStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
