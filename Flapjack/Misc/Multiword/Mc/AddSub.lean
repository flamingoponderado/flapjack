module

public import Flapjack.Misc.Multiword.Mc.Compare

@[expose] public section

/-! Machine-code-style addition and subtraction functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_add_loop2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAddLoop2Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r3, r8, r9, r10, xs, zs) =>
    if r1 = (1 : BitVec width) then
      (let r1 := (0 : BitVec width)
      (.inr (l, r1, r3, r8, r9, r10, xs, zs), True))
    else
      (let r1 := r1 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r8 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
      let (r8, r3) := singleAddWord r8 r9 r3
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r3, r8, r9, r10, xs, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_add_loop2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAddLoop2 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcAddLoop2Step

/-- The precondition of `mc_add_loop2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop2_pre"
  (words_as_type_indexed_bitvec)]
def mcAddLoop2Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcAddLoop2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add_loop2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop2_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddLoop2_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoop2 (l, r1, r3, r8, r9, r10, xs, zs) =
      if r1 = (1 : BitVec width) then
        (let r1 := (0 : BitVec width)
        (l, r1, r3, r8, r9, r10, xs, zs))
      else
        (let r1 := r1 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) xs
        let (r8, r3) := singleAddWord r8 r9 r3
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcAddLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)) := by
  unfold mcAddLoop2
  rw [holShortTailrec_eq_elim]
  simp only [mcAddLoop2Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add_loop2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddLoop2Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoop2Pre (l, r1, r3, r8, r9, r10, xs, zs) ↔
      if r1 = (1 : BitVec width) then
        (let _r1 := (0 : BitVec width)
        True)
      else
        (let r1 := r1 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r8 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
        let (r8, r3) := singleAddWord r8 r9 r3
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcAddLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcAddLoop2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAddLoop2Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_add_loop1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAddLoop1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r3, r8, r9, r10, xs, ys, zs) =>
    if r1 = (1 : BitVec width) then
      (let r1 := (0 : BitVec width)
      (.inr (l, r1, r3, r8, r9, r10, xs, ys, zs), True))
    else
      (let r1 := r1 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r8 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r10.toNat) < (ys.length))
      let r9 := holEl (r10.toNat) ys
      let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
      let (r8, r3) := singleAddWord r8 r9 r3
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r3, r8, r9, r10, xs, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_add_loop1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAddLoop1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcAddLoop1Step

/-- The precondition of `mc_add_loop1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop1_pre"
  (words_as_type_indexed_bitvec)]
def mcAddLoop1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcAddLoop1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add_loop1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop1_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddLoop1_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoop1 (l, r1, r3, r8, r9, r10, xs, ys, zs) =
      if r1 = (1 : BitVec width) then
        (let r1 := (0 : BitVec width)
        (l, r1, r3, r8, r9, r10, xs, ys, zs))
      else
        (let r1 := r1 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) xs
        let r9 := holEl (r10.toNat) ys
        let (r8, r3) := singleAddWord r8 r9 r3
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcAddLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) := by
  unfold mcAddLoop1
  rw [holShortTailrec_eq_elim]
  simp only [mcAddLoop1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add_loop1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddLoop1Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoop1Pre (l, r1, r3, r8, r9, r10, xs, ys, zs) ↔
      if r1 = (1 : BitVec width) then
        (let _r1 := (0 : BitVec width)
        True)
      else
        (let r1 := r1 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r8 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r10.toNat) < (ys.length))
        let r9 := holEl (r10.toNat) ys
        let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
        let (r8, r3) := singleAddWord r8 r9 r3
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcAddLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcAddLoop1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAddLoop1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_add_loop` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAddLoopStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, r8, r9, r10, xs, ys, zs) =>
    (let r1 := r1 + (1 : BitVec width)
    let r2 := r2 + (1 : BitVec width)
    let r3 := (0 : BitVec width)
    let cond := (mcAddLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) ∧ (l ≠ 0)
    let (l, _r1, r3, r8, _r9, r10, xs, ys, zs) := mcAddLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
    let r1 := r2
    let r9 := (0 : BitVec width)
    let cond := cond ∧ ((mcAddLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs)) ∧ (l ≠ 0))
    let (l, r1, r3, r8, r9, r10, xs, zs) := mcAddLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
    if r3 = (0 : BitVec width) then
      (.inr (l, r1, r2, r8, r9, r10, xs, ys, zs), cond)
    else
      (let r8 := (1 : BitVec width)
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inr (l, r1, r2, r8, r9, r10, xs, ys, zs), cond)))

/-- HOL `mc_add_loop`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAddLoop {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcAddLoopStep

/-- The precondition of `mc_add_loop`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop_pre"
  (words_as_type_indexed_bitvec)]
def mcAddLoopPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcAddLoopStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop_def" 365
  (words_as_type_indexed_bitvec)]
theorem mcAddLoop_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoop (l, r1, r2, r8, r9, r10, xs, ys, zs) =
      (let r1 := r1 + (1 : BitVec width)
      let r2 := r2 + (1 : BitVec width)
      let r3 := (0 : BitVec width)
      let (l, _r1, r3, r8, _r9, r10, xs, ys, zs) := mcAddLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
      let r1 := r2
      let r9 := (0 : BitVec width)
      let (l, r1, r3, r8, r9, r10, xs, zs) := mcAddLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
      if r3 = (0 : BitVec width) then
        (l, r1, r2, r8, r9, r10, xs, ys, zs)
      else
        (let r8 := (1 : BitVec width)
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        (l, r1, r2, r8, r9, r10, xs, ys, zs))) := by
  unfold mcAddLoop
  rw [holShortTailrec_eq_elim]
  simp only [mcAddLoopStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_loop_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddLoopPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs) ↔
      (let r1 := r1 + (1 : BitVec width)
      let r2 := r2 + (1 : BitVec width)
      let r3 := (0 : BitVec width)
      let cond := (mcAddLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) ∧ (l ≠ 0)
      let (l, _r1, r3, r8, _r9, r10, xs, _ys, zs) := mcAddLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
      let r1 := r2
      let r9 := (0 : BitVec width)
      let cond := cond ∧ ((mcAddLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs)) ∧ (l ≠ 0))
      let (_l, _r1, r3, _r8, _r9, r10, _xs, zs) := mcAddLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
      if r3 = (0 : BitVec width) then
        cond
      else
        (let r8 := (1 : BitVec width)
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let _zs := zs.set (r10.toNat) r8
        let _r10 := r10 + (1 : BitVec width)
        cond)) := by
  unfold mcAddLoopPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAddLoopStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_add` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcAddStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, r8, r9, r10, xs, ys, zs) =>
    (let r2 := r2 - r1
    let cond := mcAddLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
    let (l, r1, r2, r8, r9, r10, xs, ys, zs) := mcAddLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
    (.inr (l, r1, r2, r8, r9, r10, xs, ys, zs), cond))

/-- HOL `mc_add`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add"
  (words_as_type_indexed_bitvec)]
noncomputable def mcAdd {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcAddStep

/-- The precondition of `mc_add`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_pre"
  (words_as_type_indexed_bitvec)]
def mcAddPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcAddStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_add`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_def"
  (words_as_type_indexed_bitvec)]
theorem mcAdd_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAdd (l, r1, r2, r8, r9, r10, xs, ys, zs) =
      (let r2 := r2 - r1
      let (l, r1, r2, r8, r9, r10, xs, ys, zs) := mcAddLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
      (l, r1, r2, r8, r9, r10, xs, ys, zs)) := by
  unfold mcAdd
  rw [holShortTailrec_eq_elim]
  simp only [mcAddStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_add`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_add_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcAddPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcAddPre (l, r1, r2, r8, r9, r10, xs, ys, zs) ↔
      (let r2 := r2 - r1
      let cond := mcAddLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let (_l, _r1, _r2, _r8, _r9, _r10, _xs, _ys, _zs) := mcAddLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
      cond) := by
  unfold mcAddPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcAddStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_sub_loop2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSubLoop2Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r3, r8, r9, r10, xs, zs) =>
    if r1 = (1 : BitVec width) then
      (let r1 := (0 : BitVec width)
      (.inr (l, r1, r3, r8, r9, r10, xs, zs), True))
    else
      (let r1 := r1 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r8 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
      let (r8, r3) := singleSubWord r8 r9 r3
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r3, r8, r9, r10, xs, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_sub_loop2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSubLoop2 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcSubLoop2Step

/-- The precondition of `mc_sub_loop2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop2_pre"
  (words_as_type_indexed_bitvec)]
def mcSubLoop2Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcSubLoop2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_sub_loop2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop2_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubLoop2_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoop2 (l, r1, r3, r8, r9, r10, xs, zs) =
      if r1 = (1 : BitVec width) then
        (let r1 := (0 : BitVec width)
        (l, r1, r3, r8, r9, r10, xs, zs))
      else
        (let r1 := r1 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) xs
        let (r8, r3) := singleSubWord r8 r9 r3
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcSubLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)) := by
  unfold mcSubLoop2
  rw [holShortTailrec_eq_elim]
  simp only [mcSubLoop2Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_sub_loop2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubLoop2Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoop2Pre (l, r1, r3, r8, r9, r10, xs, zs) ↔
      if r1 = (1 : BitVec width) then
        (let _r1 := (0 : BitVec width)
        True)
      else
        (let r1 := r1 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r8 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
        let (r8, r3) := singleSubWord r8 r9 r3
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcSubLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcSubLoop2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSubLoop2Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_sub_loop1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSubLoop1Step {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r3, r8, r9, r10, xs, ys, zs) =>
    if r1 = (1 : BitVec width) then
      (let r1 := (0 : BitVec width)
      (.inr (l, r1, r3, r8, r9, r10, xs, ys, zs), True))
    else
      (let r1 := r1 - (1 : BitVec width)
      let cond := (r10.toNat) < (xs.length)
      let r8 := holEl (r10.toNat) xs
      let cond := cond ∧ ((r10.toNat) < (ys.length))
      let r9 := holEl (r10.toNat) ys
      let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
      let (r8, r3) := singleSubWord r8 r9 r3
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r8
      let r10 := r10 + (1 : BitVec width)
      (.inl (l - 1, r1, r3, r8, r9, r10, xs, ys, zs), cond ∧ (l ≠ 0)))

/-- HOL `mc_sub_loop1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSubLoop1 {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcSubLoop1Step

/-- The precondition of `mc_sub_loop1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop1_pre"
  (words_as_type_indexed_bitvec)]
def mcSubLoop1Pre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcSubLoop1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_sub_loop1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop1_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubLoop1_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoop1 (l, r1, r3, r8, r9, r10, xs, ys, zs) =
      if r1 = (1 : BitVec width) then
        (let r1 := (0 : BitVec width)
        (l, r1, r3, r8, r9, r10, xs, ys, zs))
      else
        (let r1 := r1 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) xs
        let r9 := holEl (r10.toNat) ys
        let (r8, r3) := singleSubWord r8 r9 r3
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcSubLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) := by
  unfold mcSubLoop1
  rw [holShortTailrec_eq_elim]
  simp only [mcSubLoop1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_sub_loop1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubLoop1Pre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r3 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoop1Pre (l, r1, r3, r8, r9, r10, xs, ys, zs) ↔
      if r1 = (1 : BitVec width) then
        (let _r1 := (0 : BitVec width)
        True)
      else
        (let r1 := r1 - (1 : BitVec width)
        let cond := (r10.toNat) < (xs.length)
        let r8 := holEl (r10.toNat) xs
        let cond := cond ∧ ((r10.toNat) < (ys.length))
        let r9 := holEl (r10.toNat) ys
        let cond := cond ∧ ((r3 ≠ (0 : BitVec width)) → (r3 = (1 : BitVec width)))
        let (r8, r3) := singleSubWord r8 r9 r3
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let zs := zs.set (r10.toNat) r8
        let r10 := r10 + (1 : BitVec width)
        mcSubLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs) ∧ (cond ∧ (l ≠ 0))) := by
  unfold mcSubLoop1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSubLoop1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_sub_loop` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSubLoopStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, r8, r9, r10, xs, ys, zs) =>
    (let r1 := r1 + (1 : BitVec width)
    let r2 := r2 + (1 : BitVec width)
    let r3 := (1 : BitVec width)
    let r8 := r8 - (0 : BitVec width)
    let cond := (mcSubLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) ∧ (l ≠ 0)
    let (l, _r1, r3, r8, _r9, r10, xs, ys, zs) := mcSubLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
    let r1 := r2
    let r9 := (0 : BitVec width)
    let cond := cond ∧ ((mcSubLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs)) ∧ (l ≠ 0))
    let (l, r1, _r3, r8, r9, r10, xs, zs) := mcSubLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
    (.inr (l, r1, r2, r8, r9, r10, xs, ys, zs), cond))

/-- HOL `mc_sub_loop`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSubLoop {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcSubLoopStep

/-- The precondition of `mc_sub_loop`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop_pre"
  (words_as_type_indexed_bitvec)]
def mcSubLoopPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcSubLoopStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_sub_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop_def" 657
  (words_as_type_indexed_bitvec)]
theorem mcSubLoop_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoop (l, r1, r2, r8, r9, r10, xs, ys, zs) =
      (let r1 := r1 + (1 : BitVec width)
      let r2 := r2 + (1 : BitVec width)
      let r3 := (1 : BitVec width)
      let r8 := r8 - (0 : BitVec width)
      let (l, _r1, r3, r8, _r9, r10, xs, ys, zs) := mcSubLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
      let r1 := r2
      let r9 := (0 : BitVec width)
      let (l, r1, _r3, r8, r9, r10, xs, zs) := mcSubLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
      (l, r1, r2, r8, r9, r10, xs, ys, zs)) := by
  unfold mcSubLoop
  rw [holShortTailrec_eq_elim]
  simp only [mcSubLoopStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_sub_loop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_loop_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubLoopPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs) ↔
      (let r1 := r1 + (1 : BitVec width)
      let r2 := r2 + (1 : BitVec width)
      let r3 := (1 : BitVec width)
      let r8 := r8 - (0 : BitVec width)
      let cond := (mcSubLoop1Pre (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)) ∧ (l ≠ 0)
      let (l, _r1, r3, r8, _r9, r10, xs, _ys, zs) := mcSubLoop1 (l - 1, r1, r3, r8, r9, r10, xs, ys, zs)
      let r1 := r2
      let r9 := (0 : BitVec width)
      let cond := cond ∧ ((mcSubLoop2Pre (l - 1, r1, r3, r8, r9, r10, xs, zs)) ∧ (l ≠ 0))
      let (_l, _r1, _r3, _r8, _r9, _r10, _xs, _zs) := mcSubLoop2 (l - 1, r1, r3, r8, r9, r10, xs, zs)
      cond) := by
  unfold mcSubLoopPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSubLoopStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_fix` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcFixStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × List (BitVec width)) × Prop
  | (l, r8, r10, zs) =>
    if r10 = (0 : BitVec width) then
      (.inr (l, r8, r10, zs), True)
    else
      (let r10 := r10 - (1 : BitVec width)
      let cond := (r10.toNat) < (zs.length)
      let r8 := holEl (r10.toNat) zs
      if r8 = (0 : BitVec width) then
        (.inl (l - 1, r8, r10, zs), cond ∧ (l ≠ 0))
      else
        (let r10 := r10 + (1 : BitVec width)
        (.inr (l, r8, r10, zs), cond)))

/-- HOL `mc_fix`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_fix"
  (words_as_type_indexed_bitvec)]
noncomputable def mcFix {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) → Nat × BitVec width × BitVec width × List (BitVec width) :=
  holShortTailrec mcFixStep

/-- The precondition of `mc_fix`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_fix_pre"
  (words_as_type_indexed_bitvec)]
def mcFixPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × List (BitVec width)) mcFixStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_fix`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_fix_def" 684
  (words_as_type_indexed_bitvec)]
theorem mcFix_def {width : Nat} [NeZero width] {l : Nat} {r8 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcFix (l, r8, r10, zs) =
      if r10 = (0 : BitVec width) then
        (l, r8, r10, zs)
      else
        (let r10 := r10 - (1 : BitVec width)
        let r8 := holEl (r10.toNat) zs
        if r8 = (0 : BitVec width) then
          mcFix (l - 1, r8, r10, zs)
        else
          (let r10 := r10 + (1 : BitVec width)
          (l, r8, r10, zs))) := by
  unfold mcFix
  rw [holShortTailrec_eq_elim]
  simp only [mcFixStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_fix`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_fix_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcFixPre_def {width : Nat} [NeZero width] {l : Nat} {r8 : BitVec width} {r10 : BitVec width} {zs : List (BitVec width)} :
    mcFixPre (l, r8, r10, zs) ↔
      if r10 = (0 : BitVec width) then
        True
      else
        (let r10 := r10 - (1 : BitVec width)
        let cond := (r10.toNat) < (zs.length)
        let r8 := holEl (r10.toNat) zs
        if r8 = (0 : BitVec width) then
          mcFixPre (l - 1, r8, r10, zs) ∧ (cond ∧ (l ≠ 0))
        else
          (let _r10 := r10 + (1 : BitVec width)
          cond)) := by
  unfold mcFixPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcFixStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> first | exact Iff.of_eq (and_true _) | exact and_comm

/-- The step function that HOL's `tailrec_define` turns into `mc_sub` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcSubStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, r8, r9, r10, xs, ys, zs) =>
    (let r2 := r2 - r1
    let cond := mcSubLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
    let (l, r1, r2, r8, r9, r10, xs, ys, zs) := mcSubLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
    let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
    let (l, r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
    (.inr (l, r1, r2, r8, r9, r10, xs, ys, zs), cond))

/-- HOL `mc_sub`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub"
  (words_as_type_indexed_bitvec)]
noncomputable def mcSub {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcSubStep

/-- The precondition of `mc_sub`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_pre"
  (words_as_type_indexed_bitvec)]
def mcSubPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcSubStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_sub`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_def" 700
  (words_as_type_indexed_bitvec)]
theorem mcSub_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSub (l, r1, r2, r8, r9, r10, xs, ys, zs) =
      (let r2 := r2 - r1
      let (l, r1, r2, r8, r9, r10, xs, ys, zs) := mcSubLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let (l, r8, r10, zs) := mcFix (l - 1, r8, r10, zs)
      (l, r1, r2, r8, r9, r10, xs, ys, zs)) := by
  unfold mcSub
  rw [holShortTailrec_eq_elim]
  simp only [mcSubStep, Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_sub`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_sub_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcSubPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {r8 : BitVec width} {r9 : BitVec width} {r10 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcSubPre (l, r1, r2, r8, r9, r10, xs, ys, zs) ↔
      (let r2 := r2 - r1
      let cond := mcSubLoopPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let (l, _r1, _r2, r8, _r9, r10, _xs, _ys, zs) := mcSubLoop (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let cond := cond ∧ ((mcFixPre (l - 1, r8, r10, zs)) ∧ (l ≠ 0))
      let (_l, _r8, _r10, _zs) := mcFix (l - 1, r8, r10, zs)
      cond) := by
  unfold mcSubPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcSubStep, Sum.elim_inr]
  exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_iadd1` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIadd1Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (r1, r2, xs, ys) =>
    (let r0 := (0 : BitVec width)
    if r1 < r2 then
      (let (xs, ys) := (ys, xs)
      let r0 := (1 : BitVec width)
      (.inr (r1, r2, r0, xs, ys), True))
    else
      (let r8 := r1
      let r1 := r2
      let r2 := r8
      (.inr (r1, r2, r0, xs, ys), True)))

/-- HOL `mc_iadd1`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd1"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIadd1 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIadd1Step

/-- The precondition of `mc_iadd1`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd1_pre"
  (words_as_type_indexed_bitvec)]
def mcIadd1Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcIadd1Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_iadd1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd1_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd1_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd1 (r1, r2, xs, ys) =
      (let r0 := (0 : BitVec width)
      if r1 < r2 then
        (let (xs, ys) := (ys, xs)
        let r0 := (1 : BitVec width)
        (r1, r2, r0, xs, ys))
      else
        (let r8 := r1
        let r1 := r2
        let r2 := r8
        (r1, r2, r0, xs, ys))) := by
  unfold mcIadd1
  rw [holShortTailrec_eq_elim]
  simp only [mcIadd1Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_iadd1`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd1_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd1Pre_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd1Pre (r1, r2, xs, ys) ↔
      (let _r0 := (0 : BitVec width)
      if r1 < r2 then
        (let (_xs, _ys) := (ys, xs)
        let _r0 := (1 : BitVec width)
        True)
      else
        (let r8 := r1
        let _r1 := r2
        let _r2 := r8
        True)) := by
  unfold mcIadd1Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIadd1Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_iadd2` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIadd2Step {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → (BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) ⊕ BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) × Prop
  | (r1, r2, r10, r12, xs, ys) =>
    (let r0 := (0 : BitVec width)
    if r10 = (1 : BitVec width) then
      (let (xs, ys) := (ys, xs)
      let r12 := r12 ^^^ (1 : BitVec width)
      let r0 := (1 : BitVec width)
      (.inr (r1, r2, r0, r12, xs, ys), True))
    else
      (let r8 := r1
      let r1 := r2
      let r2 := r8
      (.inr (r1, r2, r0, r12, xs, ys), True)))

/-- HOL `mc_iadd2`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd2"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIadd2 {width : Nat} [NeZero width] :
    BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIadd2Step

/-- The precondition of `mc_iadd2`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd2_pre"
  (words_as_type_indexed_bitvec)]
def mcIadd2Pre {width : Nat} [NeZero width] : BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width)) mcIadd2Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_iadd2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd2_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd2_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {r10 : BitVec width} {r12 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd2 (r1, r2, r10, r12, xs, ys) =
      (let r0 := (0 : BitVec width)
      if r10 = (1 : BitVec width) then
        (let (xs, ys) := (ys, xs)
        let r12 := r12 ^^^ (1 : BitVec width)
        let r0 := (1 : BitVec width)
        (r1, r2, r0, r12, xs, ys))
      else
        (let r8 := r1
        let r1 := r2
        let r2 := r8
        (r1, r2, r0, r12, xs, ys))) := by
  unfold mcIadd2
  rw [holShortTailrec_eq_elim]
  simp only [mcIadd2Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_iadd2`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd2_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd2Pre_def {width : Nat} [NeZero width] {r1 : BitVec width} {r2 : BitVec width} {r10 : BitVec width} {r12 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd2Pre (r1, r2, r10, r12, xs, ys) ↔
      (let _r0 := (0 : BitVec width)
      if r10 = (1 : BitVec width) then
        (let (_xs, _ys) := (ys, xs)
        let _r12 := r12 ^^^ (1 : BitVec width)
        let _r0 := (1 : BitVec width)
        True)
      else
        (let r8 := r1
        let _r1 := r2
        let _r2 := r8
        True)) := by
  unfold mcIadd2Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIadd2Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_iadd3` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIadd3Step {width : Nat} [NeZero width] :
    BitVec width × List (BitVec width) × List (BitVec width) → (BitVec width × List (BitVec width) × List (BitVec width) ⊕ List (BitVec width) × List (BitVec width)) × Prop
  | (r0, xs, ys) =>
    if r0 = (0 : BitVec width) then
      (.inr (xs, ys), True)
    else
      (let (xs, ys) := (ys, xs)
      (.inr (xs, ys), True))

/-- HOL `mc_iadd3`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd3"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIadd3 {width : Nat} [NeZero width] :
    BitVec width × List (BitVec width) × List (BitVec width) → List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIadd3Step

/-- The precondition of `mc_iadd3`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd3_pre"
  (words_as_type_indexed_bitvec)]
def mcIadd3Pre {width : Nat} [NeZero width] : BitVec width × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := List (BitVec width) × List (BitVec width)) mcIadd3Step

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_iadd3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd3_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd3_def {width : Nat} [NeZero width] {r0 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd3 (r0, xs, ys) =
      if r0 = (0 : BitVec width) then
        (xs, ys)
      else
        (let (xs, ys) := (ys, xs)
        (xs, ys)) := by
  unfold mcIadd3
  rw [holShortTailrec_eq_elim]
  simp only [mcIadd3Step, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_iadd3`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd3_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd3Pre_def {width : Nat} [NeZero width] {r0 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} :
    mcIadd3Pre (r0, xs, ys) ↔
      if r0 = (0 : BitVec width) then
        True
      else
        (let (_xs, _ys) := (ys, xs)
        True) := by
  unfold mcIadd3Pre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIadd3Step, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_iadd` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIaddStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r1, r2, xs, ys, zs) =>
    (let r10 := r1
    let r10 := r10 &&& (1 : BitVec width)
    let r11 := r2
    let r11 := r11 &&& (1 : BitVec width)
    if r10 = r11 then
      (let r1 := r1 >>> 1
      let r2 := r2 >>> 1
      let (r1, r2, r0, xs, ys) := mcIadd1 (r1, r2, xs, ys)
      let r8 := (0 : BitVec width)
      let r9 := r8
      let r10 := r8
      let cond := mcAddPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let (l, _r1, _r2, _r8, _r9, r10, xs, ys, zs) := mcAdd (l, r1, r2, r8, r9, r10, xs, ys, zs)
      let (xs, ys) := mcIadd3 (r0, xs, ys)
      let r10 := r10 <<< 1
      let r10 := r10 + r11
      (.inr (l, r10, xs, ys, zs), cond))
    else
      (let r12 := r10
      let r10 := r1
      let r10 := r10 >>> 1
      let r11 := r2
      let r11 := r11 >>> 1
      let cond := mcComparePre (l, r10, r11, xs, ys)
      let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
      if r10 = (0 : BitVec width) then
        (.inr (l, r10, xs, ys, zs), cond)
      else
        (let (r1, r2, r0, r12, xs, ys) := mcIadd2 (r1, r2, r10, r12, xs, ys)
        let r8 := (0 : BitVec width)
        let r9 := r8
        let r10 := r8
        let r1 := r1 >>> 1
        let r2 := r2 >>> 1
        let cond := cond ∧ (mcSubPre (l, r1, r2, r8, r9, r10, xs, ys, zs))
        let (l, _r1, _r2, _r8, _r9, r10, xs, ys, zs) := mcSub (l, r1, r2, r8, r9, r10, xs, ys, zs)
        let (xs, ys) := mcIadd3 (r0, xs, ys)
        let r10 := r10 <<< 1
        let r10 := r10 + r12
        (.inr (l, r10, xs, ys, zs), cond))))

/-- HOL `mc_iadd`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIadd {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIaddStep

/-- The precondition of `mc_iadd`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd_pre"
  (words_as_type_indexed_bitvec)]
def mcIaddPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcIaddStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_iadd`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd_def"
  (words_as_type_indexed_bitvec)]
theorem mcIadd_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIadd (l, r1, r2, xs, ys, zs) =
      (let r10 := r1
      let r10 := r10 &&& (1 : BitVec width)
      let r11 := r2
      let r11 := r11 &&& (1 : BitVec width)
      if r10 = r11 then
        (let r1 := r1 >>> 1
        let r2 := r2 >>> 1
        let (r1, r2, r0, xs, ys) := mcIadd1 (r1, r2, xs, ys)
        let r8 := (0 : BitVec width)
        let r9 := r8
        let r10 := r8
        let (l, _r1, _r2, _r8, _r9, r10, xs, ys, zs) := mcAdd (l, r1, r2, r8, r9, r10, xs, ys, zs)
        let (xs, ys) := mcIadd3 (r0, xs, ys)
        let r10 := r10 <<< 1
        let r10 := r10 + r11
        (l, r10, xs, ys, zs))
      else
        (let r12 := r10
        let r10 := r1
        let r10 := r10 >>> 1
        let r11 := r2
        let r11 := r11 >>> 1
        let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
        if r10 = (0 : BitVec width) then
          (l, r10, xs, ys, zs)
        else
          (let (r1, r2, r0, r12, xs, ys) := mcIadd2 (r1, r2, r10, r12, xs, ys)
          let r8 := (0 : BitVec width)
          let r9 := r8
          let r10 := r8
          let r1 := r1 >>> 1
          let r2 := r2 >>> 1
          let (l, _r1, _r2, _r8, _r9, r10, xs, ys, zs) := mcSub (l, r1, r2, r8, r9, r10, xs, ys, zs)
          let (xs, ys) := mcIadd3 (r0, xs, ys)
          let r10 := r10 <<< 1
          let r10 := r10 + r12
          (l, r10, xs, ys, zs)))) := by
  unfold mcIadd
  rw [holShortTailrec_eq_elim]
  simp only [mcIaddStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_iadd`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iadd_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIaddPre_def {width : Nat} [NeZero width] {l : Nat} {r1 : BitVec width} {r2 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIaddPre (l, r1, r2, xs, ys, zs) ↔
      (let r10 := r1
      let r10 := r10 &&& (1 : BitVec width)
      let r11 := r2
      let r11 := r11 &&& (1 : BitVec width)
      if r10 = r11 then
        (let r1 := r1 >>> 1
        let r2 := r2 >>> 1
        let (r1, r2, r0, xs, ys) := mcIadd1 (r1, r2, xs, ys)
        let r8 := (0 : BitVec width)
        let r9 := r8
        let r10 := r8
        let cond := mcAddPre (l, r1, r2, r8, r9, r10, xs, ys, zs)
        let (_l, _r1, _r2, _r8, _r9, r10, xs, ys, _zs) := mcAdd (l, r1, r2, r8, r9, r10, xs, ys, zs)
        let (_xs, _ys) := mcIadd3 (r0, xs, ys)
        let r10 := r10 <<< 1
        let _r10 := r10 + r11
        cond)
      else
        (let r12 := r10
        let r10 := r1
        let r10 := r10 >>> 1
        let r11 := r2
        let r11 := r11 >>> 1
        let cond := mcComparePre (l, r10, r11, xs, ys)
        let (l, r10, xs, ys) := mcCompare (l, r10, r11, xs, ys)
        if r10 = (0 : BitVec width) then
          cond
        else
          (let (r1, r2, r0, r12, xs, ys) := mcIadd2 (r1, r2, r10, r12, xs, ys)
          let r8 := (0 : BitVec width)
          let r9 := r8
          let r10 := r8
          let r1 := r1 >>> 1
          let r2 := r2 >>> 1
          let cond := cond ∧ (mcSubPre (l, r1, r2, r8, r9, r10, xs, ys, zs))
          let (_l, _r1, _r2, _r8, _r9, r10, xs, ys, _zs) := mcSub (l, r1, r2, r8, r9, r10, xs, ys, zs)
          let (_xs, _ys) := mcIadd3 (r0, xs, ys)
          let r10 := r10 <<< 1
          let _r10 := r10 + r12
          cond))) := by
  unfold mcIaddPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIaddStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
