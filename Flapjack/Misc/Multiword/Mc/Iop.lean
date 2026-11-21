module

public import Flapjack.Misc.Multiword.Mc.IDiv

@[expose] public section

/-! Machine-code-style operation dispatch functions of HOL's `mc_multiword`, defined by
`tailrec_define`: each has a step function, the function and its
precondition, and their unfolding theorems. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The step function that HOL's `tailrec_define` turns into `mc_isub_flip` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIsubFlipStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width → (BitVec width × BitVec width ⊕ BitVec width × BitVec width) × Prop
  | (r1, r3) =>
    if r3 = (0 : BitVec width) then
      (.inr (r1, r3), True)
    else
      (let r1 := r1 ^^^ (1 : BitVec width)
      (.inr (r1, r3), True))

/-- HOL `mc_isub_flip`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_isub_flip"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIsubFlip {width : Nat} [NeZero width] :
    BitVec width × BitVec width → BitVec width × BitVec width :=
  holShortTailrec mcIsubFlipStep

/-- The precondition of `mc_isub_flip`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_isub_flip_pre"
  (words_as_type_indexed_bitvec)]
def mcIsubFlipPre {width : Nat} [NeZero width] : BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width × BitVec width) mcIsubFlipStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_isub_flip`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_isub_flip_def"
  (words_as_type_indexed_bitvec)]
theorem mcIsubFlip_def {width : Nat} [NeZero width] {r1 : BitVec width} {r3 : BitVec width} :
    mcIsubFlip (r1, r3) =
      if r3 = (0 : BitVec width) then
        (r1, r3)
      else
        (let r1 := r1 ^^^ (1 : BitVec width)
        (r1, r3)) := by
  unfold mcIsubFlip
  rw [holShortTailrec_eq_elim]
  simp only [mcIsubFlipStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_isub_flip`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_isub_flip_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIsubFlipPre_def {width : Nat} [NeZero width] {r1 : BitVec width} {r3 : BitVec width} :
    mcIsubFlipPre (r1, r3) ↔
      if r3 = (0 : BitVec width) then
        True
      else
        (let _r1 := r1 ^^^ (1 : BitVec width)
        True) := by
  unfold mcIsubFlipPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIsubFlipStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_icmp_res` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIcmpResStep {width : Nat} [NeZero width] :
    BitVec width × BitVec width → (BitVec width × BitVec width ⊕ BitVec width) × Prop
  | (r10, r3) =>
    if r3 = (2 : BitVec width) then
      if r10 = (1 : BitVec width) then
        (let r10 := (1 : BitVec width)
        (.inr r10, True))
      else
        (let r10 := (0 : BitVec width)
        (.inr r10, True))
    else
      if r10 = (0 : BitVec width) then
        (let r10 := (1 : BitVec width)
        (.inr r10, True))
      else
        (let r10 := (0 : BitVec width)
        (.inr r10, True))

/-- HOL `mc_icmp_res`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icmp_res"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIcmpRes {width : Nat} [NeZero width] :
    BitVec width × BitVec width → BitVec width :=
  holShortTailrec mcIcmpResStep

/-- The precondition of `mc_icmp_res`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icmp_res_pre"
  (words_as_type_indexed_bitvec)]
def mcIcmpResPre {width : Nat} [NeZero width] : BitVec width × BitVec width → Prop :=
  holShortTailrecPre (β := BitVec width) mcIcmpResStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_icmp_res`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icmp_res_def"
  (words_as_type_indexed_bitvec)]
theorem mcIcmpRes_def {width : Nat} [NeZero width] {r10 : BitVec width} {r3 : BitVec width} :
    mcIcmpRes (r10, r3) =
      if r3 = (2 : BitVec width) then
        if r10 = (1 : BitVec width) then
          (let r10 := (1 : BitVec width)
          r10)
        else
          (let r10 := (0 : BitVec width)
          r10)
      else
        if r10 = (0 : BitVec width) then
          (let r10 := (1 : BitVec width)
          r10)
        else
          (let r10 := (0 : BitVec width)
          r10) := by
  unfold mcIcmpRes
  rw [holShortTailrec_eq_elim]
  simp only [mcIcmpResStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_icmp_res`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_icmp_res_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIcmpResPre_def {width : Nat} [NeZero width] {r10 : BitVec width} {r3 : BitVec width} :
    mcIcmpResPre (r10, r3) ↔
      if r3 = (2 : BitVec width) then
        if r10 = (1 : BitVec width) then
          (let _r10 := (1 : BitVec width)
          True)
        else
          (let _r10 := (0 : BitVec width)
          True)
      else
        if r10 = (0 : BitVec width) then
          (let _r10 := (1 : BitVec width)
          True)
        else
          (let _r10 := (0 : BitVec width)
          True) := by
  unfold mcIcmpResPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIcmpResStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_full_cmp` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcFullCmpStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r3, r10, r11, xs, ys, zs) =>
    (let cond := mcIcomparePre (l, r10, r11, xs, ys)
    let (l, r10, xs, ys) := mcIcompare (l, r10, r11, xs, ys)
    let r10 := mcIcmpRes (r10, r3)
    if r10 = (0 : BitVec width) then
      (.inr (l, r10, xs, ys, zs), cond)
    else
      (let r0 := (1 : BitVec width)
      let r10 := ((0 : BitVec width))
      let cond := cond ∧ ((r10.toNat) < (zs.length))
      let zs := zs.set (r10.toNat) r0
      let r10 := (2 : BitVec width)
      (.inr (l, r10, xs, ys, zs), cond)))

/-- HOL `mc_full_cmp`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_full_cmp"
  (words_as_type_indexed_bitvec)]
noncomputable def mcFullCmp {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcFullCmpStep

/-- The precondition of `mc_full_cmp`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_full_cmp_pre"
  (words_as_type_indexed_bitvec)]
def mcFullCmpPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcFullCmpStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_full_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_full_cmp_def"
  (words_as_type_indexed_bitvec)]
theorem mcFullCmp_def {width : Nat} [NeZero width] {l : Nat} {r3 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcFullCmp (l, r3, r10, r11, xs, ys, zs) =
      (let (l, r10, xs, ys) := mcIcompare (l, r10, r11, xs, ys)
      let r10 := mcIcmpRes (r10, r3)
      if r10 = (0 : BitVec width) then
        (l, r10, xs, ys, zs)
      else
        (let r0 := (1 : BitVec width)
        let r10 := ((0 : BitVec width))
        let zs := zs.set (r10.toNat) r0
        let r10 := (2 : BitVec width)
        (l, r10, xs, ys, zs))) := by
  unfold mcFullCmp
  rw [holShortTailrec_eq_elim]
  simp only [mcFullCmpStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_full_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_full_cmp_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcFullCmpPre_def {width : Nat} [NeZero width] {l : Nat} {r3 : BitVec width} {r10 : BitVec width} {r11 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcFullCmpPre (l, r3, r10, r11, xs, ys, zs) ↔
      (let cond := mcIcomparePre (l, r10, r11, xs, ys)
      let (_l, r10, _xs, _ys) := mcIcompare (l, r10, r11, xs, ys)
      let r10 := mcIcmpRes (r10, r3)
      if r10 = (0 : BitVec width) then
        cond
      else
        (let r0 := (1 : BitVec width)
        let r10 := ((0 : BitVec width))
        let cond := cond ∧ ((r10.toNat) < (zs.length))
        let _zs := zs.set (r10.toNat) r0
        let _r10 := (2 : BitVec width)
        cond)) := by
  unfold mcFullCmpPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcFullCmpStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

/-- The step function that HOL's `tailrec_define` turns into `mc_iop` (the
lambda term of the definition; Flapjack names it for readability). -/
noncomputable def mcIopStep {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → (Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) ⊕ Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) × Prop
  | (l, r0, r1, r3, xs, ys, zs) =>
    if r3 < (2 : BitVec width) then
      (let (r1, _r3) := mcIsubFlip (r1, r3)
      let r2 := r1
      let r1 := r0
      let cond := mcIaddPre (l, r1, r2, xs, ys, zs)
      let (l, r10, xs, ys, zs) := mcIadd (l, r1, r2, xs, ys, zs)
      (.inr (l, r10, xs, ys, zs), cond))
    else
      if r3 = (4 : BitVec width) then
        (let r2 := r1
        let r1 := r0
        let cond := mcImulPre (l, r1, r2, xs, ys, zs)
        let (l, r10, xs, ys, zs) := mcImul (l, r1, r2, xs, ys, zs)
        (.inr (l, r10, xs, ys, zs), cond))
      else
        (let r3 := r3 - (5 : BitVec width)
        let r10 := r0
        let r11 := r1
        let cond := mcIdivPre (l, r3, r10, r11, xs, ys, zs)
        let (l, r11, xs, ys, zs) := mcIdiv (l, r3, r10, r11, xs, ys, zs)
        let r10 := r11
        (.inr (l, r10, xs, ys, zs), cond))

/-- HOL `mc_iop`, defined by `tailrec_define` as `SHORT_TAILREC` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iop"
  (words_as_type_indexed_bitvec)]
noncomputable def mcIop {width : Nat} [NeZero width] :
    Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) :=
  holShortTailrec mcIopStep

/-- The precondition of `mc_iop`, `SHORT_TAILREC_PRE` of its step. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iop_pre"
  (words_as_type_indexed_bitvec)]
def mcIopPre {width : Nat} [NeZero width] : Nat × BitVec width × BitVec width × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width) → Prop :=
  holShortTailrecPre (β := Nat × BitVec width × List (BitVec width) × List (BitVec width) × List (BitVec width)) mcIopStep

set_option maxHeartbeats 1000000 in
/-- The unfolding equation of `mc_iop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iop_def"
  (words_as_type_indexed_bitvec)]
theorem mcIop_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIop (l, r0, r1, r3, xs, ys, zs) =
      if r3 < (2 : BitVec width) then
        (let (r1, _r3) := mcIsubFlip (r1, r3)
        let r2 := r1
        let r1 := r0
        let (l, r10, xs, ys, zs) := mcIadd (l, r1, r2, xs, ys, zs)
        (l, r10, xs, ys, zs))
      else
        if r3 = (4 : BitVec width) then
          (let r2 := r1
          let r1 := r0
          let (l, r10, xs, ys, zs) := mcImul (l, r1, r2, xs, ys, zs)
          (l, r10, xs, ys, zs))
        else
          (let r3 := r3 - (5 : BitVec width)
          let r10 := r0
          let r11 := r1
          let (l, r11, xs, ys, zs) := mcIdiv (l, r3, r10, r11, xs, ys, zs)
          let r10 := r11
          (l, r10, xs, ys, zs)) := by
  unfold mcIop
  rw [holShortTailrec_eq_elim]
  simp only [mcIopStep, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr, id]

set_option maxHeartbeats 1000000 in
/-- The unfolding equivalence of the precondition of `mc_iop`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iop_pre_def"
  (words_as_type_indexed_bitvec)]
theorem mcIopPre_def {width : Nat} [NeZero width] {l : Nat} {r0 : BitVec width} {r1 : BitVec width} {r3 : BitVec width} {xs : List (BitVec width)} {ys : List (BitVec width)} {zs : List (BitVec width)} :
    mcIopPre (l, r0, r1, r3, xs, ys, zs) ↔
      if r3 < (2 : BitVec width) then
        (let (r1, _r3) := mcIsubFlip (r1, r3)
        let r2 := r1
        let r1 := r0
        let cond := mcIaddPre (l, r1, r2, xs, ys, zs)
        let (_l, _r10, _xs, _ys, _zs) := mcIadd (l, r1, r2, xs, ys, zs)
        cond)
      else
        if r3 = (4 : BitVec width) then
          (let r2 := r1
          let r1 := r0
          let cond := mcImulPre (l, r1, r2, xs, ys, zs)
          let (_l, _r10, _xs, _ys, _zs) := mcImul (l, r1, r2, xs, ys, zs)
          cond)
        else
          (let r3 := r3 - (5 : BitVec width)
          let r10 := r0
          let r11 := r1
          let cond := mcIdivPre (l, r3, r10, r11, xs, ys, zs)
          let (_l, r11, _xs, _ys, _zs) := mcIdiv (l, r3, r10, r11, xs, ys, zs)
          let _r10 := r11
          cond) := by
  unfold mcIopPre
  rw [holShortTailrecPre_eq_elim]
  simp only [mcIopStep, apply_ite Prod.snd, apply_ite Prod.fst, apply_ite (Sum.elim _ _), Sum.elim_inr]
  split_ifs <;> exact Iff.of_eq (and_true _)

end Flapjack.Misc.Multiword
