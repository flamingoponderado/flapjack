import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Misc.Sptree

/-! Expression relation used by CakeML's BVL tick inlining proof. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl

/-- Relate BVL expressions before and after inlining calls from a code tree. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "exp_rel"]
inductive ExpRel (code : Spt (Nat × Exp)) : List Exp → List Exp → Prop where
  | var (v : Nat) : ExpRel code [.var v] [.var v]
  | nil : ExpRel code [] []
  | cons {x x1 y y1 : Exp} {xs ys : List Exp} :
      ExpRel code [x] [y] → ExpRel code (x1 :: xs) (y1 :: ys) →
      ExpRel code (x :: x1 :: xs) (y :: y1 :: ys)
  | ifThenElse {x1 x2 x3 y1 y2 y3 : Exp} :
      ExpRel code [x1] [y1] → ExpRel code [x2] [y2] → ExpRel code [x3] [y3] →
      ExpRel code [.ifThenElse x1 x2 x3] [.ifThenElse y1 y2 y3]
  | letExp {xs ys : List Exp} {x y : Exp} :
      ExpRel code xs ys → ExpRel code [x] [y] → ExpRel code [.let xs x] [.let ys y]
  | handle {x1 x2 y1 y2 : Exp} :
      ExpRel code [x1] [y1] → ExpRel code [x2] [y2] →
      ExpRel code [.handle x1 x2] [.handle y1 y2]
  | raise {x y : Exp} : ExpRel code [x] [y] → ExpRel code [.raise x] [.raise y]
  | tick {x y : Exp} : ExpRel code [x] [y] → ExpRel code [.tick x] [.tick y]
  | op {op : ClosLang.Op} {xs ys : List Exp} :
      ExpRel code xs ys → ExpRel code [.op op xs] [.op op ys]
  | force (loc n : Nat) : ExpRel code [.force loc n] [.force loc n]
  | call {ticks : Nat} {dest : Option Nat} {xs ys : List Exp} :
      ExpRel code xs ys → ExpRel code [.call ticks dest xs] [.call ticks dest ys]
  | inlineCall {ticks n arity : Nat} {xs ys : List Exp} {x y : Exp} :
      ExpRel code xs ys → sptLookup n code = some (arity, x) → ExpRel code [x] [y] →
      ExpRel code [.call ticks (some n) xs] [.let ys (mkTick (ticks + 1) y)]

/-- Extending a code tree preserves the inlining relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "subspt_exp_rel"]
theorem subsptExpRel (source target : Spt (Nat × Exp)) (xs ys : List Exp)
    (subset : sptSubspt source target) (related : ExpRel source xs ys) : ExpRel target xs ys := by
  induction related with
  | var v => exact .var v
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | letExp _ _ ih1 ih2 => exact .letExp ih1 ih2
  | handle _ _ ih1 ih2 => exact .handle ih1 ih2
  | raise _ ih => exact .raise ih
  | tick _ ih => exact .tick ih
  | op _ ih => exact .op ih
  | force loc n => exact .force loc n
  | call _ ih => exact .call ih
  | @inlineCall ticks n arity xs ys x y _ lookup _ ih1 ih2 =>
    have inDomain : sptMem n source := (sptMem_iff_lookup n source).2 ⟨_, lookup⟩
    exact .inlineCall ih1 ((subset n inDomain).2.trans lookup) ih2

/-- Extensionally equal code trees induce the same expression relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "exp_rel_swap"]
theorem expRelSwap (source : Spt (Nat × Exp)) (xs ys : List Exp) (target : Spt (Nat × Exp))
    (same : ∀ key, sptLookup key source = sptLookup key target) :
    ExpRel source xs ys = ExpRel target xs ys := by
  have subset : sptSubspt source target := by
    intro key member
    obtain ⟨value, found⟩ := (sptMem_iff_lookup key source).1 member
    exact ⟨(sptMem_iff_lookup key target).2 ⟨value, (same key).symm.trans found⟩, (same key).symm⟩
  have reverse : sptSubspt target source := by
    intro key member
    obtain ⟨value, found⟩ := (sptMem_iff_lookup key target).1 member
    exact ⟨(sptMem_iff_lookup key source).2 ⟨value, (same key).trans found⟩, same key⟩
  exact propext ⟨subsptExpRel source target xs ys subset,
    subsptExpRel target source xs ys reverse⟩

mutual
private theorem expRelSelf (code : Spt (Nat × Exp)) (e : Exp) : ExpRel code [e] [e] := by
  cases e with
  | var v => exact .var v
  | force loc n => exact .force loc n
  | ifThenElse x y z => exact .ifThenElse (expRelSelf code x) (expRelSelf code y) (expRelSelf code z)
  | «let» xs body => exact .letExp (listRelSelf code xs) (expRelSelf code body)
  | raise x => exact .raise (expRelSelf code x)
  | handle x y => exact .handle (expRelSelf code x) (expRelSelf code y)
  | tick x => exact .tick (expRelSelf code x)
  | op op xs => exact .op (listRelSelf code xs)
  | call ticks dest xs => exact .call (listRelSelf code xs)
termination_by sizeOf e
decreasing_by all_goals simp_wf <;> omega

private theorem listRelSelf (code : Spt (Nat × Exp)) (xs : List Exp) : ExpRel code xs xs := by
  cases xs with
  | nil => exact .nil
  | cons x xs =>
    cases xs with
    | nil => exact expRelSelf code x
    | cons y ys => exact .cons (expRelSelf code x) (listRelSelf code (y :: ys))
termination_by sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- Every expression list is related to itself. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "exp_rel_refl"]
theorem expRelRefl (code : Spt (Nat × Exp)) (xs : List Exp) : ExpRel code xs xs :=
  listRelSelf code xs

end Flapjack.Compiler.Backend.BvlInline.Proofs
