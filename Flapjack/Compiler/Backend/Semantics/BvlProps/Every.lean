module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Measure
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Recursive predicates over every BVL expression and subexpression. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem (expsWeight expWeight)

/-- The predicate holds at each expression in a list and all its descendants. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "bEvery_def"]
def bEvery (p : Bvl.Exp → Prop) : List Bvl.Exp → Prop
  | [] => True
  | x :: y :: xs => bEvery p [x] ∧ bEvery p (y :: xs)
  | [.var v] => p (.var v)
  | [.ifThenElse x y z] => p (.ifThenElse x y z) ∧ bEvery p [x] ∧ bEvery p [y] ∧ bEvery p [z]
  | [.let xs body] => p (.let xs body) ∧ bEvery p xs ∧ bEvery p [body]
  | [.raise x] => p (.raise x) ∧ bEvery p [x]
  | [.tick x] => p (.tick x) ∧ bEvery p [x]
  | [.op op xs] => p (.op op xs) ∧ bEvery p xs
  | [.force loc v] => p (.force loc v)
  | [.handle x y] => p (.handle x y) ∧ bEvery p [x] ∧ bEvery p [y]
  | [.call ticks dest xs] => p (.call ticks dest xs) ∧ bEvery p xs
termination_by xs => expsWeight xs
decreasing_by
  all_goals simp only [expsWeight, expWeight]
  all_goals try (have := BvlSem.expWeight_pos y)
  all_goals omega

private theorem bEvery_cons_iff (p : Bvl.Exp → Prop) (x : Bvl.Exp) (xs : List Bvl.Exp) :
    bEvery p (x :: xs) ↔ bEvery p [x] ∧ bEvery p xs := by
  cases xs with
  | nil => simp [bEvery]
  | cons y ys => rw [bEvery]

/-- The recursive property on a list is the list-wide singleton property. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "bEvery_EVERY"]
theorem bEvery_every (p : Bvl.Exp → Prop) (xs : List Bvl.Exp) :
    bEvery p xs ↔ xs.Forall (fun x => bEvery p [x]) := by
  induction xs with
  | nil => simp [bEvery]
  | cons x xs ih => rw [bEvery_cons_iff, List.forall_cons, ih]

end Flapjack.Compiler.Backend.BvlProps
