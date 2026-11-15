module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Measure

@[expose] public section

/-! Variable-bound predicates used by the BVL lowering proofs. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem (expsWeight expWeight)

/-- Recognize a variable expression. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "isVar_def"]
def isVar : Bvl.Exp → Bool
  | .var _ => true
  | _ => false

/-- A totalization of the variable projection for Flapjack proofs. HOL
specifies only the variable case; the fallback is a Flapjack choice and must
not be used to infer HOL behavior on other expressions. -/
def destVar : Bvl.Exp → Nat
  | .var n => n
  | _ => 0

/-- Projecting a variable yields its index. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "destVar_def"]
theorem destVar_var (n : Nat) : destVar (.var n) = n := rfl

/-- All variables in the expressions are in scope at the given depth. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "bVarBound_def"]
def bVarBound (n : Nat) : List Bvl.Exp → Prop
  | [] => True
  | x :: y :: xs => bVarBound n [x] ∧ bVarBound n (y :: xs)
  | [.var v] => v < n
  | [.ifThenElse x y z] => bVarBound n [x] ∧ bVarBound n [y] ∧ bVarBound n [z]
  | [.let xs body] => bVarBound n xs ∧ bVarBound (n + xs.length) [body]
  | [.raise x] | [.tick x] => bVarBound n [x]
  | [.op _ xs] | [.call _ _ xs] => bVarBound n xs
  | [.force _ v] => v < n
  | [.handle x y] => bVarBound n [x] ∧ bVarBound (n + 1) [y]
termination_by xs => expsWeight xs
decreasing_by
  all_goals simp only [expsWeight, expWeight]
  all_goals try (have := BvlSem.expWeight_pos y)
  all_goals omega

end Flapjack.Compiler.Backend.BvlProps
