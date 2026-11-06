import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Source-shaped total traversal for closure free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang

mutual
/-- Replace out-of-scope variables with the source type-error expression. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeSing (bound : Nat) : Exp → Exp
  | .var t v => if v < bound then .var t v else .op t (.memOp .el) []
  | .ifThenElse t x y z => .ifThenElse t (removeSing bound x) (removeSing bound y) (removeSing bound z)
  | .let t xs body =>
      let ys := removeList bound xs
      .let t ys (removeSing (bound + ys.length) body)
  | .raise t x => .raise t (removeSing bound x)
  | .handle t x y => .handle t (removeSing bound x) (removeSing (bound + 1) y)
  | .op t op xs => .op t op (removeList bound xs)
  | .tick t x => .tick t (removeSing bound x)
  | .call t ticks dest xs => .call t ticks dest (removeList bound xs)
  | .app t loc x xs => .app t loc (removeSing bound x) (removeList bound xs)
  | .fn name loc vs arity body =>
      let captured := (vs.map List.length).getD bound
      .fn name loc vs arity (removeSing (arity + captured) body)
  | .letrec names loc vs fns body =>
      let captured := (vs.map List.length).getD bound
      .letrec names loc vs (removeFuns fns.length captured fns)
        (removeSing (fns.length + bound) body)

/-- Remove free variables from a list in source order. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeList (bound : Nat) : List Exp → List Exp
  | [] => []
  | x :: xs => removeSing bound x :: removeList bound xs

/-- Process recursive functions with their shared captured-environment size. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "remove_fvs_sing_def"]
def removeFuns (count captured : Nat) : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest =>
      (arity, removeSing (arity + count + captured) body) :: removeFuns count captured rest
end

/-- Free-variable removal preserves list length. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "LENGTH_remove_fvs"]
theorem removeList_length (bound : Nat) (xs : List Exp) : (removeList bound xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [removeList, ih]

/-- Free-variable removal for a closed program. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "compile_def"]
def compile (expressions : List Exp) : List Exp := removeList 0 expressions

/-- Incremental removal discards the auxiliary component. The input type and
output auxiliary element type are independent as in HOL. -/
@[hol "cakeml/compiler/backend/clos_fvsScript.sml" "compile_inc_def"]
def compileInc {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compile program.1, [])

end Flapjack.Compiler.Backend.ClosFvs
