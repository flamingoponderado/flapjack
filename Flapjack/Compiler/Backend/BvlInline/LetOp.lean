import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.HolRef

/-! Source-shaped BVL let-operation optimization. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- Check that the expression list consists of consecutive variables and has
the same length as the second list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "var_list_def"]
def varListHOL {α : Type} : Nat → List Exp → List α → Bool
  | _, [], [] => true
  | n, .var m :: xs, _ :: ys => m == n && varListHOL (n + 1) xs ys
  | _, _, _ => false

/-- Recognize an operator applied to the variables bound by a list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "dest_op_def"]
def destOp {α : Type} (expression : Exp) (args : List α) : Option ClosLang.Op :=
  match expression with
  | .op op xs => if varListHOL 0 xs args then some op else none
  | _ => none

mutual
/-- Apply the original let-operation traversal to a single expression. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "let_op_one_def"]
def letOpOne : Exp → Exp
  | .var n => .var n
  | .ifThenElse x y z => .ifThenElse (letOpOne x) (letOpOne y) (letOpOne z)
  | .let xs body =>
    let xs' := letOpList xs
    let body' := letOpOne body
    match destOp body' xs' with
    | some op => .op op xs'
    | none => .let xs' body'
  | .raise body => .raise (letOpOne body)
  | .handle body handler => .handle (letOpOne body) (letOpOne handler)
  | .tick body => .tick (letOpOne body)
  | .force location index => .force location index
  | .op op xs => .op op (letOpList xs)
  | .call ticks dest xs => .call ticks dest (letOpList xs)
termination_by expression => sizeOf expression

/-- Apply the original let-operation traversal to an expression list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "let_op_one_def"]
def letOpList : List Exp → List Exp
  | [] => []
  | e :: es => letOpOne e :: letOpList es
termination_by expressions => sizeOf expressions
end

/-- The original list form of let-operation optimization. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "let_op_def"]
def letOp (expressions : List Exp) : List Exp := letOpList expressions

/-- Select the optimized singleton, retaining the source's fallback case. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "let_op_sing_def"]
def letOpSing (expression : Exp) : Exp :=
  match letOp [expression] with
  | result :: _ => result
  | [] => .op (.intOp (.const 0)) []

/-- The single-expression traversal and list traversal agree with `letOp`. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "let_op_one"]
theorem letOpOne_equivalence :
    (∀ expression, letOp [expression] = [letOpOne expression]) ∧
    (∀ expressions, letOpList expressions = letOp expressions) := by
  constructor
  · intro expression; simp [letOp, letOpList]
  · intro expressions; rfl

end Flapjack.Compiler.Backend.BvlInline
