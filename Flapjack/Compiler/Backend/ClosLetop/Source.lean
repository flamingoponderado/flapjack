module

public import Flapjack.Compiler.Backend.ClosLang.Syntax

@[expose] public section

/-! Source-shaped total traversal for closure let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang

/-- Check that variables enumerate the bindings from the given index. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "var_list_def"]
def varList {α : Type} : Nat → List Exp → List α → Bool
  | _, [], [] => true
  | n, .var _ m :: xs, _ :: ys => (m == n) && varList (n + 1) xs ys
  | _, _, _ => false

/-- Recognize an operation applied to all its bound variables. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "dest_op_def"]
def destOp {α : Type} : Exp → List α → Option Op
  | .op _ op xs, args => if varList 0 xs args then some op else none
  | _, _ => none

mutual
/-- Clean up a closure expression in the original traversal order. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileSing : Exp → Exp
  | .var t v => .var t v
  | .ifThenElse t x y z => .ifThenElse t (compileSing x) (compileSing y) (compileSing z)
  | .let t xs body =>
      let ys := compileList xs
      let nextBody := compileSing body
      match destOp nextBody ys with
      | some op => .op t op ys
      | none => .let t ys nextBody
  | .raise t x => .raise t (compileSing x)
  | .handle t x y => .handle t (compileSing x) (compileSing y)
  | .op t op xs => .op t op (compileList xs)
  | .tick t x => .tick t (compileSing x)
  | .call t ticks dest xs => .call t ticks dest (compileList xs)
  | .app t loc x xs => .app t loc (compileSing x) (compileList xs)
  | .fn name loc vs arity body => .fn name loc vs arity (compileSing body)
  | .letrec names loc vs fns body => .letrec names loc vs (compileFuns fns) (compileSing body)

/-- Process expression lists in their original order. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileList : List Exp → List Exp
  | [] => []
  | x :: xs => compileSing x :: compileList xs

/-- Process recursive bodies without changing their arities. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "let_op_sing_def"]
def compileFuns : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest => (arity, compileSing body) :: compileFuns rest
end

/-- Let-operation cleanup preserves the length of the expression list. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "LENGTH_let_op"]
theorem compileList_length (xs : List Exp) : (compileList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [compileList, ih]

/-- Incremental cleanup discards the auxiliary component. -/
@[hol "cakeml/compiler/backend/clos_letopScript.sml" "compile_inc_def"]
def compileInc {α β : Type} (program : List Exp × α) : List Exp × List β :=
  (compileList program.1, [])

end Flapjack.Compiler.Backend.ClosLetop
