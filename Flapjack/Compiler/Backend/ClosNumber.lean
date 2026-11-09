import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Assign fresh code locations to closure expressions. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosLang

mutual
/-- Renumber closures, traversing each expression in the source's order. -/
@[hol "cakeml/compiler/backend/clos_numberScript.sml" "renumber_code_locs_def"]
def renumber (n : Nat) : Exp → Nat × Exp
  | .var t v => (n, .var t v)
  | .ifThenElse t x y z =>
      let (n, x) := renumber n x
      let (n, y) := renumber n y
      let (n, z) := renumber n z
      (n, .ifThenElse t x y z)
  | .let t xs x =>
      let (n, xs) := renumberList n xs
      let (n, x) := renumber n x
      (n, .let t xs x)
  | .raise t x =>
      let (n, x) := renumber n x
      (n, .raise t x)
  | .tick t x =>
      let (n, x) := renumber n x
      (n, .tick t x)
  | .op t op xs =>
      let (n, xs) := renumberList n xs
      (n, .op t op xs)
  | .app t _ x xs =>
      let (n, x) := renumber n x
      let (n, xs) := renumberList n xs
      (n, .app t none x xs)
  | .fn t _ vs args x =>
      let (n, x) := renumber n x
      (n + 2, .fn t (some n) vs args x)
  | .letrec t _ vs fs x =>
      let (m, fs') := renumberFuns n fs
      let (n, x) := renumber (m + 2 * fs'.length) x
      (n, .letrec t (some m) vs fs' x)
  | .handle t x y =>
      let (n, x) := renumber n x
      let (n, y) := renumber n y
      (n, .handle t x y)
  | .call t _ _ xs =>
      let (n, xs) := renumberList n xs
      (n, .op t (.intOp .add) xs)

/-- List clauses of the location traversal. -/
@[hol "cakeml/compiler/backend/clos_numberScript.sml" "renumber_code_locs_def"]
def renumberList (n : Nat) : List Exp → Nat × List Exp
  | [] => (n, [])
  | x :: xs =>
      let (n, x) := renumber n x
      let (n, xs) := renumberList n xs
      (n, x :: xs)

/-- Traverse recursive bodies and preserve their associated arities. -/
def renumberFuns (n : Nat) : List (Nat × Exp) → Nat × List (Nat × Exp)
  | [] => (n, [])
  | (arity, x) :: xs =>
      let (n, x) := renumber n x
      let (n, xs) := renumberFuns n xs
      (n, (arity, x) :: xs)
end

/-- Number an incremental program after reserving the even-aligned entry
locations, then prepend the source's embedded original location. -/
@[hol "cakeml/compiler/backend/clos_numberScript.sml" "compile_inc_def"]
def compileInc (n : Nat) (xs : List Exp) : Nat × List Exp :=
  let next := n + max xs.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  let (m, ys) := renumberList aligned xs
  (m, .op .none (.intOp (.const (Int.ofNat n))) [] :: ys)

/-- Thread a state transformation through code while retaining its auxiliary
component; the state, code and auxiliary types are independent. -/
@[hol "cakeml/compiler/backend/clos_numberScript.sml" "ignore_table_def"]
def ignoreTable {State Code State' Code' Aux : Type} (f : State → Code → State' × Code')
    (st : State) (input : Code × Aux) : State' × (Code' × Aux) :=
  let (st', code') := f st input.1
  (st', (code', input.2))

end Flapjack.Compiler.Backend.ClosNumber
