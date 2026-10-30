import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.BvlToBvi.Budget

/-! Executable helpers and fuel-bounded traversal for the BVL constant pass.
The total traversal and its executable correspondence are in the `BvlConst`
submodules; pass-semantics correctness remains open. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl BvlToBvi
open ClosLang (Op)

private def const (n : Int) : Exp := .op (.intOp (.const n)) []
private def bool (b : Bool) : Exp := .op (.blockOp (.cons (if b then 1 else 0))) []
private def simple : Exp → Option Int
  | .op (.intOp (.const n)) [] => some n
  | _ => none
private def opConst : Exp → Option (Op × Exp × Int)
  | .op op [x, .op (.intOp (.const n)) []] => some (op, x, n)
  | _ => none
private def add (x y : Exp) : Exp := .op (.intOp .add) [x, y]
private def sub (x y : Exp) : Exp := .op (.intOp .sub) [x, y]
private def mul (x y : Exp) : Exp := .op (.intOp .mult) [x, y]
private def addConst (x : Exp) (n : Int) : Exp := if n == 0 then x else add x (const n)

private def mkAdd (x y : Exp) : Exp :=
  match simple y with
  | some n =>
      match opConst x with
      | some (.intOp .add, a, m) => addConst a (n + m)
      | some (.intOp .sub, a, m) => sub a (const (n + m))
      | some _ => add x y
      | none => match simple x with
          | some m => const (n + m)
          | none => addConst x n
  | none =>
      match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => addConst (add a b) (n + m)
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => sub (sub a b) (const (n + m))
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => addConst (sub a b) (n + m)
      | _, _ => add x y

private def mkSub (x y : Exp) : Exp :=
  match simple y with
  | some n =>
      match opConst x with
      | some (.intOp .add, a, m) => sub a (const (n - m))
      | some (.intOp .sub, a, m) => addConst a (n - m)
      | some _ => sub x y
      | none => match simple x with
          | some m => const (n - m)
          | none => sub x y
  | none =>
      match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) => add (sub a b) (const (n - m))
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) => sub (add a b) (const (n - m))
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) => addConst (add a b) (n - m)
      | _, _ => sub x y

private def mkMul (x y : Exp) : Exp :=
  match simple y with
  | some n =>
      match opConst x with
      | some (.intOp .mult, a, m) => mul a (const (n * m))
      | some _ => mul x y
      | none => match simple x with
          | some m => const (n * m)
          | none => if n == 1 then x else if n == -1 then mkSub x (const 0) else mul x y
  | none =>
      match opConst x, opConst y with
      | some (.intOp .mult, a, m), some (.intOp .mult, b, n) => mul (const (n * m)) (mul a b)
      | _, _ => mul x y

private def smart2 (op : Op) (x y : Exp) : Exp :=
  let (op, x, y) := match simple x, op with
    | some _, .intOp .add => (Op.intOp .add, y, x)
    | some _, .intOp .mult => (Op.intOp .mult, y, x)
    | some n, .intOp .sub => (Op.intOp .add, y, const (-n))
    | _, _ => (op, x, y)
  match op with
  | .intOp .add => mkAdd x y
  | .intOp .sub => mkSub x y
  | .intOp .mult => mkMul x y
  | .intOp .div => match simple x, simple y with
      | some a, some b => if a == 0 then .op op [x, y] else const (Int.fdiv b a)
      | _, _ => .op op [x, y]
  | .intOp .mod => match simple x, simple y with
      | some a, some b => if a == 0 then .op op [x, y] else const (Int.fmod b a)
      | _, _ => .op op [x, y]
  | .intOp .less => match simple x, simple y with
      | some a, some b => bool (b < a)
      | _, _ => .op op [x, y]
  | .intOp .lessEq => match simple x, simple y with
      | some a, some b => bool (b ≤ a)
      | _, _ => .op op [x, y]
  | .intOp .greater => match simple x, simple y with
      | some a, some b => bool (b > a)
      | _, _ => .op op [x, y]
  | .intOp .greaterEq => match simple x, simple y with
      | some a, some b => bool (b ≥ a)
      | _, _ => .op op [x, y]
  | .blockOp .equal => match simple x, simple y with
      | some a, some b => bool (b == a)
      | some a, none => .op (.blockOp (.equalConst (.int a))) [y]
      | none, some b => .op (.blockOp (.equalConst (.int b))) [x]
      | _, _ => .op op [x, y]
  | .memOp .el => match simple x with
      | some n => if n < 0 then .op op [x, y] else .op (.blockOp (.elemAt n.toNat)) [y]
      | none => .op op [x, y]
  | _ => .op op [x, y]

/-- Apply the source's operation-specific constant rewrites. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp_def"]
def smartOp (op : Op) : List Exp → Exp
  | [x, y] => smart2 op x y
  | [x] => match op, simple x with
      | .blockOp (.equalConst (.int a)), some b => bool (b == a)
      | _, _ => .op op [x]
  | xs => .op op xs

private def extract (e : Exp) (restLength : Nat) : Option Exp :=
  match e with
  | .var n => some (.var (n + restLength + 1))
  | .op (.intOp (.const n)) _ => some (const n)
  | .op (.blockOp (.cons t)) [] => some (.op (.blockOp (.cons t)) [])
  | _ => none

/-- Build the constant environment contributed by a list of let bindings. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "extract_list_def"]
def extractList : List Exp → List (Option Exp)
  | [] => []
  | x :: xs => extract x xs.length :: extractList xs

/-- Replace let-bound variable aliases with the source's zero placeholder. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "delete_var_def"]
def deleteVar : Exp → Exp
  | .var _ => const 0
  | e => e

/-- Apply constant propagation with explicit recursion fuel. -/
def compileFuel : Nat → List (Option Exp) → Exp → Option Exp
  | 0, _, _ => none
  | fuel + 1, env, e =>
      let visit := compileFuel fuel env
      match e with
      | .var v =>
          match env[v]? with
          | some (some (.var i)) => some (.var (v + i))
          | some (some x) => some x
          | _ => some (.var v)
      | .ifThenElse x y z => do
          let x ← visit x
          let y ← visit y
          let z ← visit z
          match x with
          | .op (.blockOp (.cons 1)) [] => pure y
          | .op (.blockOp (.cons 0)) [] => pure z
          | _ => pure (.ifThenElse x y z)
      | .let xs y => do
          let xs ← xs.mapM visit
          let y ← compileFuel fuel (extractList xs ++ env) y
          pure (.let (xs.map deleteVar) y)
      | .handle x y => do pure (.handle (← visit x) (← compileFuel fuel (none :: env) y))
      | .raise x => do pure (.raise (← visit x))
      | .op op xs => do pure (smartOp op (← xs.mapM visit))
      | .tick x => do pure (.tick (← visit x))
      | .force loc v =>
          match env[v]? with
          | some (some (.var i)) => some (.force loc (v + i))
          | _ => some (.force loc v)
      | .call t dest xs => do pure (.call t dest (← xs.mapM visit))

/-- Preserve a successful constant-folding traversal and retry exhaustion
with a structural budget. -/
def compileBounded (fuel : Nat) (env : List (Option Exp)) (e : Exp) : Option Exp :=
  match compileFuel fuel env e with
  | some result => some result
  | none => compileFuel (max fuel (expBudget e + 1)) env e

end Flapjack.Compiler.Backend.BvlConst
