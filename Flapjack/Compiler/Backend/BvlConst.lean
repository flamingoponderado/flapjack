module

public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Compiler.Backend.BvlToBvi.Budget

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Executable helpers and fuel-bounded traversal for the BVL constant pass.
The total traversal and its executable correspondence are in the `BvlConst`
submodules; pass-semantics correctness remains open. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl BvlToBvi
open ClosLang (Op)

private def const (n : Int) : Exp := .op (.intOp (.const n)) []
/-- Construct the source Boolean expression. -/
def bool (b : Bool) : Exp := .op (.blockOp (.cons (if b then 1 else 0))) []
/-- Recognize an argument-free integer constant. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "dest_simple_def"]
def simple : Exp → Option Int
  | .op (.intOp (.const n)) [] => some n
  | _ => none

/-- The `dest_simple` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "dest_simple_pmatch"]
theorem simple_pmatch (op : Exp) :
    simple op = match op with | .op (.intOp (.const i)) [] => some i | _ => none := rfl

/-- Recognize a binary operation whose second operand is an integer constant. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "case_op_const_def"]
def opConst : Exp → Option (Op × Exp × Int)
  | .op op [x, .op (.intOp (.const n)) []] => some (op, x, n)
  | _ => none

/-- The `case_op_const` matcher written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "case_op_const_pmatch"]
theorem opConst_pmatch (exp : Exp) :
    opConst exp = match exp with
      | .op op [x, .op (.intOp (.const n)) []] => some (op, x, n)
      | _ => none := rfl
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

/-- Orient a simple first operand for the binary arithmetic rewrites. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp_flip_def"]
def smartOpFlip (op : Op) (x y : Exp) : Op × Exp × Exp :=
  match simple x, op with
    | some _, .intOp .add => (Op.intOp .add, y, x)
    | some _, .intOp .mult => (Op.intOp .mult, y, x)
    | some n, .intOp .sub => (Op.intOp .add, y, const (-n))
    | _, _ => (op, x, y)

/-- The operand orientation written as HOL's case expression. HOL tests the
operation with `MEM op [IntOp Add; IntOp Mult]` and `op = IntOp Sub`; this file
cannot render those as `∈`/`=`, because `ClosLang.Op` gets its `DecidableEq`
instance only in `ConfigDecidableEq`, which imports the whole `Backend` and so
would be circular here. The reviewed `Op` datatype does derive `LawfulBEq`, and
`smartOpFlip` itself matches `op` structurally rather than testing equality, so
the statement uses the executable `.elem` and `==` tests for HOL's two
conditions. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp_flip_pmatch"]
theorem smartOpFlip_pmatch (op : Op) (x1 x2 : Exp) :
    smartOpFlip op x1 x2 =
      match simple x1 with
      | some i =>
          if [Op.intOp .add, Op.intOp .mult].elem op then (op, x2, x1)
          else if op == Op.intOp .sub then
            (Op.intOp .add, x2, .op (.intOp (.const (-i))) [])
          else (op, x1, x2)
      | none => (op, x1, x2) := by
  cases h : simple x1 with
  | none => simp [smartOpFlip, h]
  | some i =>
    cases op with
    | intOp io =>
      cases io
      all_goals simp [smartOpFlip, h, const]
    | _ => simp [smartOpFlip, h]

/-- Apply the source binary operation rewrites to an already-oriented tuple. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp2_def"]
def smartOp2 (input : Op × Exp × Exp) : Exp :=
  let (op, x, y) := input
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

/-- The binary rewrite dispatch written as HOL's case expression. HOL's
statement inlines the local `mk_add_const`/`mk_add`/`mk_sub`/`mk_mul` lets;
this file renders those helpers as the private definitions the executed
`smartOp2` uses, so the case expression below is the definition body. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp2_pmatch"]
theorem SmartOp2_pmatch (op : Op) (x1 x2 : Exp) :
    smartOp2 (op, x1, x2) = (match op with
      | .intOp .add => mkAdd x1 x2
      | .intOp .sub => mkSub x1 x2
      | .intOp .mult => mkMul x1 x2
      | .intOp .div => match simple x1, simple x2 with
          | some a, some b => if a == 0 then .op op [x1, x2] else const (Int.fdiv b a)
          | _, _ => .op op [x1, x2]
      | .intOp .mod => match simple x1, simple x2 with
          | some a, some b => if a == 0 then .op op [x1, x2] else const (Int.fmod b a)
          | _, _ => .op op [x1, x2]
      | .intOp .less => match simple x1, simple x2 with
          | some a, some b => bool (b < a)
          | _, _ => .op op [x1, x2]
      | .intOp .lessEq => match simple x1, simple x2 with
          | some a, some b => bool (b ≤ a)
          | _, _ => .op op [x1, x2]
      | .intOp .greater => match simple x1, simple x2 with
          | some a, some b => bool (b > a)
          | _, _ => .op op [x1, x2]
      | .intOp .greaterEq => match simple x1, simple x2 with
          | some a, some b => bool (b ≥ a)
          | _, _ => .op op [x1, x2]
      | .blockOp .equal => match simple x1, simple x2 with
          | some a, some b => bool (b == a)
          | some a, none => .op (.blockOp (.equalConst (.int a))) [x2]
          | none, some b => .op (.blockOp (.equalConst (.int b))) [x1]
          | _, _ => .op op [x1, x2]
      | .memOp .el => match simple x1 with
          | some n => if n < 0 then .op op [x1, x2] else .op (.blockOp (.elemAt n.toNat)) [x2]
          | none => .op op [x1, x2]
      | _ => .op op [x1, x2]) := by
  rfl

private def smart2 (op : Op) (x y : Exp) : Exp :=
  smartOp2 (smartOpFlip op x y)

/-- Recognize an integer constant-equality operation. HOL's `SmartOp1` calls
this recognition; the Lean `smartOp1` matches the same operation shape inline,
so this definition is the source-shaped rendering rather than a second
executable path. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "dest_EqualInt_def"]
def destEqualInt : Op → Option Int
  | .blockOp (.equalConst (.int i)) => some i
  | _ => none

/-- The constant-equality recognition written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "dest_EqualInt_pmatch"]
theorem dest_EqualInt_pmatch (x : Op) :
    destEqualInt x = (match x with
      | .blockOp (.equalConst (.int i)) => some i
      | _ => none) := by
  rfl

/-- Apply the source's unary constant-equality rewrite. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp1_def"]
def smartOp1 (op : Op) (x : Exp) : Exp :=
  match op, simple x with
  | .blockOp (.equalConst (.int a)), some b => bool (b == a)
  | _, _ => .op op [x]

/-- Apply the source's operation-specific constant rewrites. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp_def"]
def smartOp (op : Op) : List Exp → Exp
  | [x, y] => smart2 op x y
  | [x] => smartOp1 op x
  | xs => .op op xs

/-- The `SmartOp` dispatch written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "SmartOp_pmatch"]
theorem smartOp_pmatch (op : Op) (xs : List Exp) :
    smartOp op xs = match xs with
      | [x1, x2] => smartOp2 (smartOpFlip op x1 x2)
      | [x] => smartOp1 op x
      | _ => .op op xs := by
  cases xs with
  | nil => rfl
  | cons x1 rest =>
    cases rest with
    | nil => rfl
    | cons x2 rest' =>
      cases rest' with
      | nil => rfl
      | cons x3 rest'' => rfl

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

/-- The variable case of the executable alias deletion. -/
theorem deleteVar_var (n : Nat) : deleteVar (.var n) = .op (.intOp (.const 0)) [] := rfl

/-- The alias deletion written as HOL's case expression. -/
@[hol "cakeml/compiler/backend/bvl_constScript.sml" "delete_var_pmatch"]
theorem deleteVar_pmatch (op : Exp) :
    deleteVar op = match op with
      | .var _ => .op (.intOp (.const 0)) []
      | x => x := by
  cases op
  all_goals rfl

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
