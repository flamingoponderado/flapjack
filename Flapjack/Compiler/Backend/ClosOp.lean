import Flapjack.Compiler.Backend.ClosLang.Budget
import Flapjack.Compiler.Backend.ClosOp.EqBudget
import Flapjack.Compiler.Backend.ClosOp.SourceHelpers

/-! Bounded infrastructure for the closure smart-operation pass. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

private def intConst : Exp → Option Int := destOpNil destConst
def cons : Exp → Option (Nat × List Exp) := destOp destCons
private def nil : Exp → Option Nat := destOpNil destCons
private def constant : Exp → Option ConstPart := destOpNil destConstant

/-- The source pair matcher agrees with the previous pair of Flapjack
matchers; this is infrastructure without a separate HOL theorem. -/
theorem destOpConsts_eq_previous (x y : Exp) :
    destOpConsts x y = match intConst x, intConst y with
      | some i, some j => some (i, j)
      | _, _ => none := by
  unfold destOpConsts intConst
  cases hx : destOpNil destConst x <;> cases hy : destOpNil destConst y <;> simp_all
private def eqConst (p : ConstPart) (x : Exp) : Exp := .op .none (.blockOp (.equalConst p)) [x]

private def directEqPrevious (x y : Exp) : Option Exp :=
  match intConst x, intConst y with
  | some i, some j => some (mkBool (i == j))
  | some i, none => some (eqConst (.int i) y)
  | none, some j => some (eqConst (.int j) x)
  | none, none =>
      match constant x, constant y with
      | some p, some q => some (mkBool (decide (p = q)))
      | some p, none => some (eqConst p y)
      | none, some q => some (eqConst q x)
      | none, none =>
          match nil x, nil y with
          | some i, some j => some (mkBool (i == j))
          | some i, none => some (.op .none (.blockOp (.tagLenEq i 0)) [y])
          | none, some j => some (.op .none (.blockOp (.tagLenEq j 0)) [x])
          | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_const_def"]
def eqDirectConst (x y : Exp) : Option Exp :=
  match intConst x, intConst y with
  | some i, some j => some (mkBool (i == j))
  | some i, none => some (eqConst (.int i) y)
  | none, some j => some (eqConst (.int j) x)
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_constant_def"]
def eqDirectConstant (x y : Exp) : Option Exp :=
  match constant x, constant y with
  | some p, some q => some (mkBool (decide (q = p)))
  | some p, none => some (eqConst p y)
  | none, some q => some (eqConst q x)
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_nil_def"]
def eqDirectNil (x y : Exp) : Option Exp :=
  match nil x, nil y with
  | some i, some j => some (mkBool (i == j))
  | some i, none => some (.op .none (.blockOp (.tagLenEq i 0)) [y])
  | none, some j => some (.op .none (.blockOp (.tagLenEq j 0)) [x])
  | none, none => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "eq_direct_def"]
def directEq (x y : Exp) : Option Exp :=
  match eqDirectConst x y with
  | some result => some result
  | none =>
    match eqDirectConstant x y with
    | some result => some result
    | none => eqDirectNil x y

/-- The source's staged equality recognizer agrees with the previous
Flapjack implementation for every pair; this is not a HOL theorem. -/
theorem directEq_eq_previous (x y : Exp) : directEq x y = directEqPrevious x y := by
  unfold directEq eqDirectConst eqDirectConstant eqDirectNil directEqPrevious
  cases hi : intConst x <;> cases hj : intConst y <;>
    cases hp : constant x <;> cases hq : constant y <;>
    cases hn : nil x <;> cases hm : nil y <;> simp_all [eq_comm]

@[hol "cakeml/compiler/backend/clos_opScript.sml" "int_op_def"]
def integerOp (op : Op) (i j : Int) : Option Exp :=
  match op with
  | .intOp .add => some (mkInt (j + i))
  | .intOp .sub => some (mkInt (j - i))
  | .intOp .mult => some (mkInt (j * i))
  | .intOp .div => some (mkInt (if i == 0 then 0 else Int.fdiv j i))
  | .intOp .mod => some (mkInt (if i == 0 then 0 else Int.fmod j i))
  | .intOp .less => some (mkBool (j < i))
  | .intOp .lessEq => some (mkBool (j ≤ i))
  | .intOp .greater => some (mkBool (i < j))
  | .intOp .greaterEq => some (mkBool (i ≤ j))
  | .blockOp .equal => some (mkBool (j == i))
  | _ => none

private def consOpPrevious (op : Op) (tag : Nat) (xs : List Exp) : Option Exp :=
  match op with
  | .blockOp (.elemAt n) =>
      if n < xs.length then some (.let .none xs (.var .none (xs.length - (n + 1)))) else none
  | .blockOp (.tagLenEq n len) => some (.let .none xs (mkBool (n == tag && xs.length == len)))
  | .blockOp (.tagEq n) => some (.let .none xs (mkBool (n == tag)))
  | .blockOp (.lenEq len) => some (.let .none xs (mkBool (xs.length == len)))
  | _ => none

@[hol "cakeml/compiler/backend/clos_opScript.sml" "cons_op_def"]
def consOp (op : Op) (tag : Nat) (xs : List Exp) : Option Exp :=
  match destElemAt op with
  | some n =>
      if n < xs.length then some (.let .none xs (.var .none (xs.length - (n + 1)))) else none
  | none =>
    match destTagLenEq op with
    | some (n, len) => some (.let .none xs (mkBool (n == tag && xs.length == len)))
    | none =>
      match destTagEq op with
      | some n => some (.let .none xs (mkBool (n == tag)))
      | none =>
        match destLenEq op with
        | some len => some (.let .none xs (mkBool (xs.length == len)))
        | none => none

/-- The source matcher composition preserves the previous Flapjack
constructor simplifier on every input; this is not a separate HOL theorem. -/
theorem consOp_eq_previous (op : Op) (tag : Nat) (xs : List Exp) :
    consOp op tag xs = consOpPrevious op tag xs := by
  cases op <;> simp [consOp, consOpPrevious, destElemAt, destTagLenEq, destTagEq, destLenEq]
  case blockOp op =>
    cases op <;> simp

@[hol "cakeml/compiler/backend/clos_opScript.sml" "dont_lift_def"]
def dontLift (e : Exp) : Bool := (intConst e).isSome || (nil e).isSome || (constant e).isSome

/-- Lift effectful terms into bindings while traversing constructor children
in source order. -/
def liftFuel : Nat → List Exp → Nat → List Exp → Option (List Exp × Nat × List Exp)
  | _, [], n, binds => some ([], n, binds)
  | 0, _ :: _, _, _ => none
  | fuel + 1, x :: xs, n, binds => do
      if dontLift x then
        let (xs, n, binds) ← liftFuel fuel xs n binds
        pure (x :: xs, n, binds)
      else match cons x with
        | some (tag, ys) =>
            let (ys, n, binds) ← liftFuel fuel ys n binds
            let (xs, n, binds) ← liftFuel fuel xs n binds
            pure (.op .none (.blockOp (.cons tag)) ys :: xs, n, binds)
        | none =>
            let (xs, next, binds) ← liftFuel fuel xs (n + 1) (binds ++ [x])
            pure (.var .none n :: xs, next, binds)

/-- Preserve a successful traversal and retry exhaustion with structural fuel. -/
def liftBounded (fuel : Nat) (xs : List Exp) (n : Nat) (binds : List Exp) :
    Option (List Exp × Nat × List Exp) :=
  match liftFuel fuel xs n binds with
  | some result => some result
  | none => liftFuel (max fuel (listBudget xs + 1)) xs n binds

/-- Produce the source sequence of pure equality checks. -/
def eqListFuel : Nat → List (Exp × Exp) → Option (List Exp)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, (x, y) :: rest => do
      let first ← match directEq x y with
        | some e => pure [e]
        | none =>
          match cons x, cons y with
          | none, none => pure [.op .none (.blockOp .equal) [x, y]]
          | some (tagX, xs), some (tagY, ys) =>
              if tagX != tagY || xs.length != ys.length then pure [mkBool false]
              else eqListFuel fuel (xs.reverse.zip ys.reverse)
          | some (tag, xs), none =>
              let fields := xs.reverse.zip (List.range xs.length) |>.map fun (e, i) =>
                (e, Exp.op .none (.blockOp (.elemAt i)) [y])
              pure (.op .none (.blockOp (.tagLenEq tag xs.length)) [y] :: (← eqListFuel fuel fields))
          | none, some _ => eqListFuel fuel [(y, x)]
      pure (first ++ (← eqListFuel fuel rest))

/-- Preserve a successful equality decomposition and retry exhaustion with
a constructor-based bound. -/
def eqListBounded (fuel : Nat) (pairs : List (Exp × Exp)) : Option (List Exp) :=
  match eqListFuel fuel pairs with
  | some result => some result
  | none => eqListFuel (max fuel (eqPairsWeight pairs + 1)) pairs

private def conj : List Exp → Exp
  | [] => mkBool true
  | [x] => x
  | x :: xs => .ifThenElse .none x (conj xs) (mkBool false)

@[hol "cakeml/compiler/backend/clos_opScript.sml" "is_Var_def"]
def isVar : Exp → Bool
  | .var _ _ => true
  | _ => false

/-- The closure smart constructor, with bounded retries for its recursive
lifting and equality decomposition. -/
def smartFuel (fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) : Option Exp := do
  let default := Exp.op trace op xs
  match xs with
  | [x] =>
      match cons x with
      | some (tag, args) => pure ((consOp op tag args).getD default)
      | none => pure default
  | [x, y] =>
      match destOpConsts x y with
      | some (i, j) => pure ((integerOp op i j).getD default)
      | none =>
          match op with
          | .blockOp .equal =>
              if isVar x && isVar y then return default
              match directEq x y with
              | some e => pure e
              | none =>
                  let (lifted, _, binds) ← liftBounded fuel [x, y] 0 []
                  match lifted with
                  | [x, y] => pure (.let .none binds (conj (← eqListBounded fuel [(x, y)])))
                  | _ => pure default
          | _ => pure default
  | _ => pure default

end Flapjack.Compiler.Backend.ClosOp
