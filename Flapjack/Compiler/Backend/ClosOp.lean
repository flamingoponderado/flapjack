import Flapjack.Compiler.Backend.ClosLang.Budget

/-! Bounded infrastructure for the closure smart-operation pass. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

private def mkBool (b : Bool) : Exp := .op .none (.blockOp (.cons (if b then 1 else 0))) []
private def mkInt (i : Int) : Exp := .op .none (.intOp (.const i)) []
private def intConst : Exp → Option Int
  | .op _ (.intOp (.const i)) [] => some i
  | _ => none
def cons : Exp → Option (Nat × List Exp)
  | .op _ (.blockOp (.cons tag)) xs => some (tag, xs)
  | _ => none
private def nil : Exp → Option Nat
  | .op _ (.blockOp (.cons tag)) [] => some tag
  | _ => none
private def constant : Exp → Option ConstPart
  | .op _ (.blockOp (.constant (.constInt i))) [] => some (.int i)
  | .op _ (.blockOp (.constant (.constStr s))) [] => some (.str s)
  | .op _ (.blockOp (.constant (.constWord64 w))) [] => some (.w64 w)
  | _ => none
private def eqConst (p : ConstPart) (x : Exp) : Exp := .op .none (.blockOp (.equalConst p)) [x]

private def directEq (x y : Exp) : Option Exp :=
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

private def integerOp (op : Op) (i j : Int) : Option Exp :=
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

private def consOp (op : Op) (tag : Nat) (xs : List Exp) : Option Exp :=
  match op with
  | .blockOp (.elemAt n) =>
      if n < xs.length then some (.let .none xs (.var .none (xs.length - (n + 1)))) else none
  | .blockOp (.tagLenEq n len) => some (.let .none xs (mkBool (n == tag && xs.length == len)))
  | .blockOp (.tagEq n) => some (.let .none xs (mkBool (n == tag)))
  | .blockOp (.lenEq len) => some (.let .none xs (mkBool (xs.length == len)))
  | _ => none

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

private def conj : List Exp → Exp
  | [] => mkBool true
  | [x] => x
  | x :: xs => .ifThenElse .none x (conj xs) (mkBool false)

private def isVar : Exp → Bool
  | .var _ _ => true
  | _ => false

/-- The closure smart constructor, returning `none` only when bounded
recursive equality decomposition exhausts fuel. -/
def smartFuel (fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) : Option Exp := do
  let default := Exp.op trace op xs
  match xs with
  | [x] =>
      match cons x with
      | some (tag, args) => pure ((consOp op tag args).getD default)
      | none => pure default
  | [x, y] =>
      match intConst x, intConst y with
      | some i, some j => pure ((integerOp op i j).getD default)
      | _, _ =>
          match op with
          | .blockOp .equal =>
              if isVar x && isVar y then return default
              match directEq x y with
              | some e => pure e
              | none =>
                  let (lifted, _, binds) ← liftBounded fuel [x, y] 0 []
                  match lifted with
                  | [x, y] => pure (.let .none binds (conj (← eqListFuel fuel [(x, y)])))
                  | _ => pure default
          | _ => pure default
  | _ => pure default

end Flapjack.Compiler.Backend.ClosOp
