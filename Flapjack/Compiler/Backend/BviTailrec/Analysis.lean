import Flapjack.Compiler.Backend.BviTailrec

/-! Bounded transcription of the type and operator analysis used by BVI
tail-recursion elimination. The total HOL functions and correspondence remain
open; `none` denotes exhausted traversal fuel. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- The source pass's type abstraction for values. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "v_ty"]
inductive ValueType where
  | int | list | any
  deriving DecidableEq, BEq

/-- The source pass's associative accumulator operations. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "assoc_op"]
inductive AssocOp where
  | plus | times | append | noop
  deriving DecidableEq, BEq

/-- Type required by the accumulator operation. -/
def opType : AssocOp → ValueType
  | .plus | .times => .int
  | .append => .list
  | .noop => .any

/-- Classify operations as source accumulator operators. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "from_op_def"]
def fromOp : ClosLang.Op → AssocOp
  | .intOp .add => .plus
  | .intOp .mult => .times
  | .blockOp .listAppend => .append
  | _ => .noop

/-- Convert a source accumulator operator into its BVI operation. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "to_op_def"]
def toOp : AssocOp → ClosLang.Op
  | .plus => .intOp .add
  | .times => .intOp .mult
  | .append => .blockOp .listAppend
  | .noop => .intOp .mod

private def small (i : Int) : Bool := -268435457 ≤ i && i ≤ 268435457
private def isConst : ClosLang.Op → Bool
  | .intOp (.const i) => small i
  | _ => false
private def isArith : ClosLang.Op → Bool
  | .intOp .add | .intOp .sub | .intOp .mult => true
  | _ => false
private def isRel : ClosLang.Op → Bool
  | .intOp .less | .intOp .lessEq | .intOp .greater | .intOp .greaterEq => true
  | _ => false
private def argType : ClosLang.Op → ValueType
  | .intOp (.const i) => if small i then .int else .any
  | .intOp .add | .intOp .sub | .intOp .mult | .intOp .div | .intOp .mod
  | .intOp .less | .intOp .lessEq | .intOp .greater | .intOp .greaterEq => .int
  | .blockOp .listAppend => .list
  | _ => .any
private def decideType : ValueType → ValueType → ValueType
  | .int, .int => .int
  | .list, .list => .list
  | _, _ => .any
private def update (ty : ValueType) (e : Exp) (ctx : List ValueType) : List ValueType :=
  match e with
  | .var n => if ctx[n]? == some .any then ctx.set n ty else ctx
  | _ => ctx
private def updateContext (ty : ValueType) (ctx : List ValueType) (x y : Exp) : List ValueType :=
  update ty y (update ty x ctx)

mutual
  /-- Source termination test for integer terms. -/
  def termIntFuel : Nat → List ValueType → Exp → Option Bool
    | 0, _, _ => none
    | fuel + 1, ctx, e => do
      match e with
      | .var n => pure (ctx[n]? == some .int)
      | .op op [x, y] =>
          if !isArith op then pure false
          else if !(← termIntFuel fuel ctx x) then pure false else termIntFuel fuel ctx y
      | .op op [] => pure (isConst op)
      | _ => pure false

  /-- Source termination test for arbitrary and list terms. -/
  def termAnyFuel : Nat → List ValueType → Bool → Exp → Option Bool
    | 0, _, _, _ => none
    | fuel + 1, ctx, list, e => do
      match e with
      | .var n => pure (if list then ctx[n]? == some .list else n < ctx.length)
      | .op op [x, y] =>
          match op with
          | .blockOp .listAppend =>
              if !(← termAnyFuel fuel ctx true x) then pure false else termAnyFuel fuel ctx true y
          | .blockOp (.cons 0) =>
              if !(← termAnyFuel fuel ctx true x) then pure false else termAnyFuel fuel ctx false y
          | _ =>
              if !list && (isArith op || isRel op) then
                if !(← termIntFuel fuel ctx x) then pure false else termIntFuel fuel ctx y
              else pure false
      | .op (.blockOp (.cons 0)) [] => pure list
      | .op op [] => pure (!list && isConst op)
      | _ => pure false
end

def termFuel (fuel : Nat) (ctx : List ValueType) (ty : ValueType) (e : Exp) : Option Bool :=
  match ty with
  | .int => termIntFuel fuel ctx e
  | .list => termAnyFuel fuel ctx true e
  | .any => termAnyFuel fuel ctx false e

/-- Preserve a successful type test, retrying exhausted traversal with a
structural bound. -/
def termBounded (fuel : Nat) (ctx : List ValueType) (ty : ValueType) (e : Exp) : Option Bool :=
  match termFuel fuel ctx ty e with
  | some result => some result
  | none => termFuel (max fuel (expBudget e + 1)) ctx ty e

/-- Fuel-bounded check of a candidate operation; this is infrastructure for
the total source operation, which remains to be ported and reviewed. -/
def checkOpFuel (fuel : Nat) (ctx : List ValueType) (assoc : AssocOp) (loc : Nat)
    (xs : List Exp) : Option (Option Exp) := do
  match xs with
  | [left, right] =>
      let (left, right) := if assoc != .append && isRec loc left then (right, left) else (left, right)
      if !isRec loc right then return none
      if ← termBounded fuel ctx (opType assoc) left then return some (.op (toOp assoc) [left, right])
      pure none
  | _ => pure none

private abbrev Scan := List ValueType × ValueType × Bool × Option AssocOp

mutual
  /-- Analyze one expression in the source evaluation order. -/
  def scanFuel : Nat → List ValueType → Nat → Exp → Option Scan
    | 0, _, _, _ => none
    | fuel + 1, ctx, loc, e => do
      match e with
      | .var n | .force _ n => pure (ctx, ctx[n]?.getD .any, false, none)
      | .ifThenElse cond yes no =>
          let (ci, _, _, _) ← scanFuel fuel ctx loc cond
          let (ct, tt, _, ot) ← scanFuel fuel ci loc yes
          let (ce, te, _, oe) ← scanFuel fuel ci loc no
          let op := ot.orElse fun _ => oe
          let ty := match op with | none => decideType tt te | some o => decideType tt (decideType te (opType o))
          pure ((ct.zip ce).map fun (x, y) => decideType x y, ty, oe.isSome, op)
      | .let xs body =>
          let scans ← scanListFuel fuel ctx loc xs
          let types := scans.map fun (_, ty, _, _) => ty
          let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
          let (out, ty, _, op) ← scanFuel fuel (types ++ last) loc body
          pure (out.drop scans.length, ty, false, op)
      | .tick x => scanFuel fuel ctx loc x
      | .op op xs =>
          let assoc := fromOp op
          if assoc == .noop then
            if argType op == .int then
              (match xs with
              | [x, y] => if isConst op then pure (ctx, .any, false, none)
                  else pure (updateContext .int ctx x y, .any, false, none)
              | _ => if isConst op then pure (ctx, .int, false, none) else pure (ctx, .any, false, none))
            else match op, xs with
              | .blockOp (.cons 0), [] => pure (ctx, .list, false, none)
              | _, _ => pure (ctx, .any, false, none)
          else
            let ty := opType assoc
            if (← checkOpFuel fuel ctx assoc loc xs).isSome then
              pure (ctx, ty, false, some assoc)
            else if ← termBounded fuel ctx ty (.op op xs) then
              match xs with
              | [x, y] => pure (updateContext ty ctx x y, ty, false, none)
              | _ => pure (ctx, .any, false, none)
            else pure (ctx, .any, false, none)
      | _ => pure (ctx, .any, false, none)

  /-- Analyze a list, threading the context in evaluation order. -/
  def scanListFuel : Nat → List ValueType → Nat → List Exp → Option (List Scan)
    | _, _, _, [] => some []
    | 0, _, _, _ :: _ => none
    | fuel + 1, ctx, loc, x :: xs => do
      let result@(next, _, _, _) ← scanFuel fuel ctx loc x
      pure (result :: (← scanListFuel fuel next loc xs))
end

/-- Retry an exhausted scan with a structural bound. -/
def scanBounded (fuel : Nat) (ctx : List ValueType) (loc : Nat) (e : Exp) : Option Scan :=
  match scanFuel fuel ctx loc e with
  | some result => some result
  | none => scanFuel (max fuel (expBudget e + 1)) ctx loc e

/-- Retry an exhausted operand scan with a structural list bound. -/
def scanListBounded (fuel : Nat) (ctx : List ValueType) (loc : Nat) (xs : List Exp) : Option (List Scan) :=
  match scanListFuel fuel ctx loc xs with
  | some result => some result
  | none => scanListFuel (max fuel (listBudget xs + 1)) ctx loc xs

/-- Decide whether the original type analysis selected an accumulator
operation. The checked rewrite is implemented in `Rewrite`. -/
def checkExpFuel (fuel loc arity : Nat) (e : Exp) : Option (Option AssocOp) := do
  if !(← hasRecBounded fuel loc e) then return none
  let (_, ty, _, op) ← scanBounded fuel (List.replicate arity .any) loc e
  match op with
  | some o => pure (if ty == opType o then some o else none)
  | none => pure none

/-- Return unchanged code only when analysis proves no function is rewritten. -/
def compileNoRewriteFuel (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) : Option (Nat × List (Nat × Nat × Exp)) := do
  if !enabled then return (next, code)
  for (loc, arity, body) in code do
    if (← checkExpFuel fuel loc arity body).isSome then failure
  pure (next, code)

end Flapjack.Compiler.Backend.BviTailrec
