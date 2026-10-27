import Flapjack.Compiler.Backend.BviTailrec.Analysis
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs

/-! Fuel-bounded accumulator rewrite for the BVI tail-recursion pass. The
source's total definitions and its correctness proof remain unported. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

private def applyOp (op : AssocOp) (x y : Exp) : Exp := .op (toOp op) [x, y]
private def identity : AssocOp → Exp
  | .plus => .op (.intOp (.const 0)) []
  | .times => .op (.intOp (.const 1)) []
  | .append => .op (.blockOp (.cons 0)) []
  | .noop => .var 1234567890

/-- Rewrite accumulator candidates, preserving the source's evaluation
contexts and the original expressions in non-rewritten conditional branches. -/
def rewriteFuel : Nat → Nat → Nat → AssocOp → Nat → List ValueType → Exp → Option (Bool × Exp)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, loc, next, op, acc, ctx, e => do
      match e with
      | .var n => pure (false, .var n)
      | .force l n => pure (false, .force l n)
      | .ifThenElse cond yes no =>
          let (ctx', _, _, _) ← scanFuel fuel ctx loc cond
          let (ry, y) ← rewriteFuel fuel loc next op acc ctx' yes
          let (rn, n) ← rewriteFuel fuel loc next op acc ctx' no
          let y := if ry then y else applyOp op (.var acc) yes
          let n := if rn then n else applyOp op (.var acc) no
          pure (ry || rn, .ifThenElse cond y n)
      | .let xs body =>
          let scans ← scanListFuel fuel ctx loc xs
          let types := scans.map fun (_, ty, _, _) => ty
          let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
          let (r, body) ← rewriteFuel fuel loc next op (acc + xs.length) (types ++ last) body
          pure (r, .let xs body)
      | .tick x =>
          let (r, x) ← rewriteFuel fuel loc next op acc ctx x
          pure (r, .tick x)
      | .op actual xs =>
          if fromOp actual == op && op != .noop then
            match ← checkOpFuel fuel ctx op loc xs with
            | some (.op _ [value, .call ticks (some _) args handler]) =>
                pure (true, .call ticks (some next) (args ++ [applyOp op (.var acc) value]) handler)
            | _ => pure (false, applyOp op (.var acc) e)
          else pure (false, applyOp op (.var acc) e)
      | _ => pure (false, applyOp op (.var acc) e)

/-- Apply the source decision and construct wrapper and worker bodies. -/
def compileExpFuel (fuel loc next arity : Nat) (e : Exp) : Option (Option (Exp × Exp)) := do
  match ← checkExpFuel fuel loc arity e with
  | none => pure none
  | some op =>
      let (_, worker) ← rewriteFuel fuel loc next op arity (List.replicate arity .any) e
      let wrapper := .let ((List.range arity).map .var ++ [identity op]) worker
      pure (some (wrapper, worker))

/-- Transform functions in original order and allocate worker labels in the
source namespace stride. -/
def compileEachFuel (fuel : Nat) : Nat → List (Nat × Nat × Exp) →
    Option (Nat × List (Nat × Nat × Exp))
  | next, [] => some (next, [])
  | next, (loc, arity, body) :: rest => do
      match ← compileExpFuel fuel loc next arity body with
      | none =>
          let (next, rest) ← compileEachFuel fuel next rest
          pure (next, (loc, arity, body) :: rest)
      | some (wrapper, worker) =>
          let (next', rest) ← compileEachFuel fuel (next + Flapjack.bvlToBviNamespaces) rest
          pure (next', (loc, arity, wrapper) :: (next, arity + 1, worker) :: rest)

/-- Apply BVI tail-recursion elimination when enabled. -/
def compileProgFuel (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) : Option (Nat × List (Nat × Nat × Exp)) :=
  if enabled then compileEachFuel fuel next code else some (next, code)

end Flapjack.Compiler.Backend.BviTailrec
