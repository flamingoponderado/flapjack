import Flapjack.Compiler.Backend.BviTailrec.Analysis
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs

/-! Accumulator rewrite for the BVI tail-recursion pass. `Proofs.Total` proves
sufficient traversal bounds; HOL correspondence and correctness remain open. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- The neutral element for each accumulator operator. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "id_from_op_def"]
def identity : AssocOp → Exp
  | .plus => .op (.intOp (.const 0)) []
  | .times => .op (.intOp (.const 1)) []
  | .append => .op (.blockOp (.cons 0)) []
  | .noop => .var 1234567890

/-- Extract the arguments and metadata of a direct call. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "args_from_def"]
def argsFrom : Exp → Option (Nat × Nat × List Exp × Option Exp)
  | .call ticks (some dest) args handler => some (ticks, dest, args, handler)
  | _ => none

/-- Construct the accumulator worker call from extracted call data. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "push_call_def"]
def pushCall (next : Nat) (op : AssocOp) (acc : Nat) (value : Exp) :
    Option (Nat × Nat × List Exp × Option Exp) → Exp
  | some (ticks, _, args, handler) => .call ticks (some next) (args ++ [applyOp op (.var acc) value]) handler
  | none => .var 1234567890

/-- Introduce the accumulator identity after the original arguments. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "let_wrap_def"]
def letWrap (arity : Nat) (identity body : Exp) : Exp :=
  .let ((List.range arity).map .var ++ [identity]) body

/-- Construct the auxiliary worker call used by the source pass. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "mk_aux_call_def"]
def mkAuxCall (loc arity : Nat) (identity : Exp) : Exp :=
  .call 0 (some loc) (identity :: (List.range arity).map .var) none

/-- Rewrite accumulator candidates, preserving the source's evaluation
contexts and the original expressions in non-rewritten conditional branches. -/
def rewriteFuel : Nat → Nat → Nat → AssocOp → Nat → List ValueType → Exp → Option (Bool × Exp)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, loc, next, op, acc, ctx, e => do
      match e with
      | .var n => pure (false, .var n)
      | .force l n => pure (false, .force l n)
      | .ifThenElse cond yes no =>
          let (ctx', _, _, _) ← scanBounded fuel ctx loc cond
          let (ry, y) ← rewriteFuel fuel loc next op acc ctx' yes
          let (rn, n) ← rewriteFuel fuel loc next op acc ctx' no
          let y := if ry then y else applyOp op (.var acc) yes
          let n := if rn then n else applyOp op (.var acc) no
          pure (ry || rn, .ifThenElse cond y n)
      | .let xs body =>
          let scans ← scanListBounded fuel ctx loc xs
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

/-- Preserve a successful rewrite and retry exhausted traversals with a
structural budget. The inner `none` means no rewrite is applicable. -/
def compileExpBounded (fuel loc next arity : Nat) (e : Exp) : Option (Option (Exp × Exp)) :=
  match compileExpFuel fuel loc next arity e with
  | some result => some result
  | none => compileExpFuel (max fuel (expBudget e + 1)) loc next arity e

/-- Transform functions in original order and allocate worker labels in the
source namespace stride. -/
def compileEachFuel (fuel : Nat) : Nat → List (Nat × Nat × Exp) →
    Option (Nat × List (Nat × Nat × Exp))
  | next, [] => some (next, [])
  | next, (loc, arity, body) :: rest => do
      match ← compileExpBounded fuel loc next arity body with
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
