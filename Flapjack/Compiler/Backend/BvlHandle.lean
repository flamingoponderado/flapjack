import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.DbVars

/-! Fuel-bounded executable infrastructure for the BVL handler pass. The
total HOL definitions, termination proofs and constant-folding prerequisite
have not yet been ported. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl DbVars

/-- Whether an expression can raise, before handler simplification. -/
def canRaiseFuel : Nat → Exp → Option Bool
  | 0, _ => none
  | fuel + 1, e => do
      let visit := canRaiseFuel fuel
      let any := fun xs => xs.foldlM (fun b x => if b then pure true else visit x) false
      match e with
      | .var _ => pure false
      | .ifThenElse x y z => any [x, y, z]
      | .let xs y => any (y :: xs)
      | .handle _ y => visit y
      | .raise _ | .force _ _ | .call _ _ _ => pure true
      | .op (.thunkOp .forceThunk) _ => pure true
      | .op _ xs => any xs
      | .tick x => visit x

/-- Shift free variables above a binder depth, including force operands. -/
def adjustVarsFuel : Nat → Nat → Nat → Exp → Option Exp
  | 0, _, _, _ => none
  | fuel + 1, depth, shift, e =>
      let visit := adjustVarsFuel fuel depth shift
      let adj := fun n => if n < depth then n else n + shift
      match e with
      | .var n => some (.var (adj n))
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← adjustVarsFuel fuel (depth + xs.length) shift y))
      | .handle x y => do pure (.handle (← visit x) (← adjustVarsFuel fuel (depth + 1) shift y))
      | .raise x => do pure (.raise (← visit x))
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .tick x => do pure (.tick (← visit x))
      | .force m n => some (.force m (adj n))
      | .call t dest xs => do pure (.call t dest (← xs.mapM visit))

mutual
  /-- Simplify handlers while preserving explicit failure on fuel exhaustion. -/
  def simplifyFuel : Nat → Exp → Option Exp
    | 0, _ => none
    | fuel + 1, e =>
      let visit := simplifyFuel fuel
      match e with
      | .handle x y => makeHandleFuel fuel x y 0
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← visit y))
      | .raise x => do pure (.raise (← visit x))
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .tick x => do pure (.tick (← visit x))
      | .force m n => some (.force m n)
      | .call t dest xs => do pure (.call t dest (← xs.mapM visit))

  /-- Move a handler through safe let bindings and one-raising-branch ifs. -/
  def makeHandleFuel : Nat → Exp → Exp → Nat → Option Exp
    | 0, _, _, _ => none
    | fuel + 1, x, handler, depth => do
      match x with
      | .raise r =>
          if !(← canRaiseFuel fuel r) then
            let handler ← simplifyFuel fuel handler
            return .let [r] (← adjustVarsFuel fuel 1 depth handler)
      | .let xs body =>
          let raises ← xs.foldlM (fun b e => if b then pure true else canRaiseFuel fuel e) false
          if !raises then
            return .let (← xs.mapM (simplifyFuel fuel)) (← makeHandleFuel fuel body handler (depth + xs.length))
      | .ifThenElse c yes no =>
          let cr ← canRaiseFuel fuel c
          if !cr then
            let yr ← canRaiseFuel fuel yes
            let nr ← canRaiseFuel fuel no
            if yr && !nr then
              return .ifThenElse (← simplifyFuel fuel c) (← makeHandleFuel fuel yes handler depth) (← simplifyFuel fuel no)
            if !yr && nr then
              return .ifThenElse (← simplifyFuel fuel c) (← simplifyFuel fuel yes) (← makeHandleFuel fuel no handler depth)
      | _ => pure ()
      let x ← simplifyFuel fuel x
      let handler ← simplifyFuel fuel handler
      pure (.handle x (← adjustVarsFuel fuel 1 depth handler))
end

private def zero : Exp := .op (.intOp (.const 0)) []

/-- Construct the source pass's environment-packing lets. -/
def letLet (envSize : Nat) (live : NumSet) (body : Exp) : Exp :=
  let retained := (List.range envSize).filter fun n => (sptLookup n live).isSome
  let mapping := retained.zip (List.range retained.length)
  let long := (List.range envSize).map fun n =>
    match mapping.lookup n with | some k => .var k | none => zero
  .let (retained.map .var) (if long.isEmpty then body else .let long body)

private def optionalLetLet (e : Exp) (env : Nat) (live : DbVarSet) (size limit : Nat)
    (noRaise : Bool) : Exp × DbVarSet × Nat × Bool :=
  if size < limit then (e, live, size, noRaise)
  else (.let [] (letLet env (dbToSet live) e), varsFlatten live, 0, noRaise)

mutual
  /-- Compile a single simplified expression with live-variable accounting. -/
  def compileFuel : Nat → Nat → Nat → Exp → Option (Exp × DbVarSet × Nat × Bool)
    | 0, _, _, _ => none
    | fuel + 1, limit, env, e => do
      let visit := compileFuel fuel limit env
      let children := compileListFuel fuel limit env
      match e with
      | .var v => if v < env then pure (.var v, .var v, 1, true) else pure (zero, .empty, 1, true)
      | .force m v => if v < env then pure (.force m v, .var v, 1, false) else pure (zero, .empty, 1, true)
      | .ifThenElse x y z =>
          let (x, lx, sx, nx) ← visit x
          let (y, ly, sy, ny) ← visit y
          let (z, lz, sz, nz) ← visit z
          pure (optionalLetLet (.ifThenElse x y z) env (mkUnion lx (mkUnion ly lz)) (sx + sy + sz + 1) limit (nx && ny && nz))
      | .let [] body => visit body
      | .let xs body =>
          let (ys, lx, sx, nx) ← children xs
          let (body, ly, sy, ny) ← compileFuel fuel limit (env + xs.length) body
          pure (optionalLetLet (.let ys body) env (mkUnion lx (.shift xs.length ly)) (sx + sy + 1) limit (nx && ny))
      | .handle x y =>
          let (x, lx, sx, nx) ← visit x
          if nx then return (x, lx, sx, true)
          let (y, ly, sy, ny) ← compileFuel fuel limit (env + 1) y
          pure (.handle (letLet env (dbToSet lx) x) y, mkUnion lx (.shift 1 ly), sy, ny)
      | .raise x =>
          let (x, live, size, _) ← visit x
          pure (optionalLetLet (.raise x) env live (size + 1) limit false)
      | .op op xs =>
          let (xs, live, size, nr) ← children xs
          match op with
          | .thunkOp .forceThunk => pure (.op op xs, live, size + 1, false)
          | _ => pure (optionalLetLet (.op op xs) env live (size + 1) limit nr)
      | .tick x =>
          let (x, live, size, nr) ← visit x
          pure (.tick x, live, size, nr)
      | .call ticks dest xs =>
          let (xs, live, size, _) ← children xs
          pure (optionalLetLet (.call ticks dest xs) env live (size + 1) limit false)

  /-- Compile expression lists, retaining the source's union order. -/
  def compileListFuel : Nat → Nat → Nat → List Exp → Option (List Exp × DbVarSet × Nat × Bool)
    | _, _, _, [] => some ([], .empty, 0, true)
    | 0, _, _, _ :: _ => none
    | fuel + 1, limit, env, x :: xs => do
      let (x, lx, sx, nx) ← compileFuel fuel limit env x
      let (xs, ly, sy, ny) ← compileListFuel fuel limit env xs
      pure (x :: xs, mkUnion lx ly, sx + sy, nx && ny)
end

/-- Run handler simplification and compilation on an expression. The original
first runs `bvl_const`; this explicitly restricted entry point omits it. -/
def compileExpWithoutConstantsFuel (fuel limit arity : Nat) (e : Exp) : Option Exp := do
  let e ← simplifyFuel fuel e
  let (e, _, _, _) ← compileFuel fuel limit arity e
  pure e

/-- Split a sequence at the source pass's exact syntactic boundary. -/
def compileSeqsWithoutConstantsFuel : Nat → Nat → Exp → Option Exp → Option Exp
  | 0, _, _, _ => none
  | fuel + 1, limit, .let [x, y] (.var 1), acc => do
      let rest ← compileSeqsWithoutConstantsFuel fuel limit y acc
      compileSeqsWithoutConstantsFuel fuel limit x (some rest)
  | fuel + 1, limit, e, acc => do
      let e ← compileExpWithoutConstantsFuel fuel limit 0 e
      match acc with
      | none => pure e
      | some rest => pure (.let [e] (.let [] (.let [] rest)))

/-- The handler stage with the constant-folding prerequisite omitted. -/
def compileAnyWithoutConstantsFuel (fuel : Nat) (splitSeq : Bool) (limit arity : Nat)
    (e : Exp) : Option Exp :=
  if arity == 0 && splitSeq then compileSeqsWithoutConstantsFuel fuel limit e none
  else compileExpWithoutConstantsFuel fuel limit arity e

end Flapjack.Compiler.Backend.BvlHandle
