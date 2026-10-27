import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.BvlHandle

/-! Fuel-bounded executable pieces of CakeML's BVL inlining pass. These are
Flapjack infrastructure until the original total definitions and termination
arguments have been ported and reviewed. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

private def mkTick : Nat → Exp → Exp
  | 0, e => e
  | n + 1, e => .tick (mkTick n e)

/-- Inline calls using the already-processed function cache. -/
def inlineExpFuel : Nat → Spt (Nat × Exp) → Exp → Option Exp
  | 0, _, _ => none
  | fuel + 1, cache, e =>
      let visit := inlineExpFuel fuel cache
      match e with
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← visit y))
      | .raise x => do pure (.raise (← visit x))
      | .handle x y => do pure (.handle (← visit x) (← visit y))
      | .tick x => do pure (.tick (← visit x))
      | .force m n => some (.force m n)
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .call ticks target xs => do
          let xs ← xs.mapM visit
          match target with
          | some name =>
              match sptLookup name cache with
              | some (_, body) => pure (.let xs (mkTick (ticks + 1) body))
              | none => pure (.call ticks target xs)
          | none => pure (.call ticks target xs)

mutual
  /-- Remaining original size budget, with ticks and variables free. -/
  def smallExpFuel : Nat → Nat → Exp → Option Nat
    | 0, _, _ => none
    | fuel + 1, n, e =>
      let child := smallExpFuel fuel
      let children := smallListFuel fuel
      match e with
      | .var _ | .force _ _ => some n
      | .tick x => child n x
      | .ifThenElse x y z => do
          let n := n - 1
          if n == 0 then return 0
          let n ← child n x
          if n == 0 then return 0
          let n ← child n y
          if n == 0 then return 0
          child n z
      | .let xs y => do
          let n := n - 1
          if n == 0 then return 0
          let n ← children n xs
          if n == 0 then return 0
          child n y
      | .raise x => do
          let n := n - 1
          if n == 0 then return 0
          child n x
      | .handle x y => do
          let n := n - 1
          if n == 0 then return 0
          let n ← child n x
          if n == 0 then return 0
          child n y
      | .op _ xs | .call _ _ xs => do
          let n := n - 1
          if n == 0 then return 0
          children n xs

  /-- Remaining size budget after traversing a list in source order. -/
  def smallListFuel : Nat → Nat → List Exp → Option Nat
    | _, n, [] => some n
    | 0, _, _ :: _ => none
    | fuel + 1, n, x :: xs => do
        if n == 0 then return n
        let n ← smallExpFuel fuel n x
        if n == 0 then return n
        smallListFuel fuel n xs
end

/-- Detect a direct or nested call to a named function. -/
def recursiveFuel : Nat → Nat → Exp → Option Bool
  | 0, _, _ => none
  | fuel + 1, name, e => do
      let visit := recursiveFuel fuel name
      let any := fun xs => xs.foldlM (fun found x => if found then pure true else visit x) false
      match e with
      | .var _ | .force _ _ => pure false
      | .tick x | .raise x => visit x
      | .ifThenElse x y z => any [x, y, z]
      | .let xs y => any (xs ++ [y])
      | .handle x y => any [x, y]
      | .op _ xs => any xs
      | .call _ target xs => if target == some name then pure true else any xs

/-- Inline entries in order and cache small nonrecursive results. -/
def tickInlineAllFuel (fuel limit : Nat) : Spt (Nat × Exp) → List (Nat × Nat × Exp) →
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp))
  | cache, [] => some (cache, [])
  | cache, (name, arity, body) :: rest => do
      let body ← inlineExpFuel fuel cache body
      let size ← smallExpFuel fuel limit body
      let recurs ← if size == 0 then pure false else recursiveFuel fuel name body
      let cache := if size != 0 && !recurs then sptInsert name (arity, body) cache else cache
      let (cache, rest) ← tickInlineAllFuel fuel limit cache rest
      pure (cache, (name, arity, body) :: rest)

/-- Remove tick accounting, as in the executable compiler. -/
def removeTicksFuel : Nat → Exp → Option Exp
  | 0, _ => none
  | fuel + 1, e =>
      let visit := removeTicksFuel fuel
      match e with
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← visit y))
      | .raise x => do pure (.raise (← visit x))
      | .handle x y => do pure (.handle (← visit x) (← visit y))
      | .tick x => visit x
      | .force m n => some (.force m n)
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .call _ dest xs => do pure (.call 0 dest (← xs.mapM visit))

private def varList (xs : List Exp) (arity : Nat) : Bool :=
  xs.length == arity && (xs.zip (List.range arity)).all fun (x, n) =>
    match x with | .var m => m == n | _ => false

/-- Eliminate a let whose body applies an operation to its bound variables. -/
def letOpFuel : Nat → Exp → Option Exp
  | 0, _ => none
  | fuel + 1, e =>
      let visit := letOpFuel fuel
      match e with
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do
          let xs ← xs.mapM visit
          let y ← visit y
          match y with
          | .op op args => if varList args xs.length then pure (.op op xs) else pure (.let xs y)
          | _ => pure (.let xs y)
      | .raise x => do pure (.raise (← visit x))
      | .handle x y => do pure (.handle (← visit x) (← visit y))
      | .tick x => do pure (.tick (← visit x))
      | .force m n => some (.force m n)
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .call ticks dest xs => do pure (.call ticks dest (← xs.mapM visit))

/-- Apply tick inlining, tick removal and let-operation reduction. The
subsequent `bvl_handle` transformation is not included. -/
def compileWithoutHandleFuel (fuel limit : Nat) (prog : List (Nat × Nat × Exp)) :
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← tickInlineAllFuel fuel limit .ln prog
  let prog ← prog.mapM fun (name, arity, body) => do
    let body ← removeTicksFuel fuel body
    pure (name, arity, ← letOpFuel fuel body)
  pure (cache, prog)

/-- Continue through handler processing without its constant-folding
prerequisite; the result is not the full original BVL optimization pass. -/
def compileWithoutConstantsFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (prog : List (Nat × Nat × Exp)) : Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← compileWithoutHandleFuel fuel inlineLimit prog
  let prog ← prog.mapM fun (name, arity, body) => do
    pure (name, arity, ← BvlHandle.compileAnyWithoutConstantsFuel fuel splitSeq cutSize arity body)
  pure (cache, prog)

end Flapjack.Compiler.Backend.BvlInline
