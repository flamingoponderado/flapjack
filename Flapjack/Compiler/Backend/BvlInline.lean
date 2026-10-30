import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.BvlHandle
import Flapjack.Compiler.Backend.BvlToBvi.Budget

/-! Fuel-bounded executable pieces of CakeML's BVL inlining pass. These are
Flapjack infrastructure until the original total definitions and termination
arguments have been ported and reviewed. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl
open BvlToBvi (expBudget listBudget)

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

/-- Preserve successful inlining and retry an exhausted traversal with a
structural budget. -/
def inlineExpBounded (fuel : Nat) (cache : Spt (Nat × Exp)) (e : Exp) : Option Exp :=
  match inlineExpFuel fuel cache e with
  | some result => some result
  | none => inlineExpFuel (max fuel (expBudget e + 1)) cache e

/-- Preserve a successful size check and retry an exhausted traversal. -/
def smallExpBounded (fuel limit : Nat) (e : Exp) : Option Nat :=
  match smallExpFuel fuel limit e with
  | some result => some result
  | none => smallExpFuel (max fuel (expBudget e + 1)) limit e

/-- Preserve a successful recursion check and retry an exhausted traversal. -/
def recursiveBounded (fuel name : Nat) (e : Exp) : Option Bool :=
  match recursiveFuel fuel name e with
  | some result => some result
  | none => recursiveFuel (max fuel (expBudget e + 1)) name e

/-- Inline entries in order and cache small nonrecursive results. -/
def tickInlineAllFuel (fuel limit : Nat) : Spt (Nat × Exp) → List (Nat × Nat × Exp) →
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp))
  | cache, [] => some (cache, [])
  | cache, (name, arity, body) :: rest => do
      let body ← inlineExpBounded fuel cache body
      let size ← smallExpBounded fuel limit body
      let recurs ← if size == 0 then pure false else recursiveBounded fuel name body
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

/-- Retry tick removal with a structural budget if the original budget was
exhausted. -/
def removeTicksBounded (fuel : Nat) (e : Exp) : Option Exp :=
  match removeTicksFuel fuel e with
  | some result => some result
  | none => removeTicksFuel (max fuel (expBudget e + 1)) e

/-- Retry let-operation reduction with a structural budget if needed. -/
def letOpBounded (fuel : Nat) (e : Exp) : Option Exp :=
  match letOpFuel fuel e with
  | some result => some result
  | none => letOpFuel (max fuel (expBudget e + 1)) e

/-- Apply tick inlining, tick removal and let-operation reduction. The
subsequent `bvl_handle` transformation is not included. -/
def compileWithoutHandleFuel (fuel limit : Nat) (prog : List (Nat × Nat × Exp)) :
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← tickInlineAllFuel fuel limit .ln prog
  let prog ← prog.mapM fun (name, arity, body) => do
    let body ← removeTicksBounded fuel body
    pure (name, arity, ← letOpBounded fuel body)
  pure (cache, prog)

/-- Continue through handler processing without its constant-folding
prerequisite; the result is not the full original BVL optimization pass. -/
def compileWithoutConstantsFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (prog : List (Nat × Nat × Exp)) : Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← compileWithoutHandleFuel fuel inlineLimit prog
  let prog ← prog.mapM fun (name, arity, body) => do
    pure (name, arity, ← BvlHandle.compileAnyWithoutConstantsFuel fuel splitSeq cutSize arity body)
  pure (cache, prog)

/-- Execute the BVL inlining and handler pipeline with explicit fuel. -/
def compileProgFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (prog : List (Nat × Nat × Exp)) : Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← compileWithoutHandleFuel fuel inlineLimit prog
  let prog ← prog.mapM fun (name, arity, body) => do
    pure (name, arity, ← BvlHandle.compileAnyFuel fuel splitSeq cutSize arity body)
  pure (cache, prog)

end Flapjack.Compiler.Backend.BvlInline
