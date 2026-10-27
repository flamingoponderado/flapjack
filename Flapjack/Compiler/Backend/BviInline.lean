import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.Misc.Sptree
import Flapjack.HolRef

/-! BVI wrapper inlining and tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

/-- Repeat the BVI tick constructor. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "bvi_mk_tick_def"]
def mkTick : Nat → Exp → Exp
  | 0, e => e
  | n + 1, e => .tick (mkTick n e)

private def isVars (xs : List Exp) (indices : List Nat) : Bool :=
  xs.length == indices.length && (xs.zip indices).all fun (e, n) =>
    match e with | .var k => k == n | _ => false

/-- Check the original worker-wrapper shape using exact variable indices. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "canonical_wrapper_def"]
def canonicalWrapper (name arity : Nat) : Exp → Bool
  | .letCall rets _ worker args (.op (.blockOp (.cons _)) values) =>
      worker != name && isVars args (List.range arity) && isVars values (List.range rets).reverse
  | _ => false

/-- Flapjack's bounded traversal of the BVI inliner. The total HOL definition
and its termination argument remain to be ported. -/
def inlineExpFuel : Nat → Spt (Nat × Exp) → Exp → Option Exp
  | 0, _, _ => none
  | fuel + 1, cache, e =>
      let visit := inlineExpFuel fuel cache
      match e with
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← visit y))
      | .raise x => do pure (.raise (← visit x))
      | .tick x => do pure (.tick (← visit x))
      | .call ticks target xs handler => do
          let xs ← xs.mapM visit
          match handler with
          | some h => pure (.call ticks target xs (some (← visit h)))
          | none =>
              match target with
              | none => pure (.call ticks none xs none)
              | some name =>
                  match sptLookup name cache with
                  | some (arity, body) =>
                      if xs.length = arity then pure (.let xs (mkTick (ticks + 1) body))
                      else pure (.call ticks (some name) xs none)
                  | none => pure (.call ticks (some name) xs none)
      | .force loc n => some (.force loc n)
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .letCall rets ticks target xs y => do pure (.letCall rets ticks target (← xs.mapM visit) (← visit y))
      | .return xs => do pure (.return (← xs.mapM visit))

/-- Flapjack's bounded traversal of the source tick-removal pass. -/
def removeTicksFuel : Nat → Exp → Option Exp
  | 0, _ => none
  | fuel + 1, e =>
      let visit := removeTicksFuel fuel
      match e with
      | .var n => some (.var n)
      | .ifThenElse x y z => do pure (.ifThenElse (← visit x) (← visit y) (← visit z))
      | .let xs y => do pure (.let (← xs.mapM visit) (← visit y))
      | .raise x => do pure (.raise (← visit x))
      | .tick x => visit x
      | .call _ target xs handler => do
          pure (.call 0 target (← xs.mapM visit) (← handler.mapM visit))
      | .force loc n => some (.force loc n)
      | .op op xs => do pure (.op op (← xs.mapM visit))
      | .letCall rets _ target xs y => do pure (.letCall rets 0 target (← xs.mapM visit) (← visit y))
      | .return xs => do pure (.return (← xs.mapM visit))

/-- Inline program entries in source order, threading the exact sparse cache. -/
def inlineAllFuel (fuel : Nat) : Spt (Nat × Exp) → List (Nat × Nat × Exp) →
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp))
  | cache, [] => some (cache, [])
  | cache, (name, arity, body) :: rest => do
      let body ← inlineExpFuel fuel cache body
      let cache := if canonicalWrapper name arity body then sptInsert name (arity, body) cache else cache
      let (cache, rest) ← inlineAllFuel fuel cache rest
      pure (cache, (name, arity, body) :: rest)

/-- Apply the bounded inliner and tick-removal traversals to a whole program. -/
def compileProgFuel (fuel : Nat) (prog : List (Nat × Nat × Exp)) :
    Option (Spt (Nat × Exp) × List (Nat × Nat × Exp)) := do
  let (cache, prog) ← inlineAllFuel fuel .ln prog
  let prog ← prog.mapM fun (name, arity, body) => do
    pure (name, arity, ← removeTicksFuel fuel body)
  pure (cache, prog)

end Flapjack.Compiler.Backend.BviInline
