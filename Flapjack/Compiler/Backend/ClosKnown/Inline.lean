import Flapjack.Compiler.Backend.ClosKnown.Config
import Flapjack.Compiler.Backend.ClosCall

/-! Bounded infrastructure for the known-closure inlining decision. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- Compute the source size metric; ticks contribute no node. -/
def sizeFuel : Nat → Exp → Option Nat
  | 0, _ => none
  | fuel + 1, e => do
      let visit := sizeFuel fuel
      let sum := fun xs => xs.foldlM (fun n x => do pure (n + (← visit x))) 0
      match e with
      | .var _ _ => pure 1
      | .tick _ x => visit x
      | .ifThenElse _ x y z => pure (1 + (← visit x) + (← visit y) + (← visit z))
      | .let _ xs body => pure (1 + (← sum xs) + (← visit body))
      | .raise _ x | .fn _ _ _ _ x => pure (1 + (← visit x))
      | .handle _ x y => pure (1 + (← visit x) + (← visit y))
      | .op _ _ xs | .call _ _ _ xs => pure (1 + (← sum xs))
      | .letrec _ _ _ fs body => pure (1 + (← sum (fs.map Prod.snd)) + (← visit body))
      | .app _ _ x xs => pure (1 + (← visit x) + (← sum xs))

/-- Detect closure-producing expressions in source traversal order. -/
def containsClosuresFuel : Nat → Exp → Option Bool
  | 0, _ => none
  | fuel + 1, e => do
      let visit := containsClosuresFuel fuel
      let any := fun xs => xs.foldlM (fun b x => if b then pure true else visit x) false
      match e with
      | .fn _ _ _ _ _ | .letrec _ _ _ _ _ => pure true
      | .var _ _ => pure false
      | .ifThenElse _ x y z => any [x, y, z]
      | .let _ xs body => any (xs ++ [body])
      | .raise _ x | .tick _ x => visit x
      | .handle _ x y => any [x, y]
      | .op _ _ xs | .call _ _ _ xs => any xs
      | .app _ _ x xs => any (x :: xs)

/-- Construct the original closure approximation from its size bound. -/
def closApproxFuel (fuel maxSize loc arity : Nat) (body : Exp) : Option ValApprox := do
  let size ← sizeFuel fuel body
  pure (if size ≤ maxSize then .clos loc arity body size else .closNoInline loc arity)

/-- Apply the original inlining decision with explicit traversal fuel. -/
def decideInlineFuel (fuel : Nat) (c : Config) (approx : ValApprox) (loc : Option Nat)
    (arity : Nat) : Option InliningDecision := do
  if loc.isSome then return .nothing
  match approx with
  | .closNoInline target n => pure (if arity == n then .annotate target else .nothing)
  | .clos target n body size =>
      if arity != n then return .nothing
      if size < c.inlineFactor * (1 + arity) then
        if !(← containsClosuresFuel fuel body) then
          if ← ClosCall.closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) then
            return .letInline body
      pure (.annotate target)
  | _ => pure .nothing

end Flapjack.Compiler.Backend.ClosKnown
