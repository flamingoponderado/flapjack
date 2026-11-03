import Flapjack.Compiler.Backend.ClosKnown.Config
import Flapjack.Compiler.Backend.ClosCall
import Flapjack.Compiler.Backend.ClosLang.Budget

/-! Bounded infrastructure for the known-closure inlining decision. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

mutual
/-- The original list-valued closure-presence predicate. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "contains_closures_def"]
def containsClosuresHOL : List Exp → Bool
  | [] => false
  | e :: es => containsClosuresExpHOL e || containsClosuresHOL es
termination_by es => sizeOf es

/-- Single-expression helper for the source list traversal. -/
def containsClosuresExpHOL : Exp → Bool
  | .var .. => false
  | .fn .. | .letrec .. => true
  | .ifThenElse _ x y z => containsClosuresExpHOL x || containsClosuresExpHOL y || containsClosuresExpHOL z
  | .let _ xs body => containsClosuresHOL xs || containsClosuresExpHOL body
  | .raise _ body | .tick _ body => containsClosuresExpHOL body
  | .handle _ x y => containsClosuresExpHOL x || containsClosuresExpHOL y
  | .op _ _ xs | .call _ _ _ xs => containsClosuresHOL xs
  | .app _ _ fn xs => containsClosuresExpHOL fn || containsClosuresHOL xs
termination_by e => sizeOf e
end

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

/-- Preserve successful size checks and retry exhaustion with a structural bound. -/
def sizeBounded (fuel : Nat) (e : Exp) : Option Nat :=
  match sizeFuel fuel e with
  | some result => some result
  | none => sizeFuel (max fuel (expBudget e + 1)) e

/-- The executed closure check uses the total source traversal. The fuel
argument is retained for the surrounding checked optimizer interface. -/
def containsClosuresBounded (_fuel : Nat) (e : Exp) : Option Bool :=
  some (containsClosuresHOL [e])

/-- Construct the original closure approximation from its size bound. -/
def closApproxFuel (fuel maxSize loc arity : Nat) (body : Exp) : Option ValApprox := do
  let size ← sizeBounded fuel body
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
        if !(← containsClosuresBounded fuel body) then
          if ← ClosCall.closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) then
            return .letInline body
      pure (.annotate target)
  | _ => pure .nothing

end Flapjack.Compiler.Backend.ClosKnown
