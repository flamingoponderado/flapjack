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

mutual
/-- The original size of an expression list; ticks contribute no node. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_aux_def"]
def getSizeAuxHOL : List Exp → Nat
  | [] => 0
  | e :: es => getSizeExpHOL e + getSizeAuxHOL es
termination_by es => sizeOf es

/-- Single-expression helper for the source size traversal. -/
def getSizeExpHOL : Exp → Nat
  | .var .. => 1
  | .tick _ e => getSizeExpHOL e
  | .ifThenElse _ x y z => 1 + getSizeExpHOL x + getSizeExpHOL y + getSizeExpHOL z
  | .let _ xs body => 1 + getSizeAuxHOL xs + getSizeExpHOL body
  | .raise _ e | .fn _ _ _ _ e => 1 + getSizeExpHOL e
  | .handle _ x y => 1 + getSizeExpHOL x + getSizeExpHOL y
  | .op _ _ xs | .call _ _ _ xs => 1 + getSizeAuxHOL xs
  | .letrec _ _ _ fs body => 1 + getSizeFunsHOL fs + getSizeExpHOL body
  | .app _ _ e xs => 1 + getSizeExpHOL e + getSizeAuxHOL xs
termination_by e => sizeOf e

/-- Helper for the source traversal of recursive-function bodies. -/
def getSizeFunsHOL : List (Nat × Exp) → Nat
  | [] => 0
  | (_, e) :: es => getSizeExpHOL e + getSizeFunsHOL es
termination_by es => sizeOf es
end

/-- The original size of one closure expression. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_def"]
def getSizeHOL (e : Exp) : Nat := getSizeAuxHOL [e]

mutual
/-- The source's budgeted list traversal, stopping as soon as the budget
reaches zero. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_aux_def"]
def getSizeScAuxHOL (n : Nat) : List Exp → Nat
  | [] => n
  | [e] => getSizeScExpHOL n e
  | e :: next :: es =>
    if n = 0 then n else
      let remaining := getSizeScExpHOL n e
      if remaining = 0 then remaining else getSizeScAuxHOL remaining (next :: es)
termination_by es => sizeOf es

/-- Single-expression helper for the source's budgeted traversal. -/
def getSizeScExpHOL (n : Nat) : Exp → Nat
  | .var .. => n - 1
  | .tick _ e => getSizeScExpHOL n e
  | .ifThenElse _ x y z =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n x
      if n = 0 then 0 else
        let n := getSizeScExpHOL n y
        if n = 0 then 0 else getSizeScExpHOL n z
  | .let _ xs body =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScAuxHOL n xs
      if n = 0 then 0 else getSizeScExpHOL n body
  | .raise _ e | .fn _ _ _ _ e =>
    let n := n - 1
    if n = 0 then 0 else getSizeScExpHOL n e
  | .handle _ x y =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n x
      if n = 0 then 0 else getSizeScExpHOL n y
  | .op _ _ xs | .call _ _ _ xs =>
    let n := n - 1
    if n = 0 then 0 else getSizeScAuxHOL n xs
  | .letrec _ _ _ fs body =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScFunsHOL n fs
      if n = 0 then 0 else getSizeScExpHOL n body
  | .app _ _ e xs =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n e
      if n = 0 then 0 else getSizeScAuxHOL n xs
termination_by e => sizeOf e

/-- Budgeted traversal of the bodies in a recursive function group. -/
def getSizeScFunsHOL (n : Nat) : List (Nat × Exp) → Nat
  | [] => n
  | (_, e) :: es =>
    let remaining := getSizeScExpHOL n e
    if remaining = 0 then 0 else getSizeScFunsHOL remaining es
termination_by es => sizeOf es
end

/-- Return the source expression size when it fits within the limit. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_def"]
def getSizeScHOL (limit : Nat) (e : Exp) : Option Nat :=
  let remaining := getSizeScAuxHOL (limit + 1) [e]
  if remaining = 0 then none else some (limit + 1 - remaining)

/-- Construct the source closure approximation using its short-circuit size
check. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "clos_approx_def"]
def closApproxHOL (maxSize loc arity : Nat) (body : Exp) : ValApprox :=
  match getSizeScHOL maxSize body with
  | none => .closNoInline loc arity
  | some size => .clos loc arity body size

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

/-- The executed size analysis uses the total source traversal. The fuel
argument is retained for the surrounding checked optimizer interface. -/
def sizeBounded (_fuel : Nat) (e : Exp) : Option Nat := some (getSizeHOL e)

/-- The executed closure check uses the total source traversal. The fuel
argument is retained for the surrounding checked optimizer interface. -/
def containsClosuresBounded (_fuel : Nat) (e : Exp) : Option Bool :=
  some (containsClosuresHOL [e])

/-- The checked optimizer uses the source closure-approximation definition. -/
def closApproxFuel (_fuel maxSize loc arity : Nat) (body : Exp) : Option ValApprox :=
  some (closApproxHOL maxSize loc arity body)

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
