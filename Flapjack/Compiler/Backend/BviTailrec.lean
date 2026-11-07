import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.Compiler.Backend.Bvi.Budget
import Flapjack.HolRef

/-! Recursive-call analysis for BVI's tail-recursion optimization. The
type scan and accumulator rewrite are in `Analysis` and `Rewrite`. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- Recognize the source pass's direct, unhandled self-call. -/
@[hol "cakeml/compiler/backend/bvi_tailrecScript.sml" "is_rec_def"]
def isRec (name : Nat) : Exp → Bool
  | .call _ (some dest) _ none => dest == name
  | _ => false

/-- Fuel-bounded traversal of the source `has_rec_sing` predicate. Unlike a
general recursion detector it intentionally examines only the positions that
can be rewritten by this optimization. -/
def hasRecFuel : Nat → Nat → Exp → Option Bool
  | 0, _, _ => none
  | fuel + 1, loc, e => do
      let visit := hasRecFuel fuel loc
      match e with
      | .ifThenElse _ x y =>
          if ← visit x then pure true else visit y
      | .let _ body | .tick body => visit body
      | .op _ xs =>
          if xs.any (isRec loc) then pure true
          else xs.foldlM (fun found x => if found then pure true else visit x) false
      | _ => pure false

/-- Preserve a successful recursion analysis, retrying exhausted traversals
with a structural budget. -/
def hasRecBounded (fuel loc : Nat) (e : Exp) : Option Bool :=
  match hasRecFuel fuel loc e with
  | some result => some result
  | none => hasRecFuel (max fuel (expBudget e + 1)) loc e

/-- Compatibility path that retains a program only when the optimizer is
disabled or every function fails its necessary recursion test. Positive
cases return `none`; `Rewrite` provides the full checked rewrite path. -/
def compileNoRecFuel (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) : Option (Nat × List (Nat × Nat × Exp)) := do
  if !enabled then return (next, code)
  for (loc, _, body) in code do
    if ← hasRecBounded fuel loc body then failure
  pure (next, code)

end Flapjack.Compiler.Backend.BviTailrec
