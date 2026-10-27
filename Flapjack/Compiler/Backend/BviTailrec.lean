import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.HolRef

/-! Executable pieces of BVI's tail-recursion optimization. The scan and
accumulator rewrite are not yet ported; the guarded program traversal rejects
every case that might require them. -/
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

/-- Retain a program only when the original optimizer is disabled or every
function fails its necessary recursion test. Positive cases return `none`
until the original type scan and accumulator rewrite have been implemented. -/
def compileNoRecFuel (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) : Option (Nat × List (Nat × Nat × Exp)) := do
  if !enabled then return (next, code)
  for (loc, _, body) in code do
    if ← hasRecFuel fuel loc body then failure
  pure (next, code)

end Flapjack.Compiler.Backend.BviTailrec
