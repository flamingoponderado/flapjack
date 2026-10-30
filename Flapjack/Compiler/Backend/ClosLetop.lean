import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.ClosLang.Budget

/-! Bounded infrastructure for the closure let-operation cleanup pass. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang

private def varList (xs : List Exp) (arity : Nat) : Bool :=
  xs.length == arity && (xs.zip (List.range arity)).all fun (x, n) =>
    match x with | .var _ m => m == n | _ => false

/-- Replace a let applied directly to its bound variables by the operation,
using the let trace as in the source transformation. -/
def compileFuel : Nat → Exp → Option Exp
  | 0, _ => none
  | fuel + 1, e =>
      let visit := compileFuel fuel
      match e with
      | .var t v => some (.var t v)
      | .ifThenElse t x y z => do pure (.ifThenElse t (← visit x) (← visit y) (← visit z))
      | .let t xs body => do
          let xs ← xs.mapM visit
          let body ← visit body
          match body with
          | .op _ op args => if varList args xs.length then pure (.op t op xs) else pure (.let t xs body)
          | _ => pure (.let t xs body)
      | .raise t x => do pure (.raise t (← visit x))
      | .handle t x y => do pure (.handle t (← visit x) (← visit y))
      | .op t op xs => do pure (.op t op (← xs.mapM visit))
      | .tick t x => do pure (.tick t (← visit x))
      | .call t ticks dest xs => do pure (.call t ticks dest (← xs.mapM visit))
      | .app t loc x xs => do pure (.app t loc (← visit x) (← xs.mapM visit))
      | .fn name loc vs arity body => do pure (.fn name loc vs arity (← visit body))
      | .letrec names loc vs fns body => do
          let fns ← fns.mapM fun (arity, e) => do pure (arity, ← visit e)
          pure (.letrec names loc vs fns (← visit body))

/-- Preserve successful let-operation cleanup and retry exhaustion with a
structural bound. -/
def compileBounded (fuel : Nat) (e : Exp) : Option Exp :=
  match compileFuel fuel e with
  | some result => some result
  | none => compileFuel (max fuel (expBudget e + 1)) e

end Flapjack.Compiler.Backend.ClosLetop
