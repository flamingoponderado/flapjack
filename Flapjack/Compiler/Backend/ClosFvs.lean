import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.ClosLang.Budget

/-! Bounded infrastructure for the closure free-variable cleanup pass. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang

/-- Replace out-of-scope variables with the source type-error expression. -/
def removeFuel : Nat → Nat → Exp → Option Exp
  | 0, _, _ => none
  | fuel + 1, bound, e =>
      let visit := removeFuel fuel bound
      match e with
      | .var t v => some (if v < bound then .var t v else .op t (.memOp .el) [])
      | .ifThenElse t x y z => do pure (.ifThenElse t (← visit x) (← visit y) (← visit z))
      | .let t xs body => do
          let xs ← xs.mapM visit
          pure (.let t xs (← removeFuel fuel (bound + xs.length) body))
      | .raise t x => do pure (.raise t (← visit x))
      | .handle t x y => do pure (.handle t (← visit x) (← removeFuel fuel (bound + 1) y))
      | .op t op xs => do pure (.op t op (← xs.mapM visit))
      | .tick t x => do pure (.tick t (← visit x))
      | .call t ticks dest xs => do pure (.call t ticks dest (← xs.mapM visit))
      | .app t loc x xs => do pure (.app t loc (← visit x) (← xs.mapM visit))
      | .fn name loc vs arity body => do
          let captured := vs.map List.length |>.getD bound
          pure (.fn name loc vs arity (← removeFuel fuel (arity + captured) body))
      | .letrec names loc vs fns body => do
          let captured := vs.map List.length |>.getD bound
          let fs ← fns.mapM fun (arity, e) => do
            pure (arity, ← removeFuel fuel (arity + fns.length + captured) e)
          pure (.letrec names loc vs fs (← removeFuel fuel (fns.length + bound) body))

/-- Preserve successful cleanup and retry exhaustion with a structural bound. -/
def removeBounded (fuel bound : Nat) (e : Exp) : Option Exp :=
  match removeFuel fuel bound e with
  | some result => some result
  | none => removeFuel (max fuel (expBudget e + 1)) bound e

end Flapjack.Compiler.Backend.ClosFvs
