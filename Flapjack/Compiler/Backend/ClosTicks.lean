import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Bounded infrastructure for the closure tick-removal pass. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang

/-- Remove ticks while retaining all non-tick trace annotations. -/
def removeFuel : Nat → Exp → Option Exp
  | 0, _ => none
  | fuel + 1, e =>
      let visit := removeFuel fuel
      match e with
      | .var t v => some (.var t v)
      | .ifThenElse t x y z => do pure (.ifThenElse t (← visit x) (← visit y) (← visit z))
      | .let t xs body => do pure (.let t (← xs.mapM visit) (← visit body))
      | .raise t x => do pure (.raise t (← visit x))
      | .handle t x y => do pure (.handle t (← visit x) (← visit y))
      | .op t op xs => do pure (.op t op (← xs.mapM visit))
      | .tick _ x => visit x
      | .call t _ dest xs => do pure (.call t 0 dest (← xs.mapM visit))
      | .app t loc x xs => do pure (.app t loc (← visit x) (← xs.mapM visit))
      | .fn name loc vs arity body => do pure (.fn name loc vs arity (← visit body))
      | .letrec names loc vs fns body => do
          let fns ← fns.mapM fun (arity, e) => do pure (arity, ← visit e)
          pure (.letrec names loc vs fns (← visit body))

end Flapjack.Compiler.Backend.ClosTicks
