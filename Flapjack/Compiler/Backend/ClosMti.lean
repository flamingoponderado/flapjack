import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.ClosLang.Budget
import Flapjack.HolRef

/-! Multi-argument closure introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- Collect nested unannotated function arguments up to the configured limit. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_args_def"]
def collectArgs (maxApp numArgs : Nat) : Exp → Nat × Exp
  | .fn t none none more body =>
      if numArgs + more ≤ maxApp then collectArgs maxApp (numArgs + more) body
      else (numArgs, .fn t none none more body)
  | e => (numArgs, e)

/-- Collect nested unannotated applications in their original argument order. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_apps_def"]
def collectApps (maxApp : Nat) (args : List Exp) : Exp → List Exp × Exp
  | .app t none body more =>
      if args.length + more.length ≤ maxApp then collectApps maxApp (args ++ more) body
      else (args, .app t none body more)
  | e => (args, e)

/-- Fuel-bounded Flapjack traversal of multi-argument introduction. Failure
indicates exhausted fuel; this helper is not the total HOL `intro_multi`. -/
def introMultiFuel : Nat → Nat → Exp → Option Exp
  | 0, _, _ => none
  | fuel + 1, maxApp, e =>
      let visit := introMultiFuel fuel maxApp
      match e with
      | .var t n => some (.var t n)
      | .ifThenElse t x y z => do pure (.ifThenElse t (← visit x) (← visit y) (← visit z))
      | .let t xs body => do pure (.let t (← xs.mapM visit) (← visit body))
      | .raise t body => do pure (.raise t (← visit body))
      | .handle t body handler => do pure (.handle t (← visit body) (← visit handler))
      | .tick t body => do pure (.tick t (← visit body))
      | .call t ticks loc xs => do pure (.call t ticks loc (← xs.mapM visit))
      | .app t none body xs => do
          let (args, head) := collectApps maxApp xs body
          pure (.app t none (← visit head) (← args.mapM visit))
      | .app t (some loc) body xs => do pure (.app t (some loc) (← visit body) (← xs.mapM visit))
      | .fn t none none arity body => do
          let (arity, body) := collectArgs maxApp arity body
          pure (.fn t none none arity (← visit body))
      | .fn t loc fvs arity body => do pure (.fn t loc fvs arity (← visit body))
      | .letrec t none none funs body => do
          let funs ← funs.mapM fun (arity, e) => do
            let (arity, e) := collectArgs maxApp arity e
            pure (arity, ← visit e)
          pure (.letrec t none none funs (← visit body))
      | .letrec t loc fvs funs body => do pure (.letrec t loc fvs funs (← visit body))
      | .op t op xs => do pure (.op t op (← xs.mapM visit))

/-- Preserve successful multi-argument introduction and retry exhaustion with
a structural traversal budget. -/
def introMultiBounded (fuel maxApp : Nat) (e : Exp) : Option Exp :=
  match introMultiFuel fuel maxApp e with
  | some result => some result
  | none => introMultiFuel (max fuel (expBudget e + 1)) maxApp e

/-- Apply the checked traversal to every expression when enabled. -/
def compileFuel (fuel : Nat) (enabled : Bool) (maxApp : Nat) (es : List Exp) : Option (List Exp) :=
  if enabled then es.mapM (introMultiBounded fuel maxApp) else some es

end Flapjack.Compiler.Backend.ClosMti
