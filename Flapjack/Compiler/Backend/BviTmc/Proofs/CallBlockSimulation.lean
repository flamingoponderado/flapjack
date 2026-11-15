module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockWorkerSimulation

@[expose] public section

/-! The ordinary-body induction hypothesis for call-block simulations. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockSimulation
open BviTmc BviSem BvlSem CallBlockAuxFrame CallBlockAuxSimulation

/-- Flapjack infrastructure: the smaller-clock ordinary function-body
simulation used by recursive call-block leaves. -/
def OrdinaryBodyIH {C F : Type} (loc : Nat) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ ticks indices body body' args args' bodyResult bodyFinal,
    wfVars env1.length indices → ticks + 1 ≤ source.clock →
    findCode (some loc) (indices.map (fun n => holEl n env1)) source.code = some (args, body) →
    findCode (some loc) (indices.map (fun n => holEl n env2)) target.code = some (args', body') →
    envRel false f args args' → noMutcons body →
    (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
      rewriteWrapperSource loc workerLoc args.length body = some body') →
    evaluate [body] args (decClock (ticks + 1) source) = (bodyResult, bodyFinal) →
    bodyResult ≠ .err (.abort .typeError) →
    ListSimulation.Core [body'] args' f (decClock (ticks + 1) target) bodyResult bodyFinal

end Flapjack.Compiler.Backend.BviTmc.CallBlockSimulation
