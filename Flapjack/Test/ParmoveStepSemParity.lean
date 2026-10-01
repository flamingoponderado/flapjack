import Flapjack.Compiler.Backend.Parmove.StepSem
namespace Flapjack.Test.ParmoveStepSemParity
open Flapjack.Compiler.Backend.Parmove
example (env : Option Nat → Nat) : eqenv (sem ([(some 1,some 1)],[],[]) env) (sem ([],[],[]) env) :=
  step_sem ([(some 1,some 1)],[],[]) ([],[],[]) (Step.removeSelf (some 1) [] [] [] []) (by simp [wf, windmill, path]) env
example (env : Option Nat → Nat) : eqenv (sem ([(some 1,some 2)],[],[]) env) (sem ([],[(some 1,some 2)],[]) env) :=
  step_sem ([(some 1,some 2)],[],[]) ([],[(some 1,some 2)],[]) (Step.start (some 1) (some 2) [] [] []) (by simp [wf, windmill, path]) env
example (env : Option Nat → Nat) : eqenv (sem ([(some 2,some 1)],[(some 1,some 3)],[]) env) (sem ([],[(some 2,some 1),(some 1,some 3)],[]) env) :=
  step_sem ([(some 2,some 1)],[(some 1,some 3)],[]) ([],[(some 2,some 1),(some 1,some 3)],[]) (Step.extend (some 1) (some 2) (some 3) [] [] [] []) (by simp [wf, windmill, path]) env
example (env : Option Nat → Nat) : eqenv (sem ([],[(some 1,some 2)],[]) env) (sem ([],[(some 1,none)],[(none,some 2)]) env) :=
  step_sem ([],[(some 1,some 2)],[]) ([],[(some 1,none)],[(none,some 2)]) (Step.save (some 1) (some 2) [] [] []) (by simp [wf, windmill, path]) env
example (env : Option Nat → Nat) : eqenv (sem ([],[(some 1,some 2),(some 2,some 3)],[]) env) (sem ([],[(some 2,some 3)],[(some 1,some 2)]) env) :=
  step_sem ([],[(some 1,some 2),(some 2,some 3)],[]) ([],[(some 2,some 3)],[(some 1,some 2)]) (Step.emitHead (some 2) (some 1) (some 3) (some 2) [] [] [] (by simp) (by decide)) (by simp [wf, windmill, path]) env
example (env : Option Nat → Nat) : eqenv (sem ([],[(some 1,some 2)],[]) env) (sem ([],[],[(some 1,some 2)]) env) :=
  step_sem ([],[(some 1,some 2)],[]) ([],[],[(some 1,some 2)]) (Step.emitLast (some 1) (some 2) [] [] (by simp)) (by simp [wf, windmill, path]) env
end Flapjack.Test.ParmoveStepSemParity
