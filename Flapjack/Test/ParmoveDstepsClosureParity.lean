import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Test.ParmoveFinalParity

namespace Flapjack.Test.ParmoveDstepsClosureParity
open Flapjack.Compiler.Backend.Parmove

/-! Kernel replay of the exact closure on the seven original scheduler outputs
in parmove_final_probe.out, including terminal history and unconstrained inputs. -/

example : DSteps (([],[],[(some 7,none)]) : State Nat) ([],[],[(some 7,none)]) := by
  have closure := pmovDsteps (([],[],[(some 7,none)]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([(some 1,some 1)],[],[]) : State Nat) ([],[],[]) := by
  have closure := pmovDsteps (([(some 1,some 1)],[],[]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat) ([],[],[(some 2,some 3), (some 1,some 2)]) := by
  have closure := pmovDsteps (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat) ([],[],[(some 1,none), (some 2,some 1), (none,some 2)]) := by
  have closure := pmovDsteps (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([(none,some 2),(some 1,none)],[],[]) : State Nat) ([],[],[(none,some 2), (some 1,none)]) := by
  have closure := pmovDsteps (([(none,some 2),(some 1,none)],[],[]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat) ([],[],[(some 1,some 3), (some 1,some 2)]) := by
  have closure := pmovDsteps (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example : DSteps (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat) ([],[],[(some 2,none), (some 1,some 2), (none,some 1)]) := by
  have closure := pmovDsteps (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)
  simpa [pmov.eq_def, fstep, splitSource, frontLast] using closure

example {α : Type} [DecidableEq α] (state : State α) : DSteps state (pmov state) :=
  pmovDsteps state

end Flapjack.Test.ParmoveDstepsClosureParity
