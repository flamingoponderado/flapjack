import Flapjack.Compiler.Backend.Parmove.PmovFinal
namespace Flapjack.Test.ParmoveFinalParity
open Flapjack.Compiler.Backend.Parmove
-- pv_final_terminal=([],[],[(SOME 7,NONE)])
example : pmov (([],[],[(some 7,none)]) : State Nat) = ([],[],[(some 7,none)]) := by simp [pmov.eq_def]
-- pv_final_self=([],[],[])
example : pmov (([(some 1,some 1)],[],[]) : State Nat) = ([],[],[]) := by simp [pmov.eq_def, fstep]
-- pv_final_chain=([],[],[(SOME 2,SOME 3); (SOME 1,SOME 2)])
example : pmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat) = ([],[],[(some 2,some 3), (some 1,some 2)]) := by simp [pmov.eq_def, fstep, splitSource]
-- pv_final_cycle=([],[],[(SOME 1,NONE); (SOME 2,SOME 1); (NONE,SOME 2)])
example : pmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat) = ([],[],[(some 1,none), (some 2,some 1), (none,some 2)]) := by simp [pmov.eq_def, fstep, splitSource, frontLast]
-- pv_final_scratch=([],[],[(NONE,SOME 2); (SOME 1,NONE)])
example : pmov (([(none,some 2),(some 1,none)],[],[]) : State Nat) = ([],[],[(none,some 2), (some 1,none)]) := by simp [pmov.eq_def, fstep, splitSource, frontLast]
-- pv_final_duplicate=([],[],[(SOME 1,SOME 3); (SOME 1,SOME 2)])
example : pmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat) = ([],[],[(some 1,some 3), (some 1,some 2)]) := by simp [pmov.eq_def, fstep, splitSource]
-- pv_final_active=([],[],[(SOME 2,NONE); (SOME 1,SOME 2); (NONE,SOME 1)])
example : pmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat) = ([],[],[(some 2,none), (some 1,some 2), (none,some 1)]) := by simp [pmov.eq_def, fstep, splitSource, frontLast]
example {α : Type} [DecidableEq α] (state : State α) :
    ∃ emitted, pmov state = ([], [], emitted) := pmov_final state
end Flapjack.Test.ParmoveFinalParity
