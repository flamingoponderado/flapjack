import Flapjack.Compiler.Backend.Parmove.StepSem.Save
namespace Flapjack.Test.ParmoveSaveParity
open Flapjack.Compiler.Backend.Parmove
private def env : Option Nat → Nat := fun x => match x with
 | none => 99
 | some k => 10*k+7
-- pv_save_history_pre_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pv_save_history_pre_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pv_save_history_pre_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pv_save_history_pre_temp=99
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (none) = 99 := by decide
-- pv_save_history_post_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,none)],[(none,some 2),(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pv_save_history_post_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,none)],[(none,some 2),(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pv_save_history_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,none)],[(none,some 2),(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pv_save_history_post_temp=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,none)],[(none,some 2),(some 2,some 3),(some 3,some 6)]) env (none) = 67 := by decide
-- pv_save_cycle_pre_1=27
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 1)],[]) env (some 1) = 27 := by decide
-- pv_save_cycle_pre_2=17
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 1)],[]) env (some 2) = 17 := by decide
-- pv_save_cycle_pre_4=17
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 1)],[]) env (some 4) = 17 := by decide
-- pv_save_cycle_post_1=27
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 1) = 27 := by decide
-- pv_save_cycle_post_2=17
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 2) = 17 := by decide
-- pv_save_cycle_post_4=17
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 4) = 17 := by decide
-- pv_save_none_source_pre_1=99
example : sem ([(some 4,some 2)],[(some 1,none)],[]) env (some 1) = 99 := by decide
-- pv_save_none_source_pre_4=27
example : sem ([(some 4,some 2)],[(some 1,none)],[]) env (some 4) = 27 := by decide
-- pv_save_none_source_post_1=99
example : sem ([(some 4,some 2)],[(some 1,none)],[(none,none)]) env (some 1) = 99 := by decide
-- pv_save_none_source_post_4=27
example : sem ([(some 4,some 2)],[(some 1,none)],[(none,none)]) env (some 4) = 27 := by decide
-- pv_save_bad_pending_pre_4=99
example : sem ([(some 4,none)],[(some 1,some 2)],[]) env (some 4) = 99 := by decide
-- pv_save_bad_pending_post_4=27
example : sem ([(some 4,none)],[(some 1,none)],[(none,some 2)]) env (some 4) = 27 := by decide
example : wf (γ := List (Move Nat)) ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : wf (γ := List (Move Nat)) ([(some 4,some 1)],[(some 1,some 2),(some 2,some 1)],[]) := by simp [wf, windmill, path]
example : wf (γ := List (Move Nat)) ([(some 4,some 2)],[(some 1,none)],[]) := by simp [wf, windmill, path]
example : ¬ wf (γ := List (Move Nat)) ([(some 4,none)],[(some 1,some 2)],[]) := by simp [wf, windmill, path]
end Flapjack.Test.ParmoveSaveParity
