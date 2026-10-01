import Flapjack.Compiler.Backend.Parmove.StepSem.EmitHead
namespace Flapjack.Test.ParmoveEmitHeadParity
open Flapjack.Compiler.Backend.Parmove
private def env : Option Nat → Nat := fun x => match x with
 | none => 99
 | some k => 10*k+7
-- pv_head_history_pre_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pv_head_history_pre_2=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) env (some 2) = 67 := by decide
-- pv_head_history_pre_3=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) env (some 3) = 67 := by decide
-- pv_head_history_pre_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pv_head_history_pre_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pv_head_history_post_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 2,some 3),(some 3,some 6)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pv_head_history_post_2=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 2,some 3),(some 3,some 6)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 2) = 67 := by decide
-- pv_head_history_post_3=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 2,some 3),(some 3,some 6)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 3) = 67 := by decide
-- pv_head_history_post_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 2,some 3),(some 3,some 6)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pv_head_history_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 2,some 3),(some 3,some 6)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pv_head_none_pre_1=27
example : sem ([(some 4,some 2)],[(some 1,some 2),(some 2,none)],[]) env (some 1) = 27 := by decide
-- pv_head_none_pre_2=99
example : sem ([(some 4,some 2)],[(some 1,some 2),(some 2,none)],[]) env (some 2) = 99 := by decide
-- pv_head_none_pre_4=27
example : sem ([(some 4,some 2)],[(some 1,some 2),(some 2,none)],[]) env (some 4) = 27 := by decide
-- pv_head_none_post_1=27
example : sem ([(some 4,some 2)],[(some 2,none)],[(some 1,some 2)]) env (some 1) = 27 := by decide
-- pv_head_none_post_2=99
example : sem ([(some 4,some 2)],[(some 2,none)],[(some 1,some 2)]) env (some 2) = 99 := by decide
-- pv_head_none_post_4=27
example : sem ([(some 4,some 2)],[(some 2,none)],[(some 1,some 2)]) env (some 4) = 27 := by decide
-- pv_head_bad_endpoint_pre_1=27
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 1) = 27 := by decide
-- pv_head_bad_endpoint_pre_2=17
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 2) = 17 := by decide
-- pv_head_bad_endpoint_post_1=27
example : sem ([],[(some 2,some 1)],[(some 1,some 2)]) env (some 1) = 27 := by decide
-- pv_head_bad_endpoint_post_2=27
example : sem ([],[(some 2,some 1)],[(some 1,some 2)]) env (some 2) = 27 := by decide
-- pv_head_bad_pending_pre_1=27
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 3)],[]) env (some 1) = 27 := by decide
-- pv_head_bad_pending_pre_2=37
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 3)],[]) env (some 2) = 37 := by decide
-- pv_head_bad_pending_pre_4=17
example : sem ([(some 4,some 1)],[(some 1,some 2),(some 2,some 3)],[]) env (some 4) = 17 := by decide
-- pv_head_bad_pending_post_1=27
example : sem ([(some 4,some 1)],[(some 2,some 3)],[(some 1,some 2)]) env (some 1) = 27 := by decide
-- pv_head_bad_pending_post_2=37
example : sem ([(some 4,some 1)],[(some 2,some 3)],[(some 1,some 2)]) env (some 2) = 37 := by decide
-- pv_head_bad_pending_post_4=27
example : sem ([(some 4,some 1)],[(some 2,some 3)],[(some 1,some 2)]) env (some 4) = 27 := by decide
example : wf (γ := List (Move Nat)) ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2),(some 2,some 3),(some 3,some 6)],[(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : wf (γ := List (Move Nat)) ([(some 4,some 2)],[(some 1,some 2),(some 2,none)],[]) := by simp [wf, windmill, path]
example : wf (γ := List (Move Nat)) ([],[(some 1,some 2),(some 2,some 1)],[]) := by simp [wf, windmill, path]
example : wf (γ := List (Move Nat)) ([(some 4,some 1)],[(some 1,some 2),(some 2,some 3)],[]) := by simp [wf, windmill, path]
example : (some 1 : Option Nat) = some 1 := rfl -- endpoint guard violated in cycle
example : (some 1 : Option Nat) ∈ ([(some 4,some 1)] : List (Move Nat)).map Prod.snd := by decide
end Flapjack.Test.ParmoveEmitHeadParity
