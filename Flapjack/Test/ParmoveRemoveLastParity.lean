import Flapjack.Compiler.Backend.Parmove.StepSem.RemoveSelfEmitLast
namespace Flapjack.Test.ParmoveRemoveLastParity
open Flapjack.Compiler.Backend.Parmove
private def env : Option Nat → Nat := fun x => match x with
 | none => 99
 | some k => 10*k+7
-- pr_self_pre_1=17
example : sem ([(some 4,some 2),(some 1,some 1),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 17 := by decide
-- pr_self_pre_4=67
example : sem ([(some 4,some 2),(some 1,some 1),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pr_self_pre_5=47
example : sem ([(some 4,some 2),(some 1,some 1),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pr_self_post_1=17
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 17 := by decide
-- pr_self_post_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pr_self_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pr_last_pre_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pr_last_pre_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pr_last_pre_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pr_last_post_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- pr_last_post_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- pr_last_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[],[(some 1,some 2),(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- pr_bad_self_pre=17
example : sem ([(some 1,some 3),(some 1,some 1)],[],[]) env (some 1) = 17 := by decide
-- pr_bad_self_post=37
example : sem ([(some 1,some 3)],[],[]) env (some 1) = 37 := by decide
-- pr_bad_read_pre=17
example : sem ([(some 3,some 1)],[(some 1,some 2)],[]) env (some 3) = 17 := by decide
-- pr_bad_read_post=27
example : sem ([(some 3,some 1)],[],[(some 1,some 2)]) env (some 3) = 27 := by decide
example : wf ([(some (4:Nat),some 2),(some 1,some 1),(some 5,some 4)],[(some 3,some 2)],
    [(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : wf ([(some (4:Nat),some 2),(some 5,some 4)],[(some 1,some 2)],
    [(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : (some (1:Nat)) ∉ [(some 4,some 2),(some 5,some 4)].map Prod.snd := by decide
example : ¬ wf ([(some (1:Nat),some 3),(some 1,some 1)],[],([] : List (Move Nat))) := by
  simp [wf, windmill]
example : wf ([(some (3:Nat),some 1)],[(some 1,some 2)],([] : List (Move Nat))) := by
  simp [wf, windmill, path]
example : (some (1:Nat)) ∈ [(some 3,some 1)].map Prod.snd := by decide
end Flapjack.Test.ParmoveRemoveLastParity
