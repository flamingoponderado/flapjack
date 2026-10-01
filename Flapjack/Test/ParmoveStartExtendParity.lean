import Flapjack.Compiler.Backend.Parmove.StepSem.StartExtend
namespace Flapjack.Test.ParmoveStartExtendParity
open Flapjack.Compiler.Backend.Parmove
private def env : Option Nat → Nat := fun x => match x with
  | none => 99
  | some k => 10*k+7
-- ps_start_pre_1=67
example : sem ([(some 4,some 2),(some 1,some 2),(some 5,some 4)],[],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- ps_start_pre_4=67
example : sem ([(some 4,some 2),(some 1,some 2),(some 5,some 4)],[],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- ps_start_pre_5=47
example : sem ([(some 4,some 2),(some 1,some 2),(some 5,some 4)],[],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- ps_start_post_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- ps_start_post_4=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 4) = 67 := by decide
-- ps_start_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- ps_extend_pre_1=67
example : sem ([(some 4,some 2),(some 3,some 1),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- ps_extend_pre_3=17
example : sem ([(some 4,some 2),(some 3,some 1),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 3) = 17 := by decide
-- ps_extend_pre_5=47
example : sem ([(some 4,some 2),(some 3,some 1),(some 5,some 4)],[(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- ps_extend_post_1=67
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 1),(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 1) = 67 := by decide
-- ps_extend_post_3=17
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 1),(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 3) = 17 := by decide
-- ps_extend_post_5=47
example : sem ([(some 4,some 2),(some 5,some 4)],[(some 3,some 1),(some 1,some 2)],[(some 2,some 3),(some 3,some 6)]) env (some 5) = 47 := by decide
-- ps_bad_pre=37
example : sem ([(some 1,some 2),(some 1,some 3)],[],[]) env (some 1) = 37 := by decide
-- ps_bad_post=27
example : sem ([(some 1,some 3)],[(some 1,some 2)],[]) env (some 1) = 27 := by decide
example : wf ([(some (4:Nat),some 2),(some 1,some 2),(some 5,some 4)], [],
    [(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : wf ([(some (4:Nat),some 2),(some 3,some 1),(some 5,some 4)], [(some 1,some 2)],
    [(some 2,some 3),(some 3,some 6)]) := by simp [wf, windmill, path]
example : ¬ wf ([(some (1:Nat),some 2),(some 1,some 3)], [], ([] : List (Move Nat))) := by
  simp [wf, windmill]
end Flapjack.Test.ParmoveStartExtendParity
