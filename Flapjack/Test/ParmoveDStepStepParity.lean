import Flapjack.Compiler.Backend.Parmove.DStepStep

namespace Flapjack.Test.ParmoveDStepStepParity
open Flapjack.Compiler.Backend.Parmove

-- pv_ds_wf_0=T
example : wf (γ := List (Move Nat)) ([(some (1 : Nat),some 1)],[],[]) := by simp [wf, windmill, path]
example : Steps ([(some (1 : Nat),some 1)],[],[]) ([],[],[]) :=
  dstep_step _ _ (DStep.removeSelf _ [] []) (by simp [wf, windmill, path])

-- pv_ds_wf_1=T
example : wf (γ := List (Move Nat)) ([(some (1 : Nat),some 2)],[],[]) := by simp [wf, windmill, path]
example : Steps ([(some (1 : Nat),some 2)],[],[]) ([],[(some 1,some 2)],[]) :=
  dstep_step _ _ (DStep.start _ _ [] [] (by decide)) (by simp [wf, windmill, path])

-- pv_ds_wf_2=T
example : wf (γ := List (Move Nat)) ([(some (3 : Nat),some 1)],[(some 1,some 2)],[]) := by simp [wf, windmill, path]
example : Steps ([(some (3 : Nat),some 1)],[(some 1,some 2)],[]) ([],[(some 3,some 1),(some 1,some 2)],[]) :=
  dstep_step _ _ (DStep.extend _ _ _ [] [] [] [] (by simp)) (by simp [wf, windmill, path])

-- pv_ds_wf_3=T
example : wf (γ := List (Move Nat)) ( [],[(some (1 : Nat),some 2),(some 2,some 1)],[]) := by simp [wf, windmill, path]
example : Steps ( [],[(some (1 : Nat),some 2),(some 2,some 1)],[]) ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) :=
  dstep_step _ _ (DStep.saveEmit _ _ _ [] [] [] (by simp)) (by simp [wf, windmill, path])

-- pv_ds_wf_4=T
example : wf (γ := List (Move Nat)) ( [],[(some (3 : Nat),some 1),(some 1,some 2)],[]) := by simp [wf, windmill, path]
example : Steps ( [],[(some (3 : Nat),some 1),(some 1,some 2)],[]) ([],[(some 1,some 2)],[(some 3,some 1)]) :=
  dstep_step _ _ (DStep.emitHead _ _ _ _ [] [] [] (by simp) (by decide)) (by simp [wf, windmill, path])

-- pv_ds_wf_5=T
example : wf (γ := List (Move Nat)) ( [],[(some (1 : Nat),some 2)],[]) := by simp [wf, windmill, path]
example : Steps ( [],[(some (1 : Nat),some 2)],[]) ([],[],[(some 1,some 2)]) :=
  dstep_step _ _ (DStep.emitLast _ _ [] [] (by simp)) (by simp [wf, windmill, path])

private def env : Option Nat → Nat
  | none => 99
  | some k => 10*k+7
-- pv_ds_cycle_0_0=27
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 1) = 27 := by decide
-- pv_ds_cycle_0_1=17
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 2) = 17 := by decide
-- pv_ds_cycle_0_2=99
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (none) = 99 := by decide
-- pv_ds_cycle_1_0=27
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 1) = 27 := by decide
-- pv_ds_cycle_1_1=17
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 2) = 17 := by decide
-- pv_ds_cycle_1_2=17
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (none) = 17 := by decide
-- pv_ds_cycle_2_0=27
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (some 1) = 27 := by decide
-- pv_ds_cycle_2_1=17
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (some 2) = 17 := by decide
-- pv_ds_cycle_2_2=17
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (none) = 17 := by decide

end Flapjack.Test.ParmoveDStepStepParity
