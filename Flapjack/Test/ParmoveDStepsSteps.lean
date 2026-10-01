import Flapjack.Compiler.Backend.Parmove.DStepsSteps

namespace Flapjack.Test.ParmoveDStepsSteps
open Flapjack.Compiler.Backend.Parmove

-- Reflexive closure preserves a terminal state with emitted history.
example : Steps ([], [], [(some (1 : Nat), some 2)])
    ([], [], [(some 1, some 2)]) :=
  dsteps_steps _ _ .refl (by simp [wf, windmill, path])

-- Start and emitLast require preservation at the intermediate active state.
example : Steps ([(some (1 : Nat), some 2)], [], [])
    ([], [], [(some 1, some 2)]) := by
  apply dsteps_steps
  · exact (Relation.ReflTransGen.single
      (DStep.start (some 1) (some 2) [] [] (by decide))).tail
      (DStep.emitLast (some 1) (some 2) [] [] (by simp))
  · simp [wf, windmill, path]

-- The cycle transition expands to two primitive steps before the final emit.
example : Steps ([], [(some (1 : Nat), some 2), (some 2, some 1)], [])
    ([], [], [(some 2, none), (some 1, some 2), (none, some 1)]) := by
  apply dsteps_steps
  · exact (Relation.ReflTransGen.single
      (DStep.saveEmit (some 1) (some 2) (some 2) [] [] [] (by simp))).tail
      (DStep.emitLast (some 2) none [] [(some 1, some 2), (none, some 1)] (by simp))
  · simp [wf, windmill, path]

end Flapjack.Test.ParmoveDStepsSteps
