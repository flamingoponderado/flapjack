import Flapjack.Compiler.Backend.Parmove.DSteps

namespace Flapjack.Test.ParmoveDStepsParity
open Flapjack.Compiler.Backend.Parmove

example : DStep ([(some (1 : Nat),some 1)],[],[]) ([],[],[]) := DStep.removeSelf _ [] []
example : DStep ([(some (1 : Nat),some 2)],[],[]) ([],[(some 1,some 2)],[]) :=
  DStep.start _ _ [] [] (by decide)
example : DStep ([(some (3 : Nat),some 1)],[(some 1,some 2)],[])
    ([],[(some 3,some 1),(some 1,some 2)],[]) := DStep.extend _ _ _ [] [] [] [] (by simp)
example : DStep ([],[(some (1 : Nat),some 2),(some 3,some 1)],[])
    ([],[(some 3,none)],[(some 1,some 2),(none,some 1)]) :=
  DStep.saveEmit _ _ _ [] [] [] (by simp)
example : DStep ([],[(some (3 : Nat),some 1),(some 1,some 2)],[])
    ([],[(some 1,some 2)],[(some 3,some 1)]) :=
  DStep.emitHead _ _ _ _ [] [] [] (by simp) (by decide)
example : DStep ([],[(some (1 : Nat),some 2)],[]) ([],[],[(some 1,some 2)]) :=
  DStep.emitLast _ _ [] [] (by simp)
example : ¬ (some (1 : Nat) ≠ some 1) := by decide
example : some (1 : Nat) ∈ ([(some 4, some 1)] : List (Move Nat)).map Prod.snd := by decide
example : DStep ([(some (3 : Nat),some 1),(some 4,some 1)],[(some 1,some 2)],[])
    ([(some 4,some 1)],[(some 3,some 1),(some 1,some 2)],[]) :=
  DStep.extend _ _ _ [] [(some 4,some 1)] [] [] (by simp)

end Flapjack.Test.ParmoveDStepsParity
