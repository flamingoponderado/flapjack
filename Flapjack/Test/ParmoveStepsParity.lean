import Flapjack.Compiler.Backend.Parmove.Steps
namespace Flapjack.Test.ParmoveStepsParity
open Flapjack.Compiler.Backend.Parmove
example : Step ([(some (1 : Nat),some 1)],[],[]) ([],[],[]) := Step.removeSelf _ [] [] [] []
example : Step ([(some (1 : Nat),some 2)],[],[]) ([],[(some 1,some 2)],[]) := Step.start _ _ [] [] []
example : Step ([(some (3 : Nat),some 1)],[(some 1,some 2)],[])
    ([],[(some 3,some 1),(some 1,some 2)],[]) := Step.extend _ _ _ [] [] [] []
example : Step ([],[(some (1 : Nat),some 2)],[])
    ([],[(some 1,none)],[(none,some 2)]) := Step.save _ _ [] [] []
example : Step ([],[(some (3 : Nat),some 1),(some 1,some 2)],[])
    ([],[(some 1,some 2)],[(some 3,some 1)]) :=
  Step.emitHead _ _ _ _ [] [] [] (by simp) (by decide)
example : Step ([],[(some (1 : Nat),some 2)],[]) ([],[],[(some 1,some 2)]) :=
  Step.emitLast _ _ [] [] (by simp)
example {α : Type} (state : State α) : Steps state state := .refl
example : Steps ([(some (1 : Nat),some 2)],[],[]) ([],[],[(some 1,some 2)]) :=
  (Relation.ReflTransGen.single (Step.start _ _ [] [] [])).trans
    (Relation.ReflTransGen.single (Step.emitLast _ _ [] [] (by simp)))
end Flapjack.Test.ParmoveStepsParity
