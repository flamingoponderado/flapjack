import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Pmov

namespace Flapjack.Test.ParmovePreservesMovesPmovParity
open Flapjack.Compiler.Backend.Parmove

private def terminal : State Nat := ([], [], [(none, some 7)])
private def pending : State Nat := ([(some 1, some 2), (some 3, some 2)], [], [])

example : none ∈ (stateToList (pmov terminal)).map Prod.fst :=
  pmovPreservesMoves none (some 7) terminal
    ⟨by simp [terminal, wf, windmill, path],
      by simp [terminal, stateToList], by decide +kernel⟩

example : some 3 ∈ (stateToList (pmov pending)).map Prod.fst :=
  pmovPreservesMoves (some 3) (some 2) pending
    ⟨by simp [pending, wf, windmill, path],
      by simp [pending, stateToList], by decide +kernel⟩

example : pmov pending = ([], [], [(some 3, some 2), (some 1, some 2)]) := by
  decide +kernel

#print axioms pmovPreservesMoves
end Flapjack.Test.ParmovePreservesMovesPmovParity
