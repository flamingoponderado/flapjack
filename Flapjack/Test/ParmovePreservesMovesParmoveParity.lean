import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Parmove

namespace Flapjack.Test.ParmovePreservesMovesParmoveParity
open Flapjack.Compiler.Backend.Parmove

private def shared : List (Nat × Nat) := [(1, 2), (3, 2)]
private def cycle : List (Nat × Nat) := [(1, 2), (2, 1)]

example : some 3 ∈ (parmove shared).map Prod.fst :=
  parmovePreservesMoves shared 3 2
    ⟨by simp [windmill, shared], by decide +kernel, by decide +kernel⟩
example : some 1 ∈ (parmove cycle).map Prod.fst :=
  parmovePreservesMoves cycle 1 2
    ⟨by simp [windmill, cycle], by decide +kernel, by decide +kernel⟩
example : some false ∈ (parmove [(false, true)]).map Prod.fst :=
  parmovePreservesMoves [(false, true)] false true
    ⟨by simp [windmill], by decide +kernel, by decide +kernel⟩
example : parmove shared = [(some 1, some 2), (some 3, some 2)] := by
  decide +kernel
example : parmove [(4, 4)] = ([] : List (Move Nat)) := by
  decide +kernel
example : parmove ([] : List (Nat × Nat)) = [] := by
  decide +kernel

#print axioms parmovePreservesMoves
end Flapjack.Test.ParmovePreservesMovesParmoveParity
