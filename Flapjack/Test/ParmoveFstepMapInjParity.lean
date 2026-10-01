import Flapjack.Compiler.Backend.Parmove.FstepMapInj

namespace Flapjack.Test.ParmoveFstepMapInjParity
open Compiler.Backend.Parmove

-- This Nat-to-Bool map collapses 0 and 2 globally, while being injective on
-- the endpoints 0/1 used by the original fixtures. NONE is retained exactly.
private def rename : Option Nat → Option Bool
  | none => none
  | some n => some (n == 1)

private theorem rename_none (x : Option Nat) : rename x = none ↔ x = none := by
  cases x <;> simp [rename]

private theorem rename_inj (x y : Option Nat)
    (hx : x = none ∨ x = some 0 ∨ x = some 1)
    (hy : y = none ∨ y = some 0 ∨ y = some 1)
    (equal : rename x = rename y) : x = y := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals simp [rename] at equal ⊢

private def states : List (State Nat) :=
  [([], [], []), ([(some 0,some 0)], [], []),
   ([(some 0,some 1)], [], []),
   ([(some 0,some 1)], [(some 1,some 0)], []),
   ([], [(some 1,some 0)], []),
   ([], [(some 1,some 0),(some 0,some 1)], []),
   ([], [(some 1,some 0),(some 0,some 0)], []),
   ([(none,some 0)], [], [(some 1,none)])]

example : rename (some 0) = rename (some 2) := by decide +kernel

-- Whole output trees on both sides of the original eight observations.
private def expected : List (State Bool) :=
  [([], [], []), ([], [], []), ([], [(some false,some true)], []),
   ([], [(some false,some true),(some true,some false)], []),
   ([], [], [(some true,some false)]),
   ([], [(some false,none)], [(some true,some false),(none,some true)]),
   ([], [(some false,some false)], [(some true,some false)]),
   ([], [(none,some false)], [(some true,none)])]

example : states.map (fun s => fstep (mapState rename s)) = expected := by
  rfl
example : states.map (fun s => mapState rename (fstep s)) = expected := by
  rfl

example {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : Option α → Option β) (s : State α) (valid : injOnState f s) :
    fstep (mapState f s) = mapState f (fstep s) := fstepMapInj f s valid

-- Apply the actual theorem with non-vacuous local support premises.
example : ∀ s ∈ states, fstep (mapState rename s) = mapState rename (fstep s) := by
  intro s member
  apply fstepMapInj
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, rename_none⟩
    intro x y ⟨hx, hy, equal⟩
    apply rename_inj x y ?_ ?_ equal
  all_goals cases x <;> cases y <;>
    simp_all [stateToList, or_left_comm, or_comm]

end Flapjack.Test.ParmoveFstepMapInjParity
