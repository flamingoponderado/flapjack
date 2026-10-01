import Flapjack.Compiler.Backend.Parmove.Invariants.Path

namespace Flapjack.Test.ParmovePathParity
open Flapjack.Compiler.Backend.Parmove
/-! Kernel replay of ten direct original HOL SNOC path/windmill observations.
Changed final destination and broken prefixes fail; repeated sources remain legal.
No semantic-invariance or full scheduler-correctness claim is made. -/
example : path ([] ++ [((1 : Nat), 99)]) := by simp [path]
example : path [((3 : Nat), 1), (1, 99)] := by simp [path]
example : path [((4 : Nat), 3), (3, 1), (1, 99)] := by simp [path]
example : path [((1 : Nat), 2), (2, 3), (3, 99)] := by simp [path]
example : ¬ path [((3 : Nat), 1), (2, 99)] := by simp [path]
example : ¬ path [((4 : Nat), 2), (3, 1), (1, 99)] := by simp [path]
example : windmill [((1 : Nat), 2)] := by simp [windmill]
example : windmill [((1 : Nat), 2), (3, 2)] := by simp [windmill]
example : ¬ windmill [((1 : Nat), 2), (1, 3)] := by simp [windmill]
example : windmill [((1 : Nat), 2), (3, 2), (4, 2)] := by simp [windmill]

example {α : Type} (before : List (α × α)) (last replacement : α × α)
    (h : path (before ++ [last]) ∧ last.1 = replacement.1) :
    path (before ++ [replacement]) := path_change_start before replacement last h
example {α : Type} (move : α × α) (moves : List (α × α))
    (h : move.1 ∉ moves.map Prod.fst ∧ windmill moves) : windmill (move :: moves) :=
  (windmill_cons move moves).mpr h
end Flapjack.Test.ParmovePathParity
