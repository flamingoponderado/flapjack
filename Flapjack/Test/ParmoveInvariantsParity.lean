import Flapjack.Compiler.Backend.Parmove.Invariants

namespace Flapjack.Test.ParmoveInvariantsParity
open Flapjack.Compiler.Backend.Parmove
/-! Kernel replay of all thirteen original HOL invariant observations. The
last active source may be NONE, while earlier sources and all destinations
must be SOME. Emitted moves are intentionally unconstrained. -/
example : path ([] : List (Nat × Nat)) := by simp [path]
example : path [((1 : Nat), 2)] := by simp [path]
example : path [((1 : Nat), 2), (2, 3), (3, 4)] := by simp [path]
example : ¬ path [((1 : Nat), 2), (3, 4)] := by simp [path]
example : wf (α := Nat) (γ := List (Move Nat)) ([], [], [(none, none)]) := by simp [wf, windmill, path]
example : wf (α := Nat) (γ := List (Move Nat)) ([(some 1, some 2), (some 3, some 2)], [], []) := by
  simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([(some 1, some 2), (some 1, some 3)], [], []) := by
  simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([(none, some 2)], [], []) := by simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([(some 1, none)], [], []) := by simp [wf, windmill, path]
example : wf (α := Nat) (γ := List (Move Nat)) ([], [(some 1, some 2), (some 2, none)], []) := by
  simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([], [(some 1, none), (some 2, some 3)], []) := by
  simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([], [(none, some 2)], []) := by simp [wf, windmill, path]
example : ¬ wf (α := Nat) (γ := List (Move Nat)) ([], [(some 1, some 2), (some 3, some 4)], []) := by
  simp [wf, windmill, path]
-- HOL's ignored emitted carrier is independent of register moves.
example : wf (α := Nat) ([], [], true) := by simp [wf, windmill, path]
example {α β : Type} (pending : List (Move α))
    (h : windmill pending ∧ (∀ m ∈ pending, m.1.isSome = true) ∧
      (∀ m ∈ pending, m.2.isSome = true)) : wf (pending, [], ([] : List β)) :=
  wf_init pending h
end Flapjack.Test.ParmoveInvariantsParity
