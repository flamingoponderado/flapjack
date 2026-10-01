import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.FirstIndex

/-! Same-input kernel replay of original predicate and both first-index observations. -/
namespace Flapjack.Test.ParmoveFirstIndexParity
open Flapjack.Compiler.Backend.Parmove Flapjack.Misc
noncomputable local instance {α : Type} : DecidableEq α := Classical.typeDecidableEq α

example : let moves : List (Option Nat × Option Nat) := [];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,none,none) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,some 1)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,none,none) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 0,none) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(none,some 1)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,none,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(none,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 0,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(none,some 1),(some 2,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 1,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 2,none),(none,some 1)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 0,some 1) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,some 1),(none,some 2),(some 3,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 2,some 1) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(none,some 0),(none,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 1,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,some 1),(none,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 1,some 1) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,none),(some 1,none),(none,some 2)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 0,some 2) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(none,some 0),(none,some 1),(some 2,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 2,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Nat × Option Nat) := [(some 0,some 1),(some 2,some 3),(some 4,none),(none,some 5)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (false,some 2,some 3) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Bool × Option (Nat)) := [(none,some 7),(some true,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 1,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example : let moves : List (Option Bool × Option (Nat → Nat)) := [(none,some Nat.succ),(some true,none)];
    (notUseTempBeforeAssign moves, findIndex none (moves.map Prod.snd) 0,
      findIndex none (moves.map Prod.fst) 0) = (true,some 1,some 0) := by
  simp [findIndex, notUseTempBeforeAssign]

example {destination source : Type} (moves : List (Option destination × Option source)) :
    notUseTempBeforeAssign moves = true ↔
      ∀ i, findIndex none (moves.map Prod.snd) 0 = some i →
        ∃ j, findIndex none (moves.map Prod.fst) 0 = some j ∧ j < i :=
  notUseTempBeforeAssignFirstIndex moves

end Flapjack.Test.ParmoveFirstIndexParity
