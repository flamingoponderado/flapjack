import Flapjack.Compiler.Backend.WordToStack.ProductionCutsetMaximum
import Flapjack.Pancake.WordLang.MaxVar

namespace Flapjack

/-- Flapjack-only accumulator normalization, with no separate HOL original. -/
private theorem foldMaximum {α : Type} (value : α → Nat) (values : List α)
    (initial : Nat) :
    values.foldl (fun result item => max result (value item)) initial =
      max initial (maxList (values.map value)) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih => simp only [List.foldl_cons, List.map_cons, maxList, ih, Nat.max_assoc]

/-- Flapjack-only specialization to the production natural-name scan. -/
private theorem foldNames (values : List Nat) (initial : Nat) :
    values.foldl max initial = max initial (maxList values) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih => simp only [List.foldl_cons, maxList, ih, Nat.max_assoc]

/-- Flapjack-only equality between the two full Move name scans. -/
private theorem moveMaximum (moves : List (Nat × Nat)) :
    moves.foldl (fun result move => max result (max move.1 move.2)) 0 =
      maxList (moves.map Prod.fst ++ moves.map Prod.snd) := by
  rw [foldMaximum, Nat.zero_max, maxList_append]
  induction moves with
  | nil => simp [maxList]
  | cons head tail ih =>
      simp only [List.map_cons, maxList] at *
      omega

/-- Flapjack-only normalization of the reviewed three-way maximum. -/
private theorem max3Maximum (a b c : Nat) : max3HOL a b c = max a (max b c) := by
  unfold max3HOL
  split <;> split <;> omega

end Flapjack
