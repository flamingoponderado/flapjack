module

public import Flapjack.Compiler.Backend.WordToStack.ProductionCutsetMaximum
public import Flapjack.Pancake.WordLang.MaxVar

@[expose] public section

namespace Flapjack

/-- Flapjack-only accumulator normalization, with no separate HOL original. -/
private theorem foldMaximum {α : Type} (value : α → Nat) (values : List α)
    (initial : Nat) :
    values.foldl (fun result item => max result (value item)) initial =
      max initial (maxList (values.map value)) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih => simp only [List.foldl_cons, List.map_cons, maxList, ih, Nat.max_assoc]

end Flapjack
