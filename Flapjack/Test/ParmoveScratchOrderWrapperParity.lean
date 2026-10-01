import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Parmove

namespace Flapjack.Test.ParmoveScratchOrderWrapperParity
open Compiler.Backend.Parmove Misc

/-! Replay the full original outputs, first scratch indices, input windmill and
exact option-match result from `parmove_scratch_order_wrapper_probe.out`. -/
private def scratchOrder {α : Type} [DecidableEq α] (moves : List (α × α)) : Prop :=
  match findIndex none ((parmove moves).map Prod.snd) 0 with
  | none => True
  | some i => match findIndex none ((parmove moves).map Prod.fst) 0 with
    | none => False
    | some j => ¬ i ≤ j

private def observe {α : Type} [DecidableEq α] (moves : List (α × α)) :=
  (parmove moves, findIndex none ((parmove moves).map Prod.snd) 0,
    findIndex none ((parmove moves).map Prod.fst) 0,
    decide ((moves.map Prod.fst).Nodup),
    match findIndex none ((parmove moves).map Prod.snd) 0 with
    | none => true
    | some i => match findIndex none ((parmove moves).map Prod.fst) 0 with
      | none => false
      | some j => decide (¬ i ≤ j))

example : observe ([] : List (Nat × Nat)) = ([], none, none, true, true) := by
  decide +kernel
example : observe [(0, 0)] = ([], none, none, true, true) := by decide +kernel
example : observe [(0, 1), (1, 2)] =
    ([(some 0, some 1), (some 1, some 2)], none, none, true, true) := by decide +kernel
example : observe [(0, 1), (1, 0)] =
    ([(none, some 1), (some 1, some 0), (some 0, none)], some 2, some 0, true, true) := by
  decide +kernel
example : observe [(0, 1), (1, 2), (2, 0)] =
    ([(none, some 1), (some 1, some 2), (some 2, some 0), (some 0, none)],
      some 3, some 0, true, true) := by decide +kernel
example : observe [(0, 2), (1, 2)] =
    ([(some 0, some 2), (some 1, some 2)], none, none, true, true) := by decide +kernel
example : observe [(false, true), (true, false)] =
    ([(none, some true), (some true, some false), (some false, none)],
      some 2, some 0, true, true) := by decide +kernel
example : observe [(0, 1), (0, 2)] =
    ([(some 0, some 1), (some 0, some 2)], none, none, false, true) := by decide +kernel

example {α : Type} [DecidableEq α] (moves : List (α × α))
    (valid : windmill moves) : scratchOrder moves :=
  parmoveNotUseTempBeforeAssign moves valid

example : scratchOrder ([] : List (Nat × Nat)) :=
  parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(0, 0)] := parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(0, 1), (1, 2)] := parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(0, 1), (1, 0)] := parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(0, 1), (1, 2), (2, 0)] :=
  parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(0, 2), (1, 2)] := parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)
example : scratchOrder [(false, true), (true, false)] :=
  parmoveNotUseTempBeforeAssign _ (by unfold windmill; decide +kernel)

end Flapjack.Test.ParmoveScratchOrderWrapperParity
