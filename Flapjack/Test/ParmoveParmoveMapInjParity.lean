import Flapjack.Compiler.Backend.Parmove.ParmoveMapInj

namespace Flapjack.Test.ParmoveParmoveMapInjParity
open Compiler.Backend.Parmove

/-! Kernel checks for the literal HOL theorem `parmove_MAP_INJ`
(`parmoveScript.sml:1294`): the top-level parallel-move compiler commutes with
a renaming that is injective on the flattened endpoint list and whose
temporary `NONE` is preserved and reflected, under the source `windmill`
premise. -/

-- The compiler commutes with renamings that satisfy the original premises.
example {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (ls : List (α × α))
    (h : (let ls1 := ls.map Prod.fst ++ ls.map Prod.snd;
      (∀ x y, x ∈ ls1 → y ∈ ls1 → f x = f y → x = y)) ∧ windmill ls) :
    parmove (ls.map (Prod.map f f)) =
      (parmove ls).map (Prod.map (Option.map f) (Option.map f)) :=
  parmoveMapInj f ls h

def runChecks : IO Bool := do
  IO.println "PASS parmove parmove_MAP_INJ commutes parmove with renamings"
  pure true

end Flapjack.Test.ParmoveParmoveMapInjParity
