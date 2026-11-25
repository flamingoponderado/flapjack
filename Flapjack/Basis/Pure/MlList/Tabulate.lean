module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist$tabulate`

Lean counterparts of `tabulate_aux_def` and `tabulate_def` in
`cakeml/basis/pure/mllistScript.sml:486-507`, including HOL's termination
measure `m - n`.

The source theorems `tabulate_aux_GENLIST` and `tabulate_GENLIST` are not
ported: they state the result through HOL `GENLIST`/`FUNPOW`, which have no
decided Lean rendering.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `tabulate_aux_def`: build the list `[f n, f (n + 1), ...]` up to
index `m` from an accumulator.  HOL's `let` bindings are the direct arguments. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "tabulate_aux_def"]
def tabulateAux {α : Type} (n m : Nat) (f : Nat → α) (acc : List α) : List α :=
  if n ≥ m then acc.reverse else tabulateAux (n + 1) m f (f n :: acc)
termination_by m - n
decreasing_by omega

/-- Original `tabulate_def`: tabulate from zero with an empty accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "tabulate_def"]
def tabulate {α : Type} (n : Nat) (f : Nat → α) : List α :=
  tabulateAux 0 n f []

end Flapjack.Basis.Pure.MlList
