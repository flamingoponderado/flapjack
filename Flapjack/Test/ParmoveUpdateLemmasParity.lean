import Flapjack.Compiler.Backend.Parmove.UpdateLemmas

namespace Flapjack.Test.ParmoveUpdateLemmasParity
open Flapjack.Compiler.Backend.Parmove
/-! Ten direct original observations from `parmove_updates_probe.out`.
Fresh insertion does not change snapshot source values; repeated destinations
show the boundary of the HOL freshness premise. The relation ignores NONE. -/
def env (n : Nat) := n + 10
#guard parsem [(1, 2), (3, 1)] env 1 == 12
#guard parsem [(1, 2), (3, 1)] env 3 == 11
#guard parsem [(1, 2), (3, 1)] env 7 == 17
#guard parsem [(1, 2), (3, 2)] env 3 == 12
#guard parsem [(1, 2), (1, 3)] env 1 == 13
#guard parsem [] env 1 == 11
#guard parsem [(1, 1)] env 1 == 11
#guard parsem [(1, 2), (2, 1)] env 2 == 11

def first : Option Nat → Nat | none => 0 | some _ => 1
def second : Option Nat → Nat | none => 9 | some _ => 1
example : eqenv first second := by
  intro register real
  cases register with
  | none => simp at real
  | some n => rfl
example : eqenv second first := by
  apply eqenv_sym first second
  intro register real
  cases register with
  | none => simp at real
  | some n => rfl

-- Generic key and value carriers; the original tagged freshness/windmill
-- premises are discharged at the call site, never replaced by output facts.
example {α β : Type} [DecidableEq α] (x y : α) (moves : List (α × α))
    (rho : α → β) (fresh : x ∉ moves.map Prod.fst) :
    parsem ((x, y) :: moves) rho = updateEnv (parsem moves rho) x (rho y) :=
  parsem_cons x y moves rho fresh
example {α β : Type} [DecidableEq α] (moves : List (α × α))
    (rho : α → β) (x : α) (h : windmill moves ∧ x ∉ moves.map Prod.fst) :
    parsem moves rho x = rho x := parsem_untouched rho moves x h
end Flapjack.Test.ParmoveUpdateLemmasParity
