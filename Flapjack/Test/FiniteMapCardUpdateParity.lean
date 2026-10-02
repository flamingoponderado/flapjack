import Flapjack.FiniteMap.CardinalityExact
namespace Flapjack.Test.FiniteMapCardUpdateParity
open Flapjack
noncomputable section
local instance : DecidableEq Nat := Classical.typeDecidableEq Nat
private def empty : HolFiniteMapExact Nat Nat := HolFiniteMapExact.empty
private def one : HolFiniteMapExact Nat Nat := empty.updateEq (1, 10)
example : ((empty).updateEq (1, 10)).card =
    (if (empty).lookup 1 ≠ none then (empty).card else 1 + (empty).card) :=
  HolFiniteMapExact.fcardFupdate (empty) 1 10
example : ((one).updateEq (1, 20)).card =
    (if (one).lookup 1 ≠ none then (one).card else 1 + (one).card) :=
  HolFiniteMapExact.fcardFupdate (one) 1 20
example : ((one).updateEq (2, 30)).card =
    (if (one).lookup 2 ≠ none then (one).card else 1 + (one).card) :=
  HolFiniteMapExact.fcardFupdate (one) 2 30
example : ((one.updateEq (1, 20)).updateEq (1, 40)).card =
    (if (one.updateEq (1, 20)).lookup 1 ≠ none then (one.updateEq (1, 20)).card else 1 + (one.updateEq (1, 20)).card) :=
  HolFiniteMapExact.fcardFupdate (one.updateEq (1, 20)) 1 40
example : ((empty).updateEq (1, 10)).card = 1 := by
  simp [empty, HolFiniteMapExact.card_updateEq]
example : ((one).updateEq (1, 20)).card = 1 := by
  simp [empty, one, HolFiniteMapExact.card_updateEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
example : ((one).updateEq (2, 30)).card = 2 := by
  simp [empty, one, HolFiniteMapExact.card_updateEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
example : ((one.updateEq (1,20)).updateEq (1, 40)).card = 1 := by
  simp [empty, one, HolFiniteMapExact.card_updateEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
end
end Flapjack.Test.FiniteMapCardUpdateParity
