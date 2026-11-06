import Flapjack.SemanticPrimitivesHOL
import Flapjack.FiniteMap.AlistExact.Lookup

/-! Properties of recursive-function lookup. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Recursive-function lookup is association-list lookup. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "find_recfun_ALOOKUP"]
theorem findRecFun_alookup {α β : Type} (funs : List (VarN × α × β)) (name : VarN) :
    findRecFun name funs = Flapjack.holALookup funs name := by
  classical
  induction funs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨f, x, body⟩ := entry
    by_cases same : f = name
    · subst f
      simp [findRecFun, Flapjack.holALookup]
    · have reverse : name ≠ f := Ne.symm same
      simp [findRecFun, Flapjack.holALookup, same, reverse, ih]

end Flapjack.SemanticPrimitivesProps
