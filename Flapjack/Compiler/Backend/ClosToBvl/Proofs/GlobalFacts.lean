module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.GlobalTraversal
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.GlobalInvariants

@[expose] public section

/-! Global-write bags through closure compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosProps
open Flapjack.Compiler.Backend.FlatProps (emptyGlobalBag unionGlobalBag)

/-- A singleton expression list has exactly the expression global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "elist_globals_sing"]
theorem elistGlobals_singleton (x : ClosLang.Exp) : elistGlobals [x] = setGlobals x := by
  funext k
  simp [elistGlobals, unionGlobalBag, emptyGlobalBag, bagUnion, emptyBag]

/-- Introducing multi-argument calls preserves a singleton expression global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "set_globals_HD_intro_multi"]
theorem setGlobals_head_introMulti (x : Nat) (y : ClosLang.Exp) :
    setGlobals (holHd (ClosMti.introList x [y])) = setGlobals y := by
  have h := ClosMti.intro_multi_preserves_elist_globals x [y]
  simpa [ClosMti.introList, holHd, elistGlobals_singleton] using h

/-- Renumbering one expression preserves its global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "set_globals_SND_renumber_code_locs"]
theorem setGlobals_renumber (x : Nat) (y : ClosLang.Exp) :
    setGlobals (ClosNumber.renumber x y).2 = setGlobals y := by
  exact ClosNumber.renumberCodeLocs_elistGlobals.2 x y
    (ClosNumber.renumber x y).1 (ClosNumber.renumber x y).2 (Prod.eta _).symm

/-- Flattening expression lists folds their global-write bags. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "elist_globals_FLAT"]
theorem elistGlobals_flatten (ls : List (List ClosLang.Exp)) :
    elistGlobals ls.flatten = (ls.map elistGlobals).foldr bagUnion emptyBag := by
  induction ls with
  | nil => simp [elistGlobals, emptyGlobalBag]
  | cons xs rest ih =>
    simp only [List.flatten_cons, elistGlobals_append, List.map_cons, List.foldr_cons, ih]
end Flapjack.Compiler.Backend.ClosToBvl
