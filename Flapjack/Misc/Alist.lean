module

public import Flapjack.HolRef

@[expose] public section

/-! Association-list lookup from the pinned HOL alist theory. -/
namespace Flapjack

/-- HOL association-list lookup, using propositional key equality. The test
reverses HOL's equality operands, which does not change the result. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_def"]
noncomputable def holALookup {K V : Type} (entries : List (K × V)) (key : K) : Option V :=
  open Classical in
  match entries with
  | [] => none
  | (entryKey, value) :: rest => if key = entryKey then some value else holALookup rest key

end Flapjack
