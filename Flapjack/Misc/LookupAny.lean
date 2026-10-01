import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal `lookup_any` (`miscScript.sml:344-348`): a sparse-tree lookup with
a default for absent keys; value type arbitrary, as in HOL
(`num -> α num_map -> α -> α`). -/
@[hol "cakeml/misc/miscScript.sml" "lookup_any_def"]
def lookupAny {α : Type} (x : Nat) (sp : Spt α) (d : α) : α :=
  match sptLookup x sp with
  | none => d
  | some m => m

end Flapjack
