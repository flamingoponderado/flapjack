import Flapjack.HolRef

/-!
# Faithful Cake `list_subset` (`misc`)

Exact definition from `cakeml/misc/miscScript.sml:3092`. `list_subset l1 l2`
holds when every element of `l1` is a member of `l2`. The type is fully
polymorphic in HOL (`'a list -> 'a list -> bool`), so the definition carries no
type-indexed word and needs no carrier qualifier: HOL `EVERY (\x. MEM x l2) l1`
is Lean `l1.all (fun x => decide (x ∈ l2))`, with HOL's decidable equality
rendered by `[DecidableEq α]`.
-/

namespace Flapjack.Misc

/-- Exact HOL `misc$list_subset_def` (`miscScript.sml:3092`):
`list_subset l1 l2 = EVERY (\x. MEM x l2) l1`. -/
@[hol "cakeml/misc/miscScript.sml" "list_subset_def"]
def listSubset {α : Type} [DecidableEq α] (l1 l2 : List α) : Bool :=
  l1.all (fun x => decide (x ∈ l2))

end Flapjack.Misc
