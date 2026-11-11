module

public import Flapjack.Misc.BalancedMap.InvariantSemantics
public import Flapjack.Misc.BalancedMap.Semantics
public import Flapjack.Misc.BalancedMap.StructuralSize

@[expose] public section

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-!
# Tree-wide order transitivity and the unrotated `bin` invariant

Flapjack induction infrastructure shared by the left and right rotation
correctness modules; no separate HOL declaration is claimed for these
helpers.
-/

/-- Transitivity over the literal tree predicate for strictly less keys. -/
theorem orderedLtTrans {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (x y : κ) (tree : Map κ ν)
    (hxy : cmp x y = .lt) (hordered : keyOrdered cmp y tree .lt) :
    keyOrdered cmp x tree .lt := by
  induction tree with
  | tip => trivial
  | bin n root value left right ihl ihr =>
    exact ⟨hgood.2.2.2.2.2.2 x y root ⟨hxy, hordered.1⟩,
      ihl hordered.2.1, ihr hordered.2.2⟩

/-- Tree-wide greater transitivity from the original comparator clauses. -/
theorem orderedGtTrans {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (x y : κ) (tree : Map κ ν)
    (hxy : cmp x y = .gt) (hordered : keyOrdered cmp y tree .gt) :
    keyOrdered cmp x tree .gt := by
  induction tree with
  | tip => trivial
  | bin n root value left right ihl ihr =>
    refine ⟨?_, ihl hordered.2.1, ihr hordered.2.2⟩
    exact (hgood.2.2.1 x root).mpr
      (hgood.2.2.2.2.2.2 root y x
        ⟨(hgood.2.2.1 y root).mp hordered.1, (hgood.2.2.1 x y).mp hxy⟩)

/-- Direct proof for the original unrotated `bin` branch: both the literal
invariant and the exact finite-map image are preserved. Flapjack
infrastructure shared by the left and right balance proofs; not a separate
HOL declaration or an extra premise of the balance theorems. -/
theorem binCorrect {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering) (hl : invariant cmp left) (hr : invariant cmp right)
    (hlo : keyOrdered cmp key left .gt) (hro : keyOrdered cmp key right .lt)
    (hb : balanced (size left) (size right)) :
    invariant cmp (bin key value left right) ∧
    toFmap cmp (bin key value left right) =
      ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  have hls := structureSizeThm cmp left hl
  have hrs := structureSizeThm cmp right hr
  refine ⟨⟨?_, hlo, hro, hb, hl, hr⟩, rfl⟩
  omega

end Flapjack.Misc.BalancedMap
