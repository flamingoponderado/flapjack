module

public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

/-!
# The domain of a round-tripped association list

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:24-28`
(`domain_fromAList_toAList`), a utility lemma the script marks `TODO move`.
`domain` is the reviewed membership rendering `sptDomain`, so the theorem is a
pointwise statement about `sptFromAList`/`sptToAList`.
-/

namespace Flapjack

/-- HOL `domain_fromAList_toAList`: rebuilding a tree from its own association
list leaves the domain unchanged. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "domain_fromAList_toAList"]
theorem sptDomainFromAListToAList {α : Type} (tree : Spt α) :
    sptDomain (sptFromAList (sptToAList tree)) = sptDomain tree := by
  rw [sptDomainFromAList]
  funext key
  exact propext (sptMemMapFstToAList tree key)

end Flapjack
