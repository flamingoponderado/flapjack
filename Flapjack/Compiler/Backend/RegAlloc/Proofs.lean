import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.SptreeLookup

/-!
# reg_alloc proofs

Counterpart of `cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml`.
-/

namespace Flapjack.RegAlloc

/-- Exact HOL `domain_numset_list_delete` (`reg_allocProofScript.sml:1354-1362`):
the domain after deleting a list is the original domain minus the list's
members. HOL sets are predicates and `DIFF` a negated conjunct. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "domain_numset_list_delete"]
theorem domainNumsetListDelete {α : Type} :
    ∀ (l : List Nat) (live : Spt α),
      sptDomain (numsetListDelete l live) = fun k => sptDomain live k ∧ k ∉ l
  | [], live => by funext k; simp [numsetListDelete]
  | x :: xs, live => by
      rw [numsetListDelete, domainNumsetListDelete xs (sptDelete x live)]
      funext k
      apply propext
      unfold sptDomain
      rw [sptLookup_sptDelete]
      by_cases h : k = x <;> simp [h]

end Flapjack.RegAlloc
