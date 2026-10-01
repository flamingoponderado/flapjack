import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness

namespace Flapjack.WordAlloc

/-- Literal HOL lookup equation for numeric-name insertion, with membership
and duplicate names preserved. No well-formedness premise is needed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_numset_list_insert"]
theorem lookupNumsetListInsert (names : List Nat) (key : Nat) (tree : NumSet) :
    sptLookup key (numsetListInsert names tree) =
      if key ∈ names then some () else sptLookup key tree := by
  induction names with
  | nil => simp [numsetListInsert]
  | cons head tail ih =>
      by_cases h : key = head
      · subst head
        simp [numsetListInsert, sptLookup_sptInsert_same]
      · rw [numsetListInsert, sptLookup_sptInsert_ne head key () _ h, ih]
        simp [h]

/-- Exact HOL domain equality. HOL sets are predicates; the output domain is
the union of the original tree domain and the input list's member set. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_numset_list_insert"]
theorem domainNumsetListInsert (names : List Nat) (tree : NumSet) :
    sptDomain (numsetListInsert names tree) =
      (fun key => sptDomain tree key ∨ key ∈ names) := by
  funext key
  apply propext
  unfold sptDomain
  rw [lookupNumsetListInsert]
  by_cases h : key ∈ names <;> simp [h]

/-- Exact HOL companion domain equality for the left-biased union tree.
Only domains are compared, with no additional tree invariant premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_numset_list_insert_eq_union"]
theorem domainNumsetListInsertEqUnion (names : List Nat) (tree : NumSet) :
    sptDomain (numsetListInsert names tree) =
      sptDomain (sptUnion (numsetListInsert names .ln) tree) := by
  rw [sptDomain_sptUnion, domainNumsetListInsert, domainNumsetListInsert]
  funext key
  apply propext
  simp [sptDomain, sptLookup, or_comm]

end Flapjack.WordAlloc
