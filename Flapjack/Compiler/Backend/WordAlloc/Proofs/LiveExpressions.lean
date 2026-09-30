import Flapjack.Compiler.Backend.WordAlloc.Expressions

namespace Flapjack.WordAlloc

/-- Exact HOL membership-to-domain-subset statement for expression live sets.
HOL set inclusion is rendered pointwise over the characteristic predicates;
the list may contain repeated expressions and the trees need no extra wf premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_big_union_subset"
  (words_as_type_indexed_bitvec)]
theorem domainBigUnionSubset {width : Nat} [NeZero width] :
    ∀ (ls : List (WordLangExpHOL (BitVec width))) (a : WordLangExpHOL (BitVec width)),
      a ∈ ls → ∀ key, sptDomain (getLiveExp a) key →
        sptDomain (bigUnion (ls.map getLiveExp)) key := by
  intro ls
  induction ls with
  | nil =>
      intro a ha
      simp at ha
  | cons head tail ih =>
      intro a ha key hk
      change sptDomain (sptUnion (getLiveExp head) (bigUnion (tail.map getLiveExp))) key
      rw [sptDomain_sptUnion]
      rcases List.mem_cons.mp ha with heq | hmem
      · subst a
        exact Or.inl hk
      · exact Or.inr (ih a hmem key hk)

end Flapjack.WordAlloc
