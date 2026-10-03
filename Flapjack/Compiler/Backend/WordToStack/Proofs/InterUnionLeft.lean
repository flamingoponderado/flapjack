import Flapjack.Misc.Sptree

namespace Flapjack.WordToStackProofs

/-- Full original tree equality, retaining HOL’s essential well-formedness
premise. Intersection normalizes empty branches, so the equation does not
hold for arbitrary malformed trees. No payload equality instance is used. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "inter_union_left"]
theorem interUnionLeft {α : Type} (s t : Spt α) (valid : sptWf s = true) :
    sptInter (sptUnion s t) s = s := by
  induction s generalizing t with
  | ln => cases t <;> simp [sptUnion, sptInter]
  | ls value => cases t <;> simp [sptUnion, sptInter]
  | bn left right ihLeft ihRight =>
      simp only [sptWf, Bool.and_eq_true] at valid
      have selfLeft : sptInter left left = left := by
        have h := ihLeft .ln valid.1.1
        cases left <;> simpa only [sptUnion] using h
      have selfRight : sptInter right right = right := by
        have h := ihRight .ln valid.1.2
        cases right <;> simpa only [sptUnion] using h
      cases t <;> simp only [sptUnion, sptInter]
      all_goals
        try simp only [ihLeft _ valid.1.1, ihRight _ valid.1.2, selfLeft, selfRight]
        cases left <;> cases right <;> simp_all [sptMkBN, sptIsEmpty]
  | bs left value right ihLeft ihRight =>
      simp only [sptWf, Bool.and_eq_true] at valid
      have selfLeft : sptInter left left = left := by
        have h := ihLeft .ln valid.1.1
        cases left <;> simpa only [sptUnion] using h
      have selfRight : sptInter right right = right := by
        have h := ihRight .ln valid.1.2
        cases right <;> simpa only [sptUnion] using h
      cases t <;> simp only [sptUnion, sptInter]
      all_goals
        try simp only [ihLeft _ valid.1.1, ihRight _ valid.1.2, selfLeft, selfRight]
        cases left <;> cases right <;> simp_all [sptMkBS, sptIsEmpty]

end Flapjack.WordToStackProofs
