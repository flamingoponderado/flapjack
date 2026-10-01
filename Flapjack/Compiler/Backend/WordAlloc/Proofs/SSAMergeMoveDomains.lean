import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure: updating an already present key preserves domain.
There is no independent HOL declaration assigned to this derived law. -/
private theorem domainInsertPresent (tree : Spt Nat) (key value : Nat)
    (present : sptDomain tree key) :
    sptDomain (sptInsert key value tree) = sptDomain tree := by
  funext other
  apply propext
  change sptMem other (sptInsert key value tree) ↔ sptMem other tree
  rw [sptMem_sptInsert]
  constructor
  · rintro (equal | member)
    · simpa only [equal, sptMem] using present
    · exact member
  · exact Or.inr

/-- Domain preservation and agreement at shared input keys, without tree
well-formedness, distinctness, allocation-class or counter hypotheses.
Both full domain equalities and the original intersection-membership implication
are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame2"]
theorem mergeMovesFrame2 (names : List Nat) (next : Nat) (leftMap rightMap : Spt Nat) :
    let result := mergeMoves names leftMap rightMap next
    sptDomain result.2.2.2.1 = sptDomain leftMap ∧
    sptDomain result.2.2.2.2 = sptDomain rightMap ∧
    (∀ key, key ∈ names ∧ sptDomain (sptInter leftMap rightMap) key →
      sptLookup key result.2.2.2.1 = sptLookup key result.2.2.2.2) := by
  induction names with
  | nil => simp [mergeMoves]
  | cons name names ih =>
    generalize h : mergeMoves names leftMap rightMap next = result at ih ⊢
    rcases result with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at ih
    rcases ih with ⟨leftDomain, rightDomain, agreement⟩
    have present (key : Nat) (common : sptDomain (sptInter leftMap rightMap) key) :
        sptDomain leftTree key ∧ sptDomain rightTree key := by
      rw [sptDomain_sptInter] at common
      simpa only [leftDomain, rightDomain] using common
    have extend (head : sptDomain (sptInter leftMap rightMap) name →
        sptLookup name leftTree = sptLookup name rightTree) :
        ∀ key, key ∈ name :: names ∧ sptDomain (sptInter leftMap rightMap) key →
          sptLookup key leftTree = sptLookup key rightTree := by
      intro key ⟨member, common⟩
      rcases List.mem_cons.mp member with equal | member
      · subst key
        exact head common
      · exact agreement key ⟨member, common⟩
    simp only [mergeMoves, h]
    cases leftLookup : sptLookup name leftTree with
    | none =>
      refine ⟨leftDomain, rightDomain, extend ?_⟩
      intro common
      have impossible := (present name common).1
      simp [sptDomain, leftLookup] at impossible
    | some leftValue =>
      cases rightLookup : sptLookup name rightTree with
      | none =>
        refine ⟨leftDomain, rightDomain, extend ?_⟩
        intro common
        have impossible := (present name common).2
        simp [sptDomain, rightLookup] at impossible
      | some rightValue =>
        simp only
        split
        · rename_i equal
          refine ⟨leftDomain, rightDomain, extend ?_⟩
          intro _
          simp only [leftLookup, rightLookup, equal]
        · simp only
          refine ⟨?_, ?_, ?_⟩
          · rw [domainInsertPresent leftTree name counter (by simp [sptDomain, leftLookup])]
            exact leftDomain
          · rw [domainInsertPresent rightTree name counter (by simp [sptDomain, rightLookup])]
            exact rightDomain
          · intro key ⟨member, common⟩
            by_cases equal : key = name
            · subst key
              rw [sptLookup_sptInsert_same, sptLookup_sptInsert_same]
            · rw [sptLookup_sptInsert_ne name key counter leftTree equal,
                  sptLookup_sptInsert_ne name key counter rightTree equal]
              exact agreement key ⟨(List.mem_cons.mp member).resolve_left equal, common⟩

end Flapjack.Compiler.Backend.WordAlloc
