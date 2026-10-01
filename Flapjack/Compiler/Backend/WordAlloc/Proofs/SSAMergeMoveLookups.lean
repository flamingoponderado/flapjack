import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveDomains

namespace Flapjack.Compiler.Backend.WordAlloc

/-- The full unchanged-lookup frame: keys absent from the input list or the
original shared domain retain both original lookups. No allocation class,
distinctness, well-formedness or counter premise is required. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame3"]
theorem mergeMovesFrame3 (names : List Nat) (next : Nat) (leftMap rightMap : Spt Nat) :
    let result := mergeMoves names leftMap rightMap next
    ∀ key, key ∉ names ∨ ¬ sptDomain (sptInter leftMap rightMap) key →
      sptLookup key result.2.2.2.1 = sptLookup key leftMap ∧
      sptLookup key result.2.2.2.2 = sptLookup key rightMap := by
  induction names with
  | nil => simp [mergeMoves]
  | cons name names ih =>
    generalize h : mergeMoves names leftMap rightMap next = result at ih ⊢
    rcases result with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at ih
    have frames := mergeMovesFrame2 names next leftMap rightMap
    rw [h] at frames
    simp only at frames
    rcases frames with ⟨leftDomain, rightDomain, _⟩
    have lift (key : Nat)
        (guard : key ∉ name :: names ∨ ¬ sptDomain (sptInter leftMap rightMap) key) :
        key ∉ names ∨ ¬ sptDomain (sptInter leftMap rightMap) key := by
      rcases guard with absent | outside
      · exact Or.inl (fun member => absent (List.mem_cons_of_mem name member))
      · exact Or.inr outside
    simp only [mergeMoves, h]
    cases leftLookup : sptLookup name leftTree with
    | none => exact fun key guard => ih key (lift key guard)
    | some leftValue =>
      cases rightLookup : sptLookup name rightTree with
      | none => exact fun key guard => ih key (lift key guard)
      | some rightValue =>
        simp only
        split
        · exact fun key guard => ih key (lift key guard)
        · simp only
          intro key guard
          have different : key ≠ name := by
            intro equal
            subst key
            rcases guard with absent | outside
            · exact absent (List.mem_cons_self)
            · apply outside
              rw [sptDomain_sptInter]
              constructor
              · rw [← leftDomain]
                simp [sptDomain, leftLookup]
              · rw [← rightDomain]
                simp [sptDomain, rightLookup]
          rw [sptLookup_sptInsert_ne name key counter leftTree different,
              sptLookup_sptInsert_ne name key counter rightTree different]
          exact ih key (lift key guard)

end Flapjack.Compiler.Backend.WordAlloc
