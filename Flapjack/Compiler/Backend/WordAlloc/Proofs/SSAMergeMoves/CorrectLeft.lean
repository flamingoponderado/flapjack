import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectRight

namespace Flapjack.Compiler.Backend.WordAlloc

namespace CorrectLeftWitnesses

/-- Flapjack canonical carrier roundtrip, re-exported in this counterpart. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CorrectLeftWitnesses

/-- Full left-side native merge correctness, with all original hypotheses and
five conclusions. Only the word dimension is shared between source and target;
their code/FFI carriers remain independent. Guarded SOME lookups determine the
selector payload. The evaluator inherits its rational-cut FP boundary, although
this Move branch only reads and writes locals. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_correctL"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem mergeMovesCorrectL {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (names : List Nat) (next : Nat)
    (left right : Spt Nat) (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) (priority : Nat)
    (allocated : isAllocVar next) (distinct : names.Nodup)
    (valid : ssaMapOK next left) :
    let merged := mergeMoves names left right next
    ssaLocalsRel next left source.locals target.locals →
    let evaluated := WordSemStateFiniteExact.evaluate (.move priority merged.1) target
    evaluated.1 = none ∧
      (∀ key, key ∉ names → sptLookup key merged.2.2.2.1 = sptLookup key left) ∧
      (∀ key value, key < next → sptLookup key target.locals = some value →
        sptLookup key evaluated.2.locals = some value) ∧
      ssaLocalsRel merged.2.2.1 merged.2.2.2.1 source.locals evaluated.2.locals ∧
      Flapjack.WordAlloc.wordStateEqRel target evaluated.2 := by
  induction names with
  | nil =>
    dsimp only
    intro related
    exact by simpa only [mergeMoves, mergeRightEmptyEvaluation] using mergeRightEmptyCorrect next right left source target priority related
  | cons name names ih =>
    have absent : name ∉ names := (List.nodup_cons.mp distinct).1
    have tail := ih distinct.tail
    dsimp only at tail ⊢
    intro related
    have tailResult := tail related
    generalize hm : mergeMoves names left right next = merged at tailResult
    rcases merged with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at tailResult
    generalize he : WordSemStateFiniteExact.evaluate (.move priority leftMoves) target = evaluated at tailResult
    rcases evaluated with ⟨result, after⟩
    simp only at tailResult
    rcases tailResult with ⟨resultNone, unchanged, preserved, localsRelated, stateRelated⟩
    subst result
    simp only [mergeMoves, hm]
    cases hl : sptLookup name leftTree with
    | none =>
      simp only [he]
      exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
        preserved, localsRelated, stateRelated⟩
    | some leftRegister =>
      cases hr : sptLookup name rightTree with
      | none =>
        simp only [he]
        exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
          preserved, localsRelated, stateRelated⟩
      | some rightRegister =>
        simp only
        split
        · simp only [he]
          exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
            preserved, localsRelated, stateRelated⟩
        · have frame := mergeMovesFrame names next left right allocated
          have bounds := mergeMovesFst names next left right
          rw [hm] at frame bounds
          simp only at frame bounds
          have rightValid := frame.2.2.1 valid
          have originalLookup : sptLookup name left = some leftRegister :=
            (unchanged name absent).symm.trans hl
          have registerBound := (valid name leftRegister originalLookup).2
          have sourcePresent := related.1 name leftRegister originalLookup
          have sourceNotWritten : leftRegister ∉ leftMoves.map Prod.fst := by
            intro member
            have bound := (bounds.2.1 leftRegister member).2
            omega
          have destinationNotWritten : counter ∉ leftMoves.map Prod.fst := by
            intro member
            have bound := (bounds.2.1 counter member).1
            omega
          have head := movEvalHead priority leftMoves target after counter leftRegister
            he sourcePresent sourceNotWritten destinationNotWritten
          simp only [head]
          refine ⟨True.intro, ?_, ?_, ?_, ?_⟩
          · intro key outside
            have different : key ≠ name := by
              intro equal; subst key; exact outside (List.mem_cons_self)
            rw [sptLookup_sptInsert_ne _ _ _ _ different]
            exact unchanged key (fun member => outside (List.mem_cons_of_mem name member))
          · exact mergeRightOldLocalsStep next counter _ target.locals after.locals bounds.1 preserved
          · rcases (sptMem_iff_lookup leftRegister target.locals).mp sourcePresent with ⟨value, found⟩
            have afterFound := preserved leftRegister value registerBound found
            simpa only [found, Option.getD_some] using
              mergeRightLocalsStep counter name leftRegister value leftTree source.locals after.locals
                rightValid localsRelated hl afterFound
          · exact mergeRightStateStep target after _ stateRelated


end Flapjack.Compiler.Backend.WordAlloc
