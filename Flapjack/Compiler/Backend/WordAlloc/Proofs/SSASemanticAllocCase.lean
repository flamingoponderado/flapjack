import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticAlloc
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticAllocWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticAllocWitnesses

/-- Full original SSA Alloc case (9333-9606), retaining all six premises and
complete source-permutation/Error-exempt simulation conclusion. Actual target
rename/count moves, GC/allocation and final restoration are derived. All normal
and exhausted-space branches retain total native evaluation and full frame;
no successful target run or desired post-relation is assumed. Imported evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). Full SSA assembly remains open. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next num : Nat) (names : WordLangCutsetsHOL)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.alloc num names : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.alloc num names) source target ssa next tables := by
  classical
  by_cases readable : ∃ amount, WordSemStateFiniteExact.getVar num source = some (.word amount)
  · obtain ⟨amount,read⟩ := readable
    cases cut : wordSemCutEnvs names source.locals with
    | none =>
      refine ⟨source.permute,?_⟩
      have run : WordSemStateFiniteExact.evaluate (.alloc num names)
          {source with permute := source.permute} = (some .error,
            WordSemStateFiniteExact.flushState true {source with permute := source.permute}) := by
        have permRead : WordSemStateFiniteExact.getVar num
            {source with permute := source.permute} = some (.word amount) := read
        simp only [WordSemStateFiniteExact.evaluate,permRead,WordSemStateFiniteExact.alloc,cut]
      simp only [run,ite_true]
    | some envs =>
      let allNames := sptUnion names.1 names.2
      let nameList := (sptToAList allNames).map Prod.fst
      have prep := allocPrepareArguments source target ssa next num names.1 names.2
        envs.1 envs.2 amount cut read h.2.1 h.2.2.1 h.2.2.2.2.1 h.1
      generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
        nameList = firstOutput at prep
      rcases firstOutput with ⟨firstMove,mapOut,counter⟩
      dsimp only at prep
      generalize moved : WordSemStateFiniteExact.evaluate firstMove target = firstRun at prep
      rcases firstRun with ⟨firstResult,refreshed⟩
      dsimp only at prep
      obtain ⟨firstNone,countMove,countRead,related,frame,cuts⟩ := prep
      subst firstResult
      let scratch := WordSemStateFiniteExact.setVar 2 (.word amount) refreshed
      have properties := listNextVarRenameMoveProps2 nameList ssa next firstMove mapOut counter
        produced ⟨Or.inl h.2.2.1,h.2.2.2.2.1⟩
      have injection : ∀ a b, (sptDomain names.1 a ∨ sptDomain names.2 a) →
          (sptDomain names.1 b ∨ sptDomain names.2 b) →
          optionLookup mapOut a = optionLookup mapOut b → a = b := by
        intro a b inA inB equal
        exact listNextVarRenameMoveDistinct ssa (next+2) nameList firstMove mapOut counter a b
          ⟨produced,sptAllDistinctMapFstToAList _,
            (sptMemMapFstToAList allNames a).mpr (by simpa [allNames,sptDomain_sptUnion] using inA),
            (sptMemMapFstToAList allNames b).mpr (by simpa [allNames,sptDomain_sptUnion] using inB),equal⟩
      have scopedRelation : ∀ live : Nat → Prop,
          Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) live source.locals scratch.locals := by
        intro live key value found
        have matching := related.2 key value found.2
        obtain ⟨register,lookup⟩ := (sptMem_iff_lookup key mapOut).mp matching.1
        simpa [optionLookup,lookup] using matching.2.1
      obtain ⟨perm,transport⟩ := allocCollectorTransport source scratch mapOut names.1 names.2
        amount frame injection (scopedRelation _) (scopedRelation _)
      refine ⟨perm,?_⟩
      have permRead : WordSemStateFiniteExact.getVar num {source with permute := perm} =
          some (.word amount) := read
      simp only [WordSemStateFiniteExact.evaluate,permRead]
      split
      · trivial
      · rename_i nonError
        obtain ⟨result,postFrame,normalPost⟩ := transport nonError
        have shape := allocNonErrorShape amount names {source with permute := perm} nonError
        generalize returned : listNextVarRenameMove (width := width)
          (sptInter mapOut allNames) (counter+2) nameList = returnOutput
        rcases returnOutput with ⟨returnMove,ssaOut,nextOut⟩
        have compiled : ssaCcTrans (.alloc num names) ssa next tables =
            (.seq firstMove (.seq (.move 1 [(2,optionLookup mapOut num)])
              (.seq (.alloc 2 (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names))
                returnMove)),ssaOut,nextOut) := by
          dsimp only [allNames,nameList] at produced returned
          simp only [ssaCcTrans,produced,returned]
        have prefixRun : WordSemStateFiniteExact.evaluate (ssaCcTrans (.alloc num names) ssa next tables).1 target =
            WordSemStateFiniteExact.evaluate
              (.seq (.alloc 2 (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names)) returnMove)
              scratch := by
          rw [compiled]
          dsimp only
          rw [evaluateSeqCollapse _ _ target refreshed moved,
            evaluateSeqCollapse _ _ refreshed scratch countMove]
        have allocRun : WordSemStateFiniteExact.evaluate
            (.alloc 2 (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names)) scratch =
            WordSemStateFiniteExact.alloc amount
              (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch := by
          have scratchRead : WordSemStateFiniteExact.getVar 2 scratch = some (.word amount) := countRead
          simp only [WordSemStateFiniteExact.evaluate,scratchRead]
        rcases shape with normal | ⟨exhausted,emptySource⟩
        · obtain ⟨postRelated,postDomain⟩ := normalPost normal
          let sourceAfter := (WordSemStateFiniteExact.alloc amount names {source with permute := perm}).2
          let targetAfter := (WordSemStateFiniteExact.alloc amount
            (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch).2
          have subsets := cutEnvsDomainSubset names.1 names.2 source.locals envs cut
          have mapped : ∀ key, sptDomain allNames key → sptDomain mapOut key := by
            intro key inNames
            have inSource : sptDomain source.locals key := by
              rw [sptDomain_sptUnion] at inNames
              exact inNames.elim (subsets.1 key) (subsets.2 key)
            obtain ⟨value,lookup⟩ := (sptMem_iff_lookup key source.locals).mp inSource
            exact (related.2 key value lookup).1
          have below : ∀ key, sptDomain allNames key → key < counter := by
            intro key inNames
            have occurrence := h.2.2.2.1
            simp only [everyVarHOL,Bool.and_eq_true,everyNameHOL,List.all_eq_true] at occurrence
            have keyBound : key < next := by
              rw [sptDomain_sptUnion] at inNames
              rcases inNames with inFirst | inSecond
              · have bound := occurrence.2.1 key ((sptMemMapFstToAList _ key).mpr inFirst)
                simpa using bound
              · have bound := occurrence.2.2 key ((sptMemMapFstToAList _ key).mpr inSecond)
                simpa using bound
            have := properties.1
            omega
          have restored := allocRestoreLocals sourceAfter targetAfter mapOut allNames counter
            mapped postDomain postRelated below properties.2.2.2 postFrame
          have returnEquation := returned
          dsimp only [nameList] at returnEquation
          rw [returnEquation] at restored
          dsimp only at restored
          generalize restoreRun : WordSemStateFiniteExact.evaluate returnMove targetAfter = finalRun at restored
          rcases finalRun with ⟨finalResult,finalState⟩
          dsimp only at restored
          obtain ⟨finalNone,finalRelated,finalFrame⟩ := restored
          subst finalResult
          have raw : WordSemStateFiniteExact.alloc amount
              (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch =
              (none,targetAfter) := Prod.ext (result.symm.trans normal) rfl
          have targetRun : WordSemStateFiniteExact.evaluate
              (ssaCcTrans (.alloc num names) ssa next tables).1 target = (none,finalState) := by
            rw [prefixRun,evaluateSeqCollapse _ _ scratch targetAfter (allocRun.trans raw),restoreRun]
          rw [targetRun]
          simp only [normal,compiled]
          exact ⟨trivial,finalFrame,finalRelated⟩
        · have targetExhausted : (WordSemStateFiniteExact.alloc amount
              (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch).1 =
              some .notEnoughSpace := result.symm.trans exhausted
          have targetNonError : (WordSemStateFiniteExact.alloc amount
              (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch).1 ≠
              some .error := by rw [targetExhausted]; simp
          have targetShape := allocNonErrorShape amount
            (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch targetNonError
          have emptyTarget : (WordSemStateFiniteExact.alloc amount
              (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch).2.locals = .ln := by
            rcases targetShape with targetNone | ⟨_,empty⟩
            · rw [targetExhausted] at targetNone; cases targetNone
            · exact empty
          have targetRun : WordSemStateFiniteExact.evaluate
              (ssaCcTrans (.alloc num names) ssa next tables).1 target =
              WordSemStateFiniteExact.alloc amount
                (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names) scratch := by
            rw [prefixRun]
            rw [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.fix_clock_evaluate,allocRun]
            simp only [targetExhausted]
            exact Prod.ext targetExhausted.symm rfl
          simp only [exhausted,targetRun,targetExhausted]
          exact ⟨trivial,postFrame,emptySource.trans emptyTarget.symm⟩
  · refine ⟨source.permute,?_⟩
    have noWord : ∀ amount, WordSemStateFiniteExact.getVar num source ≠ some (.word amount) := by
      simpa only [not_exists] using readable
    have run : (WordSemStateFiniteExact.evaluate (.alloc num names)
        {source with permute := source.permute}).1 = some .error := by
      cases read : WordSemStateFiniteExact.getVar num source with
      | none =>
        have permRead : WordSemStateFiniteExact.getVar num {source with permute := source.permute} = none := read
        simp only [WordSemStateFiniteExact.evaluate,permRead]
      | some value =>
        cases value with
        | word amount => exact False.elim (noWord amount read)
        | loc a b =>
          have permRead : WordSemStateFiniteExact.getVar num {source with permute := source.permute} = some (.loc a b) := read
          simp only [WordSemStateFiniteExact.evaluate,permRead]
    simp only [run,ite_true]

end Flapjack.Compiler.Backend.WordAlloc
