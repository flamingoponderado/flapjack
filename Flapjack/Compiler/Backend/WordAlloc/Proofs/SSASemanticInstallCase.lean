import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstall
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

-- Original Install guards are extracted from its actual non-Error source run;
-- these are internal facts, not hypotheses of the full pass-correctness case.
private theorem installNonErrorInputs {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F)
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (nonError : (WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) source).1 ≠ some .error) :
    ∃ env pointer length dataPointer dataLength,
      wordSemCutEnv names source.locals = some env ∧
      WordSemStateFiniteExact.getVar ptr source = some (.word pointer) ∧
      WordSemStateFiniteExact.getVar len source = some (.word length) ∧
      WordSemStateFiniteExact.getVar dptr source = some (.word dataPointer) ∧
      WordSemStateFiniteExact.getVar dlen source = some (.word dataLength) := by
  unfold WordSemStateFiniteExact.evaluate at nonError
  split at nonError
  · simp at nonError
  · rename_i env cut
    split at nonError
    · rename_i pointer length dataPointer dataLength hp hl hdp hdl
      exact ⟨env,pointer,length,dataPointer,dataLength,cut,hp,hl,hdp,hdl⟩
    · simp at nonError

private theorem installNonErrorNormal {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F)
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (nonError : (WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) source).1 ≠ some .error) :
    (WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) source).1 = none := by
  unfold WordSemStateFiniteExact.evaluate at nonError ⊢
  repeat' split <;> simp_all

namespace SemanticInstallWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstallWitnesses

/-- Full original SSA Install case (9700-9858), retaining all six premises and
complete source-permutation/Error-exempt result/frame/locals simulation.
Actual source guards, native rename/count Move preparation, complete callback
branches, fresh pointer copy and final rename are derived. No target execution,
successful callback or desired post-relation is assumed. Imported evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8); full SSA assembly remains open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.install ptr len dptr dlen names : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.install ptr len dptr dlen names) source target ssa next tables := by
  classical
  let permuted := {source with permute := target.permute}
  have shared : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted,Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute,?_⟩
  change let run := WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) permuted
    if run.1 = some .error then True else
      let compiled := ssaCcTrans (.install ptr len dptr dlen names) ssa next tables
      let targetRun := WordSemStateFiniteExact.evaluate compiled.1 target
      run.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel run.2 targetRun.2 ∧
        match run.1 with
        | none => ssaLocalsRel compiled.2.2 compiled.2.1 run.2.locals targetRun.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (dest,_,exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain exits) run.2.locals targetRun.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (dest,entries,_) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain entries) run.2.locals targetRun.2.locals
        | some _ => run.2.locals = targetRun.2.locals
  dsimp only
  split
  · trivial
  · rename_i nonError
    obtain ⟨sourceEnv,pointer,length,dataPointer,dataLength,cut,readPtr,readLen,readDptr,readDlen⟩ :=
      installNonErrorInputs permuted ptr len dptr dlen names nonError
    have normal := installNonErrorNormal permuted ptr len dptr dlen names nonError
    let allNames := sptUnion names.1 names.2
    let nameList := (sptToAList allNames).map Prod.fst
    have prep := installPrepareArguments permuted target ssa next ptr len dptr dlen
      names.1 names.2 pointer length dataPointer dataLength sourceEnv shared
      h.2.1 h.2.2.1 h.2.2.2.2.1 readPtr readLen readDptr readDlen cut
    generalize produced : listNextVarRenameMove (width := width) ssa (next+2) nameList = output at prep
    rcases output with ⟨firstMove,mapOut,counter⟩
    dsimp only at prep
    generalize firstRun : WordSemStateFiniteExact.evaluate firstMove target = moved at prep
    rcases moved with ⟨firstResult,refreshed⟩
    dsimp only at prep
    obtain ⟨firstNone,countMove,ptrRead,lenRead,dptrRead,dlenRead,related,frame,targetEnv,
      targetCut,matching,sourceDomain⟩ := prep
    subst firstResult
    let scratch := WordSemStateFiniteExact.setVars [2,4] [.word pointer,.word length] refreshed
    have properties := listNextVarRenameMoveProps2 nameList ssa next firstMove mapOut counter
      produced ⟨Or.inl h.2.2.1,h.2.2.2.2.1⟩
    have callbacks := installCallbacksAligned permuted scratch ptr len dptr dlen
      2 4 (optionLookup mapOut dptr) (optionLookup mapOut dlen) names
      (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names)
      sourceEnv targetEnv pointer length dataPointer dataLength frame cut targetCut
      readPtr readLen readDptr readDlen ptrRead lenRead dptrRead dlenRead
    dsimp only at callbacks
    obtain ⟨result,postFrame,postLocals⟩ := callbacks
    obtain ⟨label,sourceLocals,targetLocals⟩ := postLocals normal
    let sourceAfter := (WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) permuted).2
    let targetAfter := (WordSemStateFiniteExact.evaluate
      (.install 2 4 (optionLookup mapOut dptr) (optionLookup mapOut dlen)
        (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names)) scratch).2
    have present : ∀ key, sptDomain allNames key → sptDomain permuted.locals key := by
      cases cuts : wordSemCutEnvs names permuted.locals with
      | none => simp [wordSemCutEnv,cuts] at cut
      | some pair =>
        have subsets := cutEnvsDomainSubset names.1 names.2 permuted.locals pair cuts
        intro key inNames
        rw [sptDomain_sptUnion] at inNames
        exact inNames.elim (subsets.1 key) (subsets.2 key)
    have mapped : ∀ key, sptDomain allNames key → sptDomain mapOut key := by
      intro key inNames
      obtain ⟨value,lookup⟩ := (sptMem_iff_lookup key permuted.locals).mp (present key inNames)
      exact (related.2 key value lookup).1
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL,Bool.and_eq_true,everyNameHOL,List.all_eq_true] at occurrences
    have below : ∀ key, sptDomain allNames key → key < counter := by
      intro key inNames
      have bound : key < next := by
        rw [sptDomain_sptUnion] at inNames
        rcases inNames with inFirst | inSecond
        · have bound := occurrences.2.1 key ((sptMemMapFstToAList _ key).mpr inFirst)
          simpa using bound
        · have bound := occurrences.2.2 key ((sptMemMapFstToAList _ key).mpr inSecond)
          simpa using bound
      have := properties.1
      omega
    have ptrBound : ptr < counter+2 := by
      have bound : ptr < next := by simpa using occurrences.1.1.1.1
      have := properties.1
      omega
    have restored := installRestoreResult sourceAfter targetAfter counter ptr mapOut allNames
      sourceEnv targetEnv (.loc label 0) mapped sourceDomain matching below properties.2.2.2
      (properties.2.1 h.2.2.1) ptrBound sourceLocals targetLocals postFrame
    generalize ptrProduced : nextVarRename ptr (sptInter mapOut allNames) (counter+2) = ptrOutput at restored
    rcases ptrOutput with ⟨ptrOut,ptrSSA,ptrCounter⟩
    dsimp only at restored
    generalize returnProduced : listNextVarRenameMove (width := width) ptrSSA ptrCounter nameList = returnOutput at restored
    rcases returnOutput with ⟨returnMove,ssaOut,nextOut⟩
    dsimp only at restored
    generalize restoreRun : WordSemStateFiniteExact.evaluate
      (.seq (.move 1 [(ptrOut,2)]) returnMove) targetAfter = finalRun at restored
    rcases finalRun with ⟨finalResult,finalState⟩
    dsimp only at restored
    obtain ⟨finalNone,finalRelated,finalFrame⟩ := restored
    subst finalResult
    have compiled : ssaCcTrans (.install ptr len dptr dlen names) ssa next tables =
        (.seq firstMove (.seq (.move 1 [(2,optionLookup mapOut ptr),(4,optionLookup mapOut len)])
          (.seq (.install 2 4 (optionLookup mapOut dptr) (optionLookup mapOut dlen)
            (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names))
            (.seq (.move 1 [(ptrOut,2)]) returnMove))),ssaOut,nextOut) := by
      dsimp only [nameList,allNames] at produced returnProduced ptrProduced
      simp only [ssaCcTrans,produced,ptrProduced,returnProduced]
    have callbackRun : WordSemStateFiniteExact.evaluate
        (.install 2 4 (optionLookup mapOut dptr) (optionLookup mapOut dlen)
          (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) names)) scratch =
        (none,targetAfter) := Prod.ext (result.symm.trans normal) rfl
    have targetRun : WordSemStateFiniteExact.evaluate
        (ssaCcTrans (.install ptr len dptr dlen names) ssa next tables).1 target = (none,finalState) := by
      rw [compiled]
      dsimp only
      rw [evaluateSeqCollapse _ _ target refreshed firstRun,
        evaluateSeqCollapse _ _ refreshed scratch countMove,
        evaluateSeqCollapse _ _ scratch targetAfter callbackRun,restoreRun]
    rw [targetRun]
    simp only [normal,compiled]
    exact ⟨trivial,finalFrame,finalRelated⟩

end Flapjack.Compiler.Backend.WordAlloc
