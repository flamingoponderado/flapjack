import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# The `Store` case of `crep_to_loop`'s `ncompile_correct`

This is the constructor case resumed at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:1758-1856`. The destination
and source expressions compile in sequence; the latter may allocate locals
above the former's temporary range, as in HOL's proof.
-/

namespace Flapjack

open LoopSemStateFiniteExact
open Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! Owning carriers for this theorem's finite-map representation qualifier. -/
namespace NCompileCorrectStoreFmapWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : LoopSemStateBroad width σ) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width σ,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end NCompileCorrectStoreFmapWitnesses

open Classical in
/-- Genuine `Store dst src` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1758-1856`).
    `evaluate_ind` gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_store {width : Nat} [NeZero width] {σ : Type} :
    ∀ (destination sourceExp : CrepExpHOL width) (sourceState : CrepSemHOLState width σ)
      (result : Option (CrepResultHOLExact width)) (sourceFinal : CrepSemHOLState width σ)
      (target : LoopSemStateFiniteExact width σ) (context : CrepToLoopContextExact)
      (live : NumSet),
      evalCrepSemHOLProgExact sourceState (.store destination sourceExp) = (result, sourceFinal) ∧
        result ≠ some .error ∧ crepToLoopStateRelExact sourceState target ∧
        crepToLoopMemRelHOLExact sourceState.memory target.memory sourceState.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceState.globals target.globals ∧
        crepToLoopCodeRelExact context sourceState.code target.code ∧
        crepToLoopLocalsRelExact context live sourceState.locals target.locals →
      ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
        (targetFinal : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact context live
            (.store destination sourceExp))
          { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
        crepToLoopStateRelExact sourceFinal targetFinal ∧
        crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
        crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
        targetResult = resultToLoop result ∧
        localsResultRel context live result sourceFinal targetFinal := by
  intro destination sourceExp sourceState result sourceFinal target context live
    ⟨hEval, hNotError, hState, hMem, hGlobals, hCode, hLocals⟩
  rw [evalCrepSemHOLProgExact_store_holShape] at hEval
  cases hDst : evalCrepSemHOLExp sourceState destination with
  | none => simp [hDst] at hEval; exact absurd hEval.1.symm hNotError
  | some dstValue =>
    cases dstValue with
    | word address =>
      cases hSrc : evalCrepSemHOLExp sourceState sourceExp with
      | none => simp [hDst, hSrc] at hEval; exact absurd hEval.1.symm hNotError
      | some value =>
        cases hStore : panMemStoreHOL address value sourceState.memaddrs sourceState.memory with
        | none => simp [hDst, hSrc, hStore] at hEval; exact absurd hEval.1.symm hNotError
        | some sourceMemory =>
          have hSourceDomain : sourceState.memaddrs address := by
            by_cases hDomain : sourceState.memaddrs address
            · exact hDomain
            · simp [panMemStoreHOL, hDomain] at hStore
          have hSourceMemory : sourceMemory =
              fun current => if current = address then value else sourceState.memory current := by
            have h := hStore
            simp [panMemStoreHOL, hSourceDomain] at h
            exact h.symm
          simp only [hDst, hSrc, hStore, Prod.mk.injEq] at hEval
          have hResultNone : result = none := hEval.1.symm
          have hSourceFinal : sourceFinal = { sourceState with memory := sourceMemory } := hEval.2.symm
          rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
            ⟨destinationCode, destinationExp, destinationTmp, destinationLive⟩
          obtain ⟨firstExtra, afterDestination, hFirst, hDestinationValue,
            hState1, hMem1, hGlobals1, hCode1, hLocals1⟩ :=
            crepToLoop_comp_exp_preserves_eval sourceState destination (.word address) target
              context (context.vmax + 1) live destinationCode destinationExp destinationTmp
              destinationLive ⟨hDst, hState, hMem, hGlobals, hCode, hLocals, hD,
                Nat.lt_succ_self _⟩
          rcases hS : compileExpHOLExact context destinationTmp destinationLive sourceExp with
            ⟨sourceCode, sourceCompiledExp, sourceTmp, sourceLive⟩
          have ⟨hOkDst, hTmpDst, hLiveDst⟩ := compile_exp_out_rel context
            (context.vmax + 1) live destination destinationCode destinationExp
            destinationTmp destinationLive hD
          have ⟨hOkSrc, hTmpSrc, hLiveSrc⟩ := compile_exp_out_rel context
            destinationTmp destinationLive sourceExp sourceCode sourceCompiledExp
            sourceTmp sourceLive hS
          obtain ⟨secondExtra, afterSource, hSecond, hSourceValue,
            hState2, hMem2, hGlobals2, hCode2, hLocals2⟩ :=
            crepToLoop_comp_exp_preserves_eval sourceState sourceExp value afterDestination
              context destinationTmp destinationLive sourceCode sourceCompiledExp sourceTmp
              sourceLive ⟨hSrc, hState1, hMem1, hGlobals1, hCode1, hLocals1, hS,
                by
                  obtain ⟨_, hTmp, _⟩ := compile_exp_out_rel context (context.vmax + 1)
                    live destination destinationCode destinationExp destinationTmp destinationLive hD
                  omega⟩
          -- The second compiled expression writes only in its fresh range, so
          -- it leaves the already evaluated destination address unchanged.
          have hAddressAfterSource : eval afterSource destinationExp = some (.word address) := by
            have hDestinationAssigned : ∀ n,
                n ∈ holLoopAssignedVars (loopNestedSeqHOL destinationCode) →
                  n < destinationTmp := by
              intro n hn
              exact (comp_exp_assigned_vars_tmp_bound context (context.vmax + 1) live
                destination destinationCode destinationExp destinationTmp destinationLive n
                ⟨hD, hn⟩).2
            have hSourceAssigned : ∀ n,
                n ∈ holLoopAssignedVars (loopNestedSeqHOL sourceCode) →
                  destinationTmp ≤ n := by
              intro n hn
              exact (comp_exp_assigned_vars_tmp_bound context destinationTmp destinationLive
                sourceExp sourceCode sourceCompiledExp sourceTmp sourceLive n
                ⟨hS, hn⟩).1
            have hTouch : ∀ n, n ∈ holLoopLocalsTouched destinationExp →
                n < destinationTmp ∧ sptMem n (cutSetsHOL live (loopNestedSeqHOL destinationCode)) := by
              intro n hn
              have hVars : ∀ varName, varName ∈ crepExpVarsHOL destination →
                  ∃ mapped, context.vars.lookup varName = some mapped ∧
                    sptMem mapped live := by
                intro varName hVariable
                obtain ⟨_, hWord⟩ := crepEval_some_var_cexp_local_lookup
                  sourceState destination (.word address) varName ⟨hDst, hVariable⟩
                obtain ⟨mapped, hMapped, hLive, _⟩ :=
                  hLocals.2.2.2 varName _ hWord
                exact ⟨mapped, hMapped, hLive⟩
              obtain ⟨_, hVars⟩ := compile_exp_le_tmp_domain context
                (context.vmax + 1) live destination destinationCode destinationExp
                destinationTmp destinationLive n
                ⟨hLocals.2.1, hD, Nat.lt_succ_self _, hVars, hn⟩
              exact ⟨by omega,
                (sptMem_iff_lookup _ _).mpr (Option.isSome_iff_exists.mp
                  (by simpa [hLiveDst] using hVars))⟩
            have hFirstClock : evaluate (loopNestedSeqHOL destinationCode)
                { target with clock := firstExtra + target.clock } = (none, afterDestination) := by
              simpa [Nat.add_comm] using hFirst
            have hSecondClock : evaluate (loopNestedSeqHOL sourceCode)
                { afterDestination with clock := secondExtra + afterDestination.clock } =
                  (none, afterSource) := by
              simpa [Nat.add_comm] using hSecond
            exact LoopSemStateFiniteExact.nested_seq_pure_evaluation
              destinationCode sourceCode target afterSource afterDestination live destinationTmp
              destinationExp (.word address) firstExtra secondExtra
              ⟨hFirstClock, hSecondClock, hOkDst,
                by simpa [hLiveDst] using hOkSrc,
                hDestinationAssigned, hSourceAssigned, hTouch, hDestinationValue⟩
          have hTargetDomain : afterSource.mdomain address = true := by
            have hRel := congrFun hState2.1 address
            simpa [hRel] using hSourceDomain
          let tail : List (HolLoopProg width) :=
            [.assign sourceTmp sourceCompiledExp, .store destinationExp sourceTmp]
          let afterStore : LoopSemStateFiniteExact width σ :=
            { afterSource with
              locals := sptInsert sourceTmp (wlabWlocExact value) afterSource.locals
              memory :=
              fun current => if current = address then wlabWlocExact value else afterSource.memory current }
          let afterAssign : LoopSemStateFiniteExact width σ :=
            { afterSource with locals := sptInsert sourceTmp (wlabWlocExact value) afterSource.locals }
          have hAddressAfterAssign : eval afterAssign destinationExp = some (.word address) := by
            rw [LoopSemStateFiniteExact.locals_touched_eq_eval_eq afterSource destinationExp afterAssign
              ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => ?_⟩]
            · exact hAddressAfterSource
            · have hVars : ∀ varName, varName ∈ crepExpVarsHOL destination →
                ∃ mapped, context.vars.lookup varName = some mapped ∧ sptMem mapped live := by
                intro varName hVariable
                obtain ⟨_, hWord⟩ := crepEval_some_var_cexp_local_lookup
                  sourceState destination (.word address) varName ⟨hDst, hVariable⟩
                obtain ⟨mapped, hMapped, hLive, _⟩ :=
                  hLocals.2.2.2 varName _ hWord
                exact ⟨mapped, hMapped, hLive⟩
              obtain ⟨hBound, _⟩ := compile_exp_le_tmp_domain context
                (context.vmax + 1) live destination destinationCode destinationExp
                destinationTmp destinationLive n
                ⟨hLocals.2.1, hD, Nat.lt_succ_self _, hVars, hn⟩
              have hNe : n ≠ sourceTmp := by omega
              simp [afterAssign, sptLookup_sptInsert, hNe]
          have hAssign : evaluate (loopNestedSeqHOL [.assign sourceTmp sourceCompiledExp])
              afterSource = (none, afterAssign) := by
            simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              LoopSemStateFiniteExact.evaluate,
              LoopSemStateFiniteExact.setVar, hSourceValue, afterAssign]
          have hStoreTail : evaluate (loopNestedSeqHOL [.store destinationExp sourceTmp])
              afterAssign = (none, afterStore) := by
            simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              LoopSemStateFiniteExact.evaluate,
              LoopSemStateFiniteExact.memStore, hAddressAfterAssign,
              hTargetDomain, afterAssign, afterStore, sptLookup_sptInsert]
          have hTail : evaluate (loopNestedSeqHOL tail) afterSource = (none, afterStore) := by
            change evaluate (loopNestedSeqHOL ([.assign sourceTmp sourceCompiledExp] ++
              [.store destinationExp sourceTmp])) afterSource = (none, afterStore)
            rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none
              [.assign sourceTmp sourceCompiledExp] afterSource afterAssign
              [.store destinationExp sourceTmp] hAssign]
            exact hStoreTail
          have hFirstLift :
              evaluate (loopNestedSeqHOL destinationCode)
                { target with clock := target.clock + (firstExtra + secondExtra) } =
                  (none, { afterDestination with clock := afterDestination.clock + secondExtra }) := by
            have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
              (loopNestedSeqHOL destinationCode)
              { target with clock := target.clock + firstExtra }
              none afterDestination secondExtra hFirst (by simp)
            simpa [Nat.add_assoc] using hLift
          have hRun :
              evaluate (loopNestedSeqHOL (destinationCode ++ sourceCode ++ tail))
                { target with clock := target.clock + (firstExtra + secondExtra) } =
                  (none, afterStore) := by
            rw [List.append_assoc]
            rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none
              destinationCode _ _ (sourceCode ++ tail) hFirstLift]
            rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none
              sourceCode _ afterSource tail hSecond]
            exact hTail
          have hCompile : compileHOLExact context live (.store destination sourceExp) =
              loopNestedSeqHOL (destinationCode ++ sourceCode ++ tail) := by
            simp [compileHOLExact, hD, hS, tail]
          have hStateFinal : crepToLoopStateRelExact sourceFinal afterStore := by
            rw [hSourceFinal]
            simpa only [crepToLoopStateRelExact] using hState2
          have hGlobalsFinal : crepToLoopGlobalsRelHOLExact sourceFinal.globals afterStore.globals := by
            rw [hSourceFinal]
            simpa only [crepToLoopGlobalsRelHOLExact] using hGlobals2
          have hCodeFinal : crepToLoopCodeRelExact context sourceFinal.code afterStore.code := by
            rw [hSourceFinal]
            simpa only [crepToLoopCodeRelExact] using hCode2
          have hMemFinal : crepToLoopMemRelHOLExact sourceFinal.memory
              afterStore.memory sourceFinal.memaddrs := by
            rw [hSourceFinal]
            intro current hCurrent
            change sourceState.memaddrs current at hCurrent
            change wlabWlocExact (sourceMemory current) = afterStore.memory current
            by_cases hEq : current = address
            · subst current
              simp [afterStore, hSourceMemory]
            · have hSourceLookup : sourceMemory current = sourceState.memory current := by
                rw [hSourceMemory]
                simp [hEq]
              have hTargetLookup : afterStore.memory current = afterSource.memory current := by
                simp [afterStore, hEq]
              rw [hSourceLookup, hTargetLookup]
              exact hMem2 current hCurrent
          have hsub : sptSubspt live sourceLive := by
            have hCombined := compSyntaxOk_append live destinationCode sourceCode hOkDst
              (by simpa [hLiveDst] using hOkSrc)
            have hCut := comp_syn_impl_cut_sets_subspt _ live hCombined
            rw [cut_sets_nested_seq, ← hLiveDst, ← hLiveSrc] at hCut
            exact hCut
          have hLocalsStore :
              crepToLoopLocalsRelExact context sourceLive sourceState.locals afterStore.locals := by
            apply crepToLoopLocalsRelExact_insert_gt_vmax context sourceLive sourceState.locals
              afterSource.locals sourceTmp (wlabWlocExact value) hLocals2
            omega
          have hLocalsFinal :
              crepToLoopLocalsRelExact context live sourceFinal.locals afterStore.locals := by
            rw [hSourceFinal]
            exact crepToLoopLocalsRelExact_cutset_prop context live sourceLive
              sourceState.locals target.locals afterStore.locals hLocals hLocalsStore hsub
          refine ⟨firstExtra + secondExtra, none, afterStore, ?_, hStateFinal,
            hMemFinal, hGlobalsFinal, hCodeFinal, ?_, ?_⟩
          · simpa [hCompile] using hRun
          · simp [hResultNone, resultToLoop]
          · simpa [hResultNone, localsResultRel] using hLocalsFinal

end Flapjack
