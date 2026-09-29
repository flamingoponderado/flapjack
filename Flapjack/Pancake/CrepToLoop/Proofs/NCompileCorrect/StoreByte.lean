import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# The `StoreByte` case of `crep_to_loop`'s `ncompile_correct`

This is the constructor case resumed at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:1966-2074`. The destination
and source expressions compile in sequence, after which the target stores the
address and byte in adjacent temporaries before executing `StoreByte`.
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
/-- Genuine `StoreByte dst src` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1966-2074`).
    `evaluate_ind` gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_storeByte {width : Nat} [NeZero width] {σ : Type} :
    ∀ (destination sourceExp : CrepExpHOL width) (sourceState : CrepSemHOLState width σ)
      (result : Option (CrepResultHOLExact width)) (sourceFinal : CrepSemHOLState width σ)
      (target : LoopSemStateFiniteExact width σ) (context : CrepToLoopContextExact)
      (live : NumSet),
      evalCrepSemHOLProgExact sourceState (.storeByte destination sourceExp) = (result, sourceFinal) ∧
        result ≠ some .error ∧ crepToLoopStateRelExact sourceState target ∧
        crepToLoopMemRelHOLExact sourceState.memory target.memory sourceState.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceState.globals target.globals ∧
        crepToLoopCodeRelExact context sourceState.code target.code ∧
        crepToLoopLocalsRelExact context live sourceState.locals target.locals →
      ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
        (targetFinal : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact context live
            (.storeByte destination sourceExp))
          { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
        crepToLoopStateRelExact sourceFinal targetFinal ∧
        crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
        crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
        targetResult = resultToLoop result ∧
        localsResultRel context live result sourceFinal targetFinal := by
  intro destination sourceExp sourceState result sourceFinal target context live
    ⟨hEval, hNotError, hState, hMem, hGlobals, hCode, hLocals⟩
  rw [evalCrepSemHOLProgExact_storeByte_holShape] at hEval
  cases hDst : evalCrepSemHOLExp sourceState destination with
  | none => simp [hDst] at hEval; exact absurd hEval.1.symm hNotError
  | some dstValue =>
    cases dstValue with
    | word address =>
      cases hSrc : evalCrepSemHOLExp sourceState sourceExp with
      | none => simp [hDst, hSrc] at hEval; exact absurd hEval.1.symm hNotError
      | some sourceValue =>
        cases sourceValue with
        | word byteValue =>
        cases hStore : panMemStoreByteWord8HOL sourceState.memory sourceState.memaddrs
            sourceState.be address (BitVec.ofNat 8 byteValue.toNat) with
        | none =>
          simp only [hDst, hSrc] at hEval
          rw [hStore] at hEval
          simp only [Prod.mk.injEq] at hEval
          exact absurd hEval.1.symm hNotError
        | some sourceMemory =>
          let aligned := panByteAlignHOL address
          let byteValue8 : BitVec 8 := BitVec.ofNat 8 byteValue.toNat
          have hSourceDomain : sourceState.memaddrs aligned := by
            by_cases hDomain : sourceState.memaddrs aligned
            · exact hDomain
            · simp [panMemStoreByteWord8HOL, aligned, hDomain] at hStore
          have hSourceCell : ∃ cell, sourceState.memory aligned = .word cell := by
            cases hCell : sourceState.memory aligned with
            | word cell => exact ⟨cell, rfl⟩
          obtain ⟨cell, hCell⟩ := hSourceCell
          have hSourceMemory : sourceMemory =
              fun current => if current = aligned then
                .word (panSetByteHOL address (BitVec.ofNat width byteValue8.toNat)
                  cell sourceState.be)
                else sourceState.memory current := by
            have h := hStore
            simp [panMemStoreByteWord8HOL, aligned, hCell, hSourceDomain] at h
            simpa [hCell, byteValue8] using h.symm
          simp only [hDst, hSrc] at hEval
          rw [hStore] at hEval
          simp only [Prod.mk.injEq] at hEval
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
            crepToLoop_comp_exp_preserves_eval sourceState sourceExp (.word byteValue) afterDestination
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
          have hTargetDomain : afterSource.mdomain (riscvByteAlignHOL address) = true := by
            have hRel := congrFun hState2.1 (panByteAlignHOL address)
            change sourceState.memaddrs (panByteAlignHOL address) =
              (afterSource.mdomain (panByteAlignHOL address) = true) at hRel
            have hDomainPan : afterSource.mdomain (panByteAlignHOL address) = true := by
              rw [← hRel]
              exact hSourceDomain
            rw [riscvByteAlignHOL_eq_panByteAlignHOL]
            exact hDomainPan
          have hTargetCell : ∃ cell, afterSource.memory (riscvByteAlignHOL address) = .word cell := by
            have hAt := hMem2 (panByteAlignHOL address) hSourceDomain
            rw [hCell] at hAt
            cases hTarget : afterSource.memory (panByteAlignHOL address) with
            | word targetCell =>
              refine ⟨targetCell, ?_⟩
              rw [riscvByteAlignHOL_eq_panByteAlignHOL]
              exact hTarget
            | loc name offset => simp [hTarget, wlabWlocExact] at hAt
          obtain ⟨targetCell, hTargetCell⟩ := hTargetCell
          have hTargetMemory :
              memStoreByteAuxExact afterSource.memory afterSource.mdomain afterSource.be
                address (byteValue.setWidth 8) = some
                  (fun current => if current = riscvByteAlignHOL address then
                    .word (setByteHOL8 address (byteValue.setWidth 8) targetCell afterSource.be)
                    else afterSource.memory current) := by
            unfold memStoreByteAuxExact
            rw [hTargetCell, hTargetDomain]
            rfl
          let tail : List (HolLoopProg width) :=
            [.assign sourceTmp destinationExp, .assign (sourceTmp + 1) sourceCompiledExp,
              .storeByte sourceTmp (sourceTmp + 1)]
          let afterAddress : LoopSemStateFiniteExact width σ :=
            LoopSemStateFiniteExact.setVar sourceTmp (.word address) afterSource
          let afterValue : LoopSemStateFiniteExact width σ :=
            LoopSemStateFiniteExact.setVar (sourceTmp + 1) (.word byteValue) afterAddress
          let targetMemory : BitVec width → WordLocW width := fun current =>
            if current = riscvByteAlignHOL address then
              .word (setByteHOL8 address (byteValue.setWidth 8) targetCell afterSource.be)
            else afterSource.memory current
          let afterStore : LoopSemStateFiniteExact width σ :=
            { afterValue with memory := targetMemory }
          have hAddressAfterAssignments : eval afterValue destinationExp = some (.word address) := by
            rw [LoopSemStateFiniteExact.locals_touched_eq_eval_eq afterSource destinationExp afterValue
              ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => ?_⟩]
            · exact hAddressAfterSource
            · have hVars : ∀ varName, varName ∈ crepExpVarsHOL destination →
                ∃ mapped, context.vars.lookup varName = some mapped ∧ sptMem mapped live := by
                intro varName hVariable
                obtain ⟨_, hWord⟩ := crepEval_some_var_cexp_local_lookup
                  sourceState destination (.word address) varName ⟨hDst, hVariable⟩
                obtain ⟨mapped, hMapped, hLive, _⟩ := hLocals.2.2.2 varName _ hWord
                exact ⟨mapped, hMapped, hLive⟩
              obtain ⟨hBound, _⟩ := compile_exp_le_tmp_domain context
                (context.vmax + 1) live destination destinationCode destinationExp
                destinationTmp destinationLive n ⟨hLocals.2.1, hD, Nat.lt_succ_self _, hVars, hn⟩
              have hNe1 : n ≠ sourceTmp := by omega
              have hNe2 : n ≠ sourceTmp + 1 := by omega
              simp [afterValue, afterAddress, LoopSemStateFiniteExact.setVar,
                sptLookup_sptInsert, hNe1, hNe2]
          have hSourceVars : ∀ varName, varName ∈ crepExpVarsHOL sourceExp →
              ∃ mapped, context.vars.lookup varName = some mapped ∧ sptMem mapped destinationLive := by
            intro varName hVariable
            obtain ⟨_, hWord⟩ := crepEval_some_var_cexp_local_lookup
              sourceState sourceExp (.word byteValue) varName ⟨hSrc, hVariable⟩
            obtain ⟨mapped, hMapped, hLive, _⟩ := hLocals1.2.2.2 varName _ hWord
            exact ⟨mapped, hMapped, hLive⟩
          have hSourceTouched : ∀ n, n ∈ holLoopLocalsTouched sourceCompiledExp → n < sourceTmp := by
            intro n hn
            obtain ⟨hBound, _⟩ := compile_exp_le_tmp_domain context destinationTmp destinationLive
              sourceExp sourceCode sourceCompiledExp sourceTmp sourceLive n
              ⟨hLocals.2.1, hS, by omega, hSourceVars, hn⟩
            exact hBound
          have hSourceValueAfterAddress :
              eval afterAddress sourceCompiledExp = some (.word byteValue) := by
            rw [LoopSemStateFiniteExact.locals_touched_eq_eval_eq afterSource sourceCompiledExp afterAddress
              ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => ?_⟩]
            · exact hSourceValue
            · have hnBound := hSourceTouched n hn
              have hNe : n ≠ sourceTmp := by omega
              simp [afterAddress, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, hNe]
          have hAssignAddress : evaluate (loopNestedSeqHOL [.assign sourceTmp destinationExp])
              afterSource = (none, afterAddress) := by
            simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              LoopSemStateFiniteExact.evaluate, hAddressAfterSource, afterAddress]
          have hAssignValue : evaluate (loopNestedSeqHOL [.assign (sourceTmp + 1) sourceCompiledExp])
              afterAddress = (none, afterValue) := by
            simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              LoopSemStateFiniteExact.evaluate, hSourceValueAfterAddress,
              afterValue, LoopSemStateFiniteExact.setVar]
          have hStoreTail : evaluate (loopNestedSeqHOL [.storeByte sourceTmp (sourceTmp + 1)])
              afterValue = (none, afterStore) := by
            simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              LoopSemStateFiniteExact.evaluate, hTargetMemory, afterStore, afterValue,
              afterAddress, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
            rfl
          have hAssigns : evaluate (loopNestedSeqHOL
              ([.assign sourceTmp destinationExp, .assign (sourceTmp + 1) sourceCompiledExp] ++
                [.storeByte sourceTmp (sourceTmp + 1)])) afterSource = (none, afterStore) := by
            change evaluate (loopNestedSeqHOL
              ([.assign sourceTmp destinationExp] ++
                ([.assign (sourceTmp + 1) sourceCompiledExp] ++ [.storeByte sourceTmp (sourceTmp + 1)]))
              )
              afterSource = (none, afterStore)
            have hAppend1 := LoopSemStateFiniteExact.evaluate_nested_seq_append_none
              [.assign sourceTmp destinationExp] afterSource afterAddress
              ([.assign (sourceTmp + 1) sourceCompiledExp] ++ [.storeByte sourceTmp (sourceTmp + 1)])
              hAssignAddress
            have hAppend2 := LoopSemStateFiniteExact.evaluate_nested_seq_append_none
                [.assign (sourceTmp + 1) sourceCompiledExp] afterAddress afterValue
                [.storeByte sourceTmp (sourceTmp + 1)] hAssignValue
            exact hAppend1.trans (hAppend2.trans hStoreTail)
          have hTail : evaluate (loopNestedSeqHOL tail) afterSource = (none, afterStore) := by
            simpa [tail] using hAssigns
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
          have hCompile : compileHOLExact context live (.storeByte destination sourceExp) =
              loopNestedSeqHOL (destinationCode ++ sourceCode ++ tail) := by
            simp [compileHOLExact, hD, hS, tail]
          have hStateFinal : crepToLoopStateRelExact sourceFinal afterStore := by
            rw [hSourceFinal]
            change crepToLoopStateRelExact sourceState afterSource
            exact hState2
          have hGlobalsFinal : crepToLoopGlobalsRelHOLExact sourceFinal.globals afterStore.globals := by
            simpa [hSourceFinal, crepToLoopGlobalsRelHOLExact, afterStore, afterValue, afterAddress,
              LoopSemStateFiniteExact.setVar] using hGlobals2
          have hCodeFinal : crepToLoopCodeRelExact context sourceFinal.code afterStore.code := by
            simpa [hSourceFinal, crepToLoopCodeRelExact, afterStore, afterValue, afterAddress,
              LoopSemStateFiniteExact.setVar] using hCode2
          have hMemFinal : crepToLoopMemRelHOLExact sourceFinal.memory
              afterStore.memory sourceFinal.memaddrs := by
            rw [hSourceFinal]
            have hDomain : sourceState.memaddrs = fun a => afterSource.mdomain a = true := hState2.1
            have hBe : sourceState.be = afterSource.be := hState2.2.2.2.1
            have hWrite := write_bytearray_mem_rel [byteValue8] sourceState.memory
              afterSource.memory address afterSource.mdomain afterSource.be
              (by simpa [hDomain] using hMem2)
            intro current hCurrent
            have hWriteAt := hWrite current (by simpa [hDomain] using hCurrent)
            have hByte : BitVec.setWidth 8 byteValue = byteValue8 := by
              apply BitVec.eq_of_toNat_eq
              simp [byteValue8]
            have hSourceWrite :
                panWriteBytearrayWord8HOL address [byteValue8] sourceState.memory
                  sourceState.memaddrs sourceState.be current = sourceMemory current := by
              simp only [panWriteBytearrayWord8HOL]
              rw [hStore]
            have hSourceWrite' :
                panWriteBytearrayWord8HOL address [byteValue8] sourceState.memory
                  (fun a => afterSource.mdomain a = true) afterSource.be current = sourceMemory current := by
              rw [hBe] at hSourceWrite
              simpa [hDomain] using hSourceWrite
            have hTargetWrite :
                writeBytearrayExact address [byteValue8] afterSource.memory
                  afterSource.mdomain afterSource.be current = afterStore.memory current := by
              have hTargetStore : memStoreByteAuxExact afterSource.memory afterSource.mdomain
                  afterSource.be address byteValue8 = some targetMemory := by
                rw [← hByte]
                simpa [targetMemory] using hTargetMemory
              simp only [writeBytearrayExact, hTargetStore, afterStore]
            change wlabWlocExact (sourceMemory current) = afterStore.memory current
            calc
              wlabWlocExact (sourceMemory current) =
                  wlabWlocExact (panWriteBytearrayWord8HOL address [byteValue8] sourceState.memory
                    (fun a => afterSource.mdomain a = true) afterSource.be current) := by
                rw [hSourceWrite']
              _ = writeBytearrayExact address [byteValue8] afterSource.memory afterSource.mdomain
                    afterSource.be current := hWriteAt
              _ = afterStore.memory current := hTargetWrite
          have hsub : sptSubspt live sourceLive := by
            have hCombined := compSyntaxOk_append live destinationCode sourceCode hOkDst
              (by simpa [hLiveDst] using hOkSrc)
            have hCut := comp_syn_impl_cut_sets_subspt _ live hCombined
            rw [cut_sets_nested_seq, ← hLiveDst, ← hLiveSrc] at hCut
            exact hCut
          have hLocalsAfterAddress :
              crepToLoopLocalsRelExact context sourceLive sourceState.locals afterAddress.locals := by
            apply crepToLoopLocalsRelExact_insert_gt_vmax context sourceLive sourceState.locals
              afterSource.locals sourceTmp (wlabWlocExact (.word address)) hLocals2
            omega
          have hLocalsStore :
              crepToLoopLocalsRelExact context sourceLive sourceState.locals afterStore.locals := by
            apply crepToLoopLocalsRelExact_insert_gt_vmax context sourceLive sourceState.locals
              afterAddress.locals (sourceTmp + 1) (wlabWlocExact (.word byteValue)) hLocalsAfterAddress
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
