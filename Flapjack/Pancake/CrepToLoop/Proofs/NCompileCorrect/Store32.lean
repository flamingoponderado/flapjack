import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.CrepToLoop.Proofs.CrepEvalHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Pancake.Semantics.PanSem.MemStore32Alt

/-!
# The `Store32` case of `crep_to_loop`'s `ncompile_correct`

This is the source case resumed at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:1857-1965`. It relies on the
two expression induction hypotheses from `evaluate_ind`, exact expression
preservation, and the source/target `mem_store_32` byte-update equations.
-/

namespace Flapjack

open LoopSemStateFiniteExact
open Pancake.CrepToLoop.Proofs.NCompileCorrect

namespace NCompileCorrectStore32FmapWitnesses

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

end NCompileCorrectStore32FmapWitnesses

private theorem panGetByte32_eq_wordGetByte32 (index : Nat) (hindex : index < 4)
    (value : BitVec 32) (bigEndian : Bool) :
    (panGetByteHOL (BitVec.ofNat 32 index) value bigEndian).toNat =
      (getByteHOL8 (BitVec.ofNat 32 index) value bigEndian).toNat := by
  rw [panGetByteHOL32_toNat index hindex value bigEndian]
  cases bigEndian <;>
    simp [getByteHOL8, byteIndexHOL, Nat.mod_eq_of_lt hindex]

private theorem store32ByteWord8 (index : Nat) (hindex : index < 4)
    (value : BitVec 32) (bigEndian : Bool) :
    (value.toNat >>> (8 * (if bigEndian then 3 - index else index))) % 256 =
      (getByteHOL8 (BitVec.ofNat 32 index) value bigEndian).toNat := by
  rw [← panGetByteHOL32_toNat index hindex value bigEndian]
  exact panGetByte32_eq_wordGetByte32 index hindex value bigEndian

private theorem panStore32Cell_chain_eq_wordStore32Cell_chain {width : Nat} [NeZero width]
    (address : BitVec width) (bigEndian : Bool) (value : BitVec 32)
    (cell : BitVec width) :
    store32Alt address bigEndian value cell =
      let v0 := setByteHOL8 address (getByteHOL8 (0 : BitVec 32) value bigEndian) cell bigEndian
      let v1 := setByteHOL8 (address + 1) (getByteHOL8 (1 : BitVec 32) value bigEndian) v0 bigEndian
      let v2 := setByteHOL8 (address + 2) (getByteHOL8 (2 : BitVec 32) value bigEndian) v1 bigEndian
      setByteHOL8 (address + 3) (getByteHOL8 (3 : BitVec 32) value bigEndian) v2 bigEndian := by
  simp only [store32Alt]
  simp only [store32ByteWord8 0 (by decide) value bigEndian,
    store32ByteWord8 1 (by decide) value bigEndian,
    store32ByteWord8 2 (by decide) value bigEndian,
    store32ByteWord8 3 (by decide) value bigEndian]
  rw [panSetByteHOL_eq_setByteHOL8, panSetByteHOL_eq_setByteHOL8,
    panSetByteHOL_eq_setByteHOL8, panSetByteHOL_eq_setByteHOL8]
  simp

private theorem store32_aligned_iff {width : Nat} (address : BitVec width) :
    riscvAlignedHOL 2 address = true ↔ address.toNat % 4 = 0 := by
  have hlt : address.toNat / 4 * 4 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) address.isLt
  have key : ((address >>> (2 : Nat)) <<< (2 : Nat)).toNat =
      address.toNat / 4 * 4 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt hlt
  simp only [riscvAlignedHOL, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [key] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [key]
    omega

private theorem crepToLoopMemStore32RelExact {width : Nat} [NeZero width]
    (smem : BitVec width → HolWordLab width) (tm : BitVec width → WordLocW width)
    (dom : BitVec width → Prop) [DecidablePred dom]
    (tdom : BitVec width → Bool) (be : Bool) (address : BitVec width)
    (sourceValue targetValue : BitVec 32)
    (smem' : BitVec width → HolWordLab width) (tm' : BitVec width → WordLocW width)
    (hdom : dom = fun a => tdom a = true)
    (hm : crepToLoopMemRelHOLExact smem tm dom)
    (hSourceStore : panMemStore32HOL smem dom be address sourceValue = some smem')
    (hTargetStore : memStore32Exact tm tdom be address targetValue = some tm')
    (hValues : sourceValue = targetValue) :
    crepToLoopMemRelHOLExact smem' tm' dom := by
  rw [panMemStore32HOL_eq_alt] at hSourceStore
  unfold memStore32Exact at hTargetStore
  have hAligned : address.toNat % 4 = 0 := by
    by_cases h : address.toNat % 4 = 0
    · exact h
    · simp [h] at hSourceStore
  have hTargetAligned : riscvAlignedHOL 2 address = true :=
    (store32_aligned_iff address).2 hAligned
  let aligned := panByteAlignHOL address
  cases hCellSource : smem aligned with
  | word cell =>
      have hSourceSuccess : dom aligned ∧
          (fun current => if current = aligned then
            HolWordLab.word (store32Alt address be sourceValue cell) else smem current) = smem' := by
        by_cases hDomain : dom aligned
        · constructor
          · exact hDomain
          · simpa [hAligned, aligned, hCellSource, hDomain] using hSourceStore
        · simp [hAligned, aligned, hDomain] at hSourceStore
      have hDomain : dom aligned := hSourceSuccess.1
      have hDomain : dom aligned := hSourceSuccess.1
      have hCellTarget : tm aligned = .word cell := by
        have hrel := hm aligned hDomain
        rw [hCellSource, wlabWlocExact] at hrel
        exact hrel.symm
      have hTargetDomain : tdom aligned = true := by
        simpa [hdom] using hDomain
      have hTargetEq :
          tm (riscvByteAlignHOL address) = .word cell := by
        rw [riscvByteAlignHOL_eq_panByteAlignHOL]
        exact hCellTarget
      have hSourceOut : smem' = fun current =>
          if current = aligned then
            .word (store32Alt address be sourceValue cell)
          else smem current := hSourceSuccess.2.symm
      let updated := setByteHOL8 (address + 3)
          (getByteHOL8 (3 : BitVec 32) targetValue be)
          (setByteHOL8 (address + 2)
            (getByteHOL8 (2 : BitVec 32) targetValue be)
            (setByteHOL8 (address + 1)
              (getByteHOL8 (1 : BitVec 32) targetValue be)
              (setByteHOL8 address (getByteHOL8 (0 : BitVec 32) targetValue be)
                cell be) be) be) be
      have hTargetOut : tm' = fun current =>
          if current = aligned then
            .word updated
          else tm current := by
        have hTargetStoreCell := hTargetStore
        rw [hTargetEq] at hTargetStoreCell
        have hTargetOption : some tm' = some (fun current =>
            if current = aligned then WordLocW.word updated else tm current) := by
          simpa [memStore32Exact, updated, hTargetAligned, aligned,
            hTargetDomain, riscvByteAlignHOL_eq_panByteAlignHOL] using hTargetStoreCell.symm
        exact Option.some.inj hTargetOption
      intro a ha
      rw [hSourceOut, hTargetOut]
      by_cases hsame : a = aligned
      · subst a
        simp only
        have hcell : wlabWlocExact (.word (store32Alt address be sourceValue cell)) =
            WordLocW.word updated := by
          change WordLocW.word (store32Alt address be sourceValue cell) =
            WordLocW.word (setByteHOL8 (address + 3)
              (getByteHOL8 (3 : BitVec 32) targetValue be)
              (setByteHOL8 (address + 2)
                (getByteHOL8 (2 : BitVec 32) targetValue be)
                (setByteHOL8 (address + 1)
                  (getByteHOL8 (1 : BitVec 32) targetValue be)
                  (setByteHOL8 address (getByteHOL8 (0 : BitVec 32) targetValue be)
                    cell be) be) be) be)
          rw [hValues]
          exact congrArg WordLocW.word
            (panStore32Cell_chain_eq_wordStore32Cell_chain address be targetValue cell)
        exact hcell
      · simp only [if_neg hsame]
        exact hm a ha

/-- Genuine `Store32 dst src` constructor case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1857-1965`). This
    retains the exact source evaluator, all seven HOL premises, and the full
    existential target run and postconditions. The tagged evaluators use the
    exact finite-word carriers; the byte-chain bridge above compares HOL's
    `mem_store_32_alt` with the Loop evaluator's four `set_byte` updates. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_store32 {width : Nat} [NeZero width]
    {σ : Type} :
    ∀ (destination source : CrepExpHOL width)
      (sourceState : CrepSemHOLState width σ)
      (result : Option (CrepResultHOLExact width))
      (sourceFinal : CrepSemHOLState width σ)
      (target : LoopSemStateFiniteExact width σ)
      (context : CrepToLoopContextExact) (live : NumSet),
      evalCrepSemHOLProgExact sourceState (.store32 destination source) =
          (result, sourceFinal) ∧ result ≠ some .error ∧
        crepToLoopStateRelExact sourceState target ∧
        crepToLoopMemRelHOLExact sourceState.memory target.memory sourceState.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceState.globals target.globals ∧
        crepToLoopCodeRelExact context sourceState.code target.code ∧
        crepToLoopLocalsRelExact context live sourceState.locals target.locals →
      ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
        (targetFinal : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate
            (compileHOLExact context live (.store32 destination source))
            { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
        crepToLoopStateRelExact sourceFinal targetFinal ∧
        crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
        crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
        crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
        targetResult = resultToLoop result ∧
        localsResultRel context live result sourceFinal targetFinal := by
  intro destination source sourceState result sourceFinal target context live
    ⟨hEval, hNotError, hState, hMem, hGlobals, hCode, hLocals⟩
  classical
  rw [evalCrepSemHOLProgExact_store32_holShape] at hEval
  cases hDestination : evalCrepSemHOLExp sourceState destination with
  | none =>
      simp [hDestination] at hEval
      exact False.elim (hNotError hEval.1.symm)
  | some destinationValue =>
    cases destinationValue with
    | word address =>
      cases hSourceValue : evalCrepSemHOLExp sourceState source with
      | none =>
          simp [hDestination, hSourceValue] at hEval
          exact False.elim (hNotError hEval.1.symm)
      | some sourceWord =>
        cases sourceWord with
        | word value =>
          cases hSourceStore : panMemStore32HOL sourceState.memory
              sourceState.memaddrs sourceState.be address
              (BitVec.setWidth 32 value) with
          | none =>
              simp [hDestination, hSourceValue, hSourceStore] at hEval
              exact False.elim (hNotError hEval.1.symm)
          | some sourceMemory' =>
            have hEvalReduced :
                (none, { sourceState with memory := sourceMemory' }) =
                  (result, sourceFinal) := by
              simpa [hDestination, hSourceValue, hSourceStore] using hEval
            rcases Prod.mk.inj hEvalReduced with ⟨hResult, hSourceFinal⟩
            subst result
            subst sourceFinal
            rcases destinationCompile : compileExpHOLExact context
                (context.vmax + 1) live destination with
              ⟨destinationCode, destinationLoopExp, destinationTmp, destinationLive⟩
            obtain ⟨destinationClock, afterDestination, hDestinationRun,
              hDestinationValue, hDestinationState, hDestinationMem,
              hDestinationGlobals, hDestinationCodeRel, hDestinationLocals⟩ :=
              crepToLoop_comp_exp_preserves_eval sourceState destination
                (.word address) target context (context.vmax + 1) live
                destinationCode destinationLoopExp destinationTmp destinationLive
                ⟨hDestination, hState, hMem, hGlobals, hCode, hLocals,
                  destinationCompile, Nat.lt_succ_self _⟩
            obtain ⟨destinationSyntax, destinationTmpBound, destinationLiveEq⟩ :=
              compile_exp_out_rel context (context.vmax + 1) live destination
                destinationCode destinationLoopExp destinationTmp destinationLive
                destinationCompile
            rcases sourceCompile : compileExpHOLExact context destinationTmp
                destinationLive source with
              ⟨sourceCode, sourceLoopExp, sourceTmp, sourceLive⟩
            obtain ⟨sourceClock, afterSource, hSourceRun,
              hSourceLoopValue, hSourceState, hSourceMem, hSourceGlobals,
              hSourceCodeRel, hSourceLocals⟩ :=
              crepToLoop_comp_exp_preserves_eval sourceState source
                (.word value) afterDestination context destinationTmp destinationLive
                sourceCode sourceLoopExp sourceTmp sourceLive
                ⟨hSourceValue, hDestinationState, hDestinationMem,
                  hDestinationGlobals, hDestinationCodeRel, hDestinationLocals,
                  sourceCompile, by omega⟩
            obtain ⟨sourceSyntax, sourceTmpBound, sourceLiveEq⟩ :=
              compile_exp_out_rel context destinationTmp destinationLive source
                sourceCode sourceLoopExp sourceTmp sourceLive sourceCompile
            have hDestinationRunLong :
                LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL destinationCode)
                    { target with clock := target.clock +
                      (destinationClock + sourceClock) } =
                  (none, { afterDestination with clock :=
                    afterDestination.clock + sourceClock }) := by
              have h := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _
                sourceClock hDestinationRun (by simp)
              simpa [Nat.add_assoc] using h
            have hDestinationAfterSource :
                LoopSemStateFiniteExact.eval afterSource destinationLoopExp =
                  some (.word address) := by
              refine LoopSemStateFiniteExact.nested_seq_pure_evaluation
                destinationCode sourceCode target afterSource afterDestination live
                destinationTmp destinationLoopExp (.word address)
                destinationClock sourceClock ⟨?_, ?_, destinationSyntax, ?_, ?_,
                  ?_, ?_, hDestinationValue⟩
              · rw [Nat.add_comm]
                exact hDestinationRun
              · rw [Nat.add_comm]
                exact hSourceRun
              · simpa [destinationLiveEq] using sourceSyntax
              · intro n hn
                exact (comp_exp_assigned_vars_tmp_bound context
                  (context.vmax + 1) live destination destinationCode
                  destinationLoopExp destinationTmp destinationLive n
                  ⟨destinationCompile, hn⟩).2
              · intro n hn
                exact (comp_exp_assigned_vars_tmp_bound context destinationTmp
                  destinationLive source sourceCode sourceLoopExp sourceTmp sourceLive n
                  ⟨sourceCompile, hn⟩).1
              · intro n hn
                have hVars : ∀ k, k ∈ crepExpVarsHOL destination →
                    ∃ mapped, context.vars.lookup k = some mapped ∧
                      (sptLookup mapped live).isSome = true := by
                  intro k hk
                  obtain ⟨sourceValue, hLookup⟩ :=
                    crepEval_some_var_cexp_local_lookup sourceState destination
                      (.word address) k ⟨hDestination, hk⟩
                  obtain ⟨mapped, hMapped, hLive, _⟩ :=
                    hLocals.2.2.2 k sourceValue hLookup
                  exact ⟨mapped, hMapped, hLive⟩
                have hTouched := compile_exp_le_tmp_domain context
                    (context.vmax + 1) live destination destinationCode
                    destinationLoopExp destinationTmp destinationLive n
                    ⟨hLocals.2.1, destinationCompile, Nat.lt_succ_self _, hVars, hn⟩
                exact ⟨hTouched.1, destinationLiveEq ▸ hTouched.2⟩
            have hSourceTmpUntouched : sourceTmp ∉ holLoopLocalsTouched sourceLoopExp := by
              intro hTouched
              have hVars : ∀ k, k ∈ crepExpVarsHOL source →
                  ∃ mapped, context.vars.lookup k = some mapped ∧
                    (sptLookup mapped destinationLive).isSome = true := by
                intro k hk
                obtain ⟨sourceValue, hLookup⟩ :=
                  crepEval_some_var_cexp_local_lookup sourceState source
                    (.word value) k ⟨hSourceValue, hk⟩
                obtain ⟨mapped, hMapped, hLive, _⟩ :=
                  hDestinationLocals.2.2.2 k sourceValue hLookup
                exact ⟨mapped, hMapped, hLive⟩
              have hBound := compile_exp_le_tmp_domain context destinationTmp
                  destinationLive source sourceCode sourceLoopExp sourceTmp sourceLive
                  sourceTmp ⟨hLocals.2.1, sourceCompile, by omega, hVars, hTouched⟩
              omega
            have hSourceAfterAddress :
                LoopSemStateFiniteExact.eval
                    (LoopSemStateFiniteExact.setVar sourceTmp (.word address) afterSource)
                    sourceLoopExp = some (.word value) := by
              have hEvalEq := LoopSemStateFiniteExact.locals_touched_eq_eval_eq
                afterSource sourceLoopExp
                (LoopSemStateFiniteExact.setVar sourceTmp (.word address) afterSource)
                (by
                  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
                  intro n hn
                  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
                  by_cases hne : n = sourceTmp
                  · subst n
                    exact False.elim (hSourceTmpUntouched hn)
                  · simp [hne])
              rw [hEvalEq]
              exact hSourceLoopValue
            let updated := setByteHOL8 (address + 3)
                (getByteHOL8 (3 : BitVec 32) (BitVec.setWidth 32 value) sourceState.be)
                (setByteHOL8 (address + 2)
                  (getByteHOL8 (2 : BitVec 32) (BitVec.setWidth 32 value) sourceState.be)
                  (setByteHOL8 (address + 1)
                    (getByteHOL8 (1 : BitVec 32) (BitVec.setWidth 32 value) sourceState.be)
                    (setByteHOL8 address
                      (getByteHOL8 (0 : BitVec 32) (BitVec.setWidth 32 value) sourceState.be)
                      (sourceState.memory (panByteAlignHOL address)).1 sourceState.be)
                    sourceState.be) sourceState.be) sourceState.be
            let targetMemory' : BitVec width → WordLocW width := fun current =>
              if current = panByteAlignHOL address then .word updated
              else afterSource.memory current
            have hAligned : address.toNat % 4 = 0 := by
              have h := hSourceStore
              rw [panMemStore32HOL_eq_alt] at h
              by_cases hAddress : address.toNat % 4 = 0
              · exact hAddress
              · simp [hAddress] at h
            have hSourceDomain :
                sourceState.memaddrs (panByteAlignHOL address) := by
              have h := hSourceStore
              rw [panMemStore32HOL_eq_alt] at h
              simp only [if_pos hAligned] at h
              cases hCell : sourceState.memory (panByteAlignHOL address) with
              | word cell =>
                by_cases hDomain : sourceState.memaddrs (panByteAlignHOL address)
                · exact hDomain
                · simp [hDomain] at h
            have hTargetDomain : afterSource.mdomain (panByteAlignHOL address) = true := by
              have hdom := congrFun hSourceState.1 (panByteAlignHOL address)
              simpa using hdom.symm ▸ hSourceDomain
            have hTargetCell : afterSource.memory (panByteAlignHOL address) =
                .word (sourceState.memory (panByteAlignHOL address)).1 := by
              have h := hSourceMem (panByteAlignHOL address) hSourceDomain
              simpa [wlabWlocExact] using h.symm
            have hTargetStore : memStore32Exact afterSource.memory afterSource.mdomain
                sourceState.be address (BitVec.setWidth 32 value) = some targetMemory' := by
              have hTargetAligned : riscvAlignedHOL 2 address = true :=
                (store32_aligned_iff address).2 hAligned
              have hbe := hSourceState.2.2.2.1
              unfold memStore32Exact
              simp [hTargetAligned, hTargetCell, hTargetDomain,
                riscvByteAlignHOL_eq_panByteAlignHOL, targetMemory', updated, hbe]
            have hMemAfter := crepToLoopMemStore32RelExact sourceState.memory
                afterSource.memory sourceState.memaddrs afterSource.mdomain
                sourceState.be address (BitVec.setWidth 32 value)
                (BitVec.setWidth 32 value) sourceMemory' targetMemory'
                hSourceState.1 hSourceMem hSourceStore hTargetStore rfl
            let afterAddress := LoopSemStateFiniteExact.setVar sourceTmp
                (.word address) afterSource
            let afterBoth := LoopSemStateFiniteExact.setVar (sourceTmp + 1)
                (.word value) afterAddress
            have hAssignAddress :
                LoopSemStateFiniteExact.evaluate (.assign sourceTmp destinationLoopExp)
                    afterSource = (none, afterAddress) := by
              rw [LoopSemStateFiniteExact.evaluate]
              simp [afterAddress, hDestinationAfterSource]
            have hAssignValue :
                LoopSemStateFiniteExact.evaluate (.assign (sourceTmp + 1) sourceLoopExp)
                    afterAddress = (none, afterBoth) := by
              rw [LoopSemStateFiniteExact.evaluate]
              simp [afterBoth, afterAddress, hSourceAfterAddress]
            have hLookupAddress :
                sptLookup sourceTmp afterBoth.locals = some (.word address) := by
              simp [afterBoth, afterAddress, LoopSemStateFiniteExact.setVar,
                sptLookup_sptInsert]
            have hLookupValue :
                sptLookup (sourceTmp + 1) afterBoth.locals = some (.word value) := by
              simp [afterBoth, afterAddress, LoopSemStateFiniteExact.setVar,
                sptLookup_sptInsert]
            have hTargetStoreAfterBoth :
                memStore32Exact afterBoth.memory afterBoth.mdomain afterBoth.be address
                    (BitVec.setWidth 32 value) = some targetMemory' := by
              have hbe := hSourceState.2.2.2.1
              simpa [afterBoth, afterAddress, LoopSemStateFiniteExact.setVar, hbe] using
                hTargetStore
            have hStoreTarget :
                LoopSemStateFiniteExact.evaluate (.store32 sourceTmp (sourceTmp + 1))
                    afterBoth = (none, { afterBoth with memory := targetMemory' }) := by
              rw [LoopSemStateFiniteExact.evaluate]
              simp only [hLookupAddress, hLookupValue, hTargetStoreAfterBoth]
            let targetFinal := { afterBoth with memory := targetMemory' }
            have hTail : LoopSemStateFiniteExact.evaluate
                (loopNestedSeqHOL
                  [.assign sourceTmp destinationLoopExp,
                   .assign (sourceTmp + 1) sourceLoopExp,
                   .store32 sourceTmp (sourceTmp + 1)]) afterSource =
                (none, targetFinal) := by
              simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
                hAssignAddress, hAssignValue, hStoreTarget,
                LoopSemStateFiniteExact.evaluate]
              rfl
            have hCompile : compileHOLExact context live
                (.store32 destination source) = loopNestedSeqHOL
                  (destinationCode ++ sourceCode ++
                    [.assign sourceTmp destinationLoopExp,
                     .assign (sourceTmp + 1) sourceLoopExp,
                     .store32 sourceTmp (sourceTmp + 1)]) := by
              simp [compileHOLExact, destinationCompile, sourceCompile,
                List.append_assoc]
            have hTargetRun : LoopSemStateFiniteExact.evaluate
                (compileHOLExact context live (.store32 destination source))
                { target with clock := target.clock +
                  (destinationClock + sourceClock) } = (none, targetFinal) := by
              rw [hCompile]
              rw [List.append_assoc]
              have hAppend1 := LoopSemStateFiniteExact.evaluate_nested_seq_append_none
                destinationCode
                { target with clock := target.clock + (destinationClock + sourceClock) }
                { afterDestination with clock := afterDestination.clock + sourceClock }
                (sourceCode ++
                  [.assign sourceTmp destinationLoopExp,
                   .assign (sourceTmp + 1) sourceLoopExp,
                   .store32 sourceTmp (sourceTmp + 1)]) hDestinationRunLong
              rw [hAppend1]
              rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none sourceCode
                _ _ [.assign sourceTmp destinationLoopExp,
                  .assign (sourceTmp + 1) sourceLoopExp,
                  .store32 sourceTmp (sourceTmp + 1)] hSourceRun]
              exact hTail
            have hLiveSub : sptSubspt live sourceLive := by
              have hDestSub : sptSubspt live destinationLive := by
                rw [destinationLiveEq]
                exact comp_syn_impl_cut_sets_subspt _ live destinationSyntax
              have hSourceSub : sptSubspt destinationLive sourceLive := by
                rw [sourceLiveEq]
                exact comp_syn_impl_cut_sets_subspt _ destinationLive sourceSyntax
              intro n hn
              obtain ⟨hDestMem, hDestLookup⟩ := hDestSub n hn
              obtain ⟨hSourceMem, hSourceLookup⟩ := hSourceSub n hDestMem
              exact ⟨hSourceMem, hSourceLookup.trans hDestLookup⟩
            have hSourceLocalsOnLive := crepToLoopLocalsRelExact_cutset_prop
                context live sourceLive sourceState.locals target.locals
                afterSource.locals hLocals hSourceLocals hLiveSub
            have hLocalsAddress := crepToLoopLocalsRelExact_insert_gt_vmax
                context live sourceState.locals afterSource.locals sourceTmp
                (.word address) hSourceLocalsOnLive (by omega)
            have hLocalsBoth := crepToLoopLocalsRelExact_insert_gt_vmax
                context live sourceState.locals
                (LoopSemStateFiniteExact.setVar sourceTmp (.word address) afterSource).locals
                (sourceTmp + 1) (.word value) hLocalsAddress (by omega)
            refine ⟨destinationClock + sourceClock, none, targetFinal,
              hTargetRun, ?_, hMemAfter, ?_, ?_, rfl, ?_⟩
            · simpa [crepToLoopStateRelExact, targetFinal, afterBoth, afterAddress,
                LoopSemStateFiniteExact.setVar] using hSourceState
            · simpa [targetFinal, afterBoth, afterAddress,
                LoopSemStateFiniteExact.setVar] using hSourceGlobals
            · simpa [targetFinal, afterBoth, afterAddress,
                LoopSemStateFiniteExact.setVar] using hSourceCodeRel
            · simpa [localsResultRel, targetFinal, afterBoth, afterAddress,
                LoopSemStateFiniteExact.setVar] using hLocalsBoth
