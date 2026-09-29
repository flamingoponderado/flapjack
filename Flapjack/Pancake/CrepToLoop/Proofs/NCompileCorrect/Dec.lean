import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.NotMemContextAssigned
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# The `Dec` case of `crep_to_loop`'s `ncompile_correct`

This module owns the HOL-native `Dec` case so its exact induction theorem and
supporting context relation do not collide with other constructor cases in
`NcompileCorrect.lean`. HOL source: `crep_to_loopProofScript.sml:110-154`,
case proof `Resume ncompile_correct[Dec]` at lines 2408-2584.
-/

namespace Flapjack

open LoopSemStateFiniteExact

namespace NCompileCorrectDecFmapWitnesses

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
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end NCompileCorrectDecFmapWitnesses

/-- Flapjack-only Dec bridge (no HOL declaration): extending the source locals
    with a declared value, the context map with its fresh temporary, and target
    locals with that temporary preserves the exact `locals_rel` conjunction.
    This is the context-update congruence step immediately before applying the
    `ncompile_correct` body induction hypothesis. -/
theorem crepToLoopNcompileDecLocalsEnter {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (sourceLocals : HolFiniteMapExact Nat (HolWordLab width))
    (targetLocals : Spt (WordLocW width)) (name tmp : Nat)
    (value : HolWordLab width)
    (hInitial : crepToLoopLocalsRelExact ctxt live sourceLocals targetLocals)
    (hFresh : ctxt.vmax < tmp) :
    crepToLoopLocalsRelExact
      { ctxt with vars := ctxt.vars.updateEq (name, tmp), vmax := tmp }
      (sptInsert tmp () live)
      (sourceLocals.updateEq (name, value))
      (sptInsert tmp (wlabWlocHOL value) targetLocals) := by
  let bodyCtxt : CrepToLoopContextExact :=
    { ctxt with vars := ctxt.vars.updateEq (name, tmp), vmax := tmp }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y n m hx hy hnm
    by_cases hxName : x = name
    · subst x
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hx
      by_cases hyName : y = name
      · subst y
        simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hy
        have hn : n = tmp := by simpa using hx.symm
        have hm : m = tmp := by simpa using hy.symm
        rfl
      · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg hyName] at hy
        have hn : n = tmp := by simpa using hx.symm
        have hbound := hInitial.2.1 y m hy
        have hFalse : False := by omega
        exact hFalse.elim
    · by_cases hyName : y = name
      · subst y
        simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg hxName] at hx
        simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hy
        have hm : tmp = m := by simpa using hy
        have hbound := hInitial.2.1 x n hx
        have hFalse : False := by omega
        exact hFalse.elim
      · have hx' : ctxt.vars.lookup x = some n := by
          simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hxName] using hx
        have hy' : ctxt.vars.lookup y = some m := by
          simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hyName] using hy
        exact hInitial.1 x y n m hx' hy' hnm
  · intro x m hx
    by_cases hxName : x = name
    · subst x
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hx
      have hm : tmp = m := by simpa using hx
      have hle : m ≤ tmp := by omega
      change m ≤ bodyCtxt.vmax
      rw [show bodyCtxt.vmax = tmp by rfl]
      exact hle
    · have hx' : ctxt.vars.lookup x = some m := by
        simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hxName] using hx
      exact Nat.le_trans (hInitial.2.1 x m hx') (Nat.le_of_lt hFresh)
  · intro n hn
    rcases (sptMem_sptInsert n tmp () live).mp hn with heq | hnLive
    · subst n
      exact (sptMem_sptInsert tmp tmp (wlabWlocHOL value) targetLocals).mpr (Or.inl rfl)
    · exact (sptMem_sptInsert n tmp (wlabWlocHOL value) targetLocals).mpr
        (Or.inr (hInitial.2.2.1 n hnLive))
  · intro sourceName item hitem
    by_cases hname : sourceName = name
    · subst sourceName
      have hitemEq : value = item := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hitem
      subst item
      exact ⟨tmp, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
        (sptMem_sptInsert tmp tmp () live).mpr (Or.inl rfl), by
          simp [sptLookup_sptInsert, wlabWlocHOL]⟩
    · have hitemOld : sourceLocals.lookup sourceName = some item := by
        have hi := hitem
        rw [HolFiniteMapExact.lookup_updateEq] at hi
        simpa [FUPDATE_HOL, hname] using hi
      obtain ⟨mapped, hmap, hmem, hslot⟩ := hInitial.2.2.2 sourceName item hitemOld
      have hmapNew : bodyCtxt.vars.lookup sourceName = some mapped := by
        rw [HolFiniteMapExact.lookup_updateEq]
        simpa [bodyCtxt, FUPDATE_HOL, hname] using hmap
      have hmappedLt : mapped ≤ ctxt.vmax := hInitial.2.1 sourceName mapped hmap
      have hne : mapped ≠ tmp := by omega
      refine ⟨mapped, hmapNew, (sptMem_sptInsert mapped tmp () live).mpr (Or.inr hmem), ?_⟩
      simpa [sptLookup_sptInsert, hne, wlabWlocHOL] using hslot

/-- Flapjack-only Dec bridge (no HOL declaration): after running a declared
    body under the context that maps its name to a fresh temporary, restoring
    the source binding yields the caller-context `locals_rel` when the body's
    execution preserved any prior caller slot for that name. This isolates the
    context/update congruence step used by HOL's `ncompile_correct[Dec]`.
    The Dec case derives `hPreserve` from HOL's `not_mem_context_assigned_mem_gt`,
    `member_cutset_survives_comp_prog`, and `unassigned_vars_evaluate_same`. -/
theorem crepToLoopNcompileDecLocalsRestore {width : Nat} [NeZero width]
    (ctxt bodyCtxt : CrepToLoopContextExact) (live : NumSet) (name tmp : Nat)
    (source0 sourceBody sourceFinal : HolFiniteMapExact Nat (HolWordLab width))
    (target0 targetBody : Spt (WordLocW width))
    (hInitial : crepToLoopLocalsRelExact ctxt live source0 target0)
    (hBody : crepToLoopLocalsRelExact bodyCtxt (sptInsert tmp () live) sourceBody targetBody)
    (hContext : bodyCtxt.vars = ctxt.vars.updateEq (name, tmp))
    (hFresh : ctxt.vmax < tmp)
    (hFinal : sourceFinal = sourceBody.resVarEq (name, source0.lookup name))
    (hPreserve : ∀ n old, ctxt.vars.lookup name = some n → source0.lookup name = some old →
      sptLookup n targetBody = sptLookup n target0) :
    crepToLoopLocalsRelExact ctxt live sourceFinal targetBody := by
  refine ⟨hInitial.1, hInitial.2.1, ?_, ?_⟩
  · intro n hn
    exact hBody.2.2.1 n ((sptMem_sptInsert n tmp () live).mpr (Or.inr hn))
  · intro sourceName value hvalue
    by_cases hname : sourceName = name
    · subst sourceName
      have hrestore :
          (sourceBody.resVarEq (name, source0.lookup name)).lookup name = some value := by
        simpa [hFinal] using hvalue
      cases hold : source0.lookup name with
      | none => simp [HolFiniteMapExact.lookup_resVarEq_none, FDOMSUB_HOL, hold] at hrestore
      | some old =>
          have hvalueOld : old = value := by
            simpa [HolFiniteMapExact.lookup_resVarEq_some, FUPDATE_HOL, hold] using hrestore
          have hprior := hInitial.2.2.2 name old hold
          obtain ⟨mapped, hmap, hmem, hslot⟩ := hprior
          refine ⟨mapped, hmap, hmem, ?_⟩
          rw [hPreserve mapped old hmap hold]
          simpa [hvalueOld] using hslot
    · have hbodyValue : sourceBody.lookup sourceName = some value := by
        have hv := hvalue
        rw [hFinal] at hv
        cases hold : source0.lookup name with
        | none =>
            simpa [HolFiniteMapExact.holFmapAsFiniteSupportResultWitness_resVarEq,
              FDOMSUB_HOL, hold, hname] using hv
        | some old =>
            simpa [HolFiniteMapExact.holFmapAsFiniteSupportResultWitness_resVarEq,
              FUPDATE_HOL, hold, hname] using hv
      obtain ⟨mapped, hmapBody, hmem, hslot⟩ := hBody.2.2.2 sourceName value hbodyValue
      have hmap : ctxt.vars.lookup sourceName = some mapped := by
        have hm := hmapBody
        rw [hContext, HolFiniteMapExact.lookup_updateEq] at hm
        simpa [FUPDATE_HOL, hname] using hm
      have hmemLive : sptMem mapped live := by
        rcases (sptMem_sptInsert mapped tmp () live).mp hmem with heq | hlive
        · subst mapped
          have hmapped := hInitial.2.1 sourceName tmp hmap
          omega
        · exact hlive
      exact ⟨mapped, hmap, hmemLive, hslot⟩

/-- Genuine `Dec name e body` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:2408-2584`). The
    induction hypothesis is exactly the theorem property for `body` after
    evaluating `e` and updating the declared source local. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_dec {width : Nat} [NeZero width] {σ : Type} :
    ∀ (name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
      (v1 : CrepSemHOLState width σ),
      (∀ value, evalCrepSemHOLExp v1 e = some value →
        crepToLoopNcompileCorrectAt body
          { v1 with locals := v1.locals.updateEq (name, value) }) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.dec name e body) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro name e body v1 ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_dec_holShape] at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
      simp only [hev, Prod.mk.injEq] at he
      exact absurd he.1.symm hne
  | some value =>
      simp only [hev] at he
      let sourceBody : CrepSemHOLState width σ :=
        { v1 with locals := v1.locals.updateEq (name, value) }
      cases hBody : evalCrepSemHOLProgExact sourceBody body with
      | mk bodyResult bodyState =>
        rw [hBody] at he
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨hResult, hFinal⟩
        have hBodyEval : evalCrepSemHOLProgExact sourceBody body = (bodyResult, bodyState) := hBody
        rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with
          ⟨codePrefix, compiledValue, temporary, nextLive⟩
        obtain ⟨prefixClock, prefixState, hPrefix, hValue, hPrefixState,
          hPrefixMem, hPrefixGlobals, hPrefixCode, hPrefixLocals⟩ :=
          crepToLoop_comp_exp_preserves_eval v1 e value t ctxt (ctxt.vmax + 1) l
            codePrefix compiledValue temporary nextLive
            ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
        obtain ⟨hNoContext, hTempBound, hNextLive⟩ :=
          compile_exp_out_rel ctxt (ctxt.vmax + 1) l e codePrefix compiledValue temporary nextLive hC
        have hLiveNext : ∀ k, sptMem k l → sptMem k nextLive := by
          intro k hk
          rw [hNextLive]
          exact cut_sets_union_domain_subset _ l hNoContext k hk
        have hLocalsBefore : crepToLoopLocalsRelExact ctxt l v1.locals prefixState.locals := by
          refine ⟨hPrefixLocals.1, hPrefixLocals.2.1, ?_, ?_⟩
          intro k hk
          exact hPrefixLocals.2.2.1 k (hLiveNext k hk)
          intro key val hval
          obtain ⟨n, hmap, hmem, _⟩ := hl.2.2.2 key val hval
          obtain ⟨n', hmap', _, hslot⟩ := hPrefixLocals.2.2.2 key val hval
          have hn : n' = n := Option.some.inj (hmap'.symm.trans hmap)
          subst n'
          exact ⟨n, hmap', hmem, hslot⟩
        have hFresh : ctxt.vmax < temporary := by omega
        let bodyCtxt : CrepToLoopContextExact :=
          { ctxt with vars := ctxt.vars.updateEq (name, temporary), vmax := temporary }
        let bodyLive : NumSet := sptInsert temporary () l
        let targetBody : LoopSemStateFiniteExact width σ :=
          LoopSemStateFiniteExact.setVar temporary (wlabWlocExact value) prefixState
        have hBodyLocals : crepToLoopLocalsRelExact bodyCtxt bodyLive
            sourceBody.locals targetBody.locals := by
          have hw : (wlabWlocExact : HolWordLab width → WordLocW width) = wlabWlocHOL := by
            funext v
            cases v
            rfl
          have hEntered := crepToLoopNcompileDecLocalsEnter ctxt l v1.locals prefixState.locals
            name temporary value hLocalsBefore hFresh
          rw [← hw] at hEntered
          simpa [sourceBody, targetBody, bodyLive, bodyCtxt, CrepSemHOLState.setVar,
            LoopSemStateFiniteExact.setVar] using hEntered
        have hBodyState : crepToLoopStateRelExact sourceBody targetBody := by
          simpa [sourceBody, targetBody, crepToLoopStateRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixState
        have hBodyMem : crepToLoopMemRelHOLExact sourceBody.memory targetBody.memory
            sourceBody.memaddrs := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixMem
        have hBodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals targetBody.globals := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixGlobals
        have hBodyCode : crepToLoopCodeRelExact bodyCtxt sourceBody.code targetBody.code := by
          simpa [sourceBody, targetBody, bodyCtxt, crepToLoopCodeRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixCode
        have hBodyNotError : bodyResult ≠ some .error := by
          intro herr
          apply hne
          rw [← hResult]
          exact herr
        let bodyIH := ih value hev
        obtain ⟨bodyClock, targetResult, targetFinal, hTargetBodyEval,
          hFinalStateBody, hFinalMemBody, hFinalGlobalsBody, hFinalCodeBody,
          hResultBody, hLocalsBody⟩ :=
          bodyIH bodyResult bodyState targetBody bodyCtxt bodyLive
            ⟨hBodyEval, hBodyNotError, hBodyState, hBodyMem, hBodyGlobals,
              hBodyCode, hBodyLocals⟩
        have hCompile : compileHOLExact ctxt l (.dec name e body) =
            .seq (loopNestedSeqHOL codePrefix)
              (.seq (.assign temporary compiledValue)
                (compileHOLExact bodyCtxt bodyLive body)) := by
          rw [compileHOLExact, hC]
        have hPrefixLift : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL codePrefix)
            { t with clock := t.clock + (prefixClock + bodyClock) } =
              (none, { prefixState with clock := prefixState.clock + bodyClock }) := by
          have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
            (loopNestedSeqHOL codePrefix) { t with clock := t.clock + prefixClock }
            none prefixState bodyClock hPrefix (by simp)
          simpa [Nat.add_assoc] using hLift
        have hAssignEval : LoopSemStateFiniteExact.evaluate (.assign temporary compiledValue)
            { prefixState with clock := prefixState.clock + bodyClock } =
              (none, { targetBody with clock := targetBody.clock + bodyClock }) := by
          rw [LoopSemStateFiniteExact.evaluate.eq_3]
          simp [LoopSemStateFiniteExact.eval_upd_clock_eq, hValue, targetBody,
            LoopSemStateFiniteExact.setVar]
        have hRun : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + (prefixClock + bodyClock) } = (targetResult, targetFinal) := by
          rw [hCompile]
          simp only [LoopSemStateFiniteExact.evaluate_seq, hPrefixLift]
          rw [hAssignEval]
          exact hTargetBodyEval
        have hResultFinal : targetResult = crepToLoopResultHOL res := by
          calc
            targetResult = crepToLoopResultHOL bodyResult := hResultBody
            _ = crepToLoopResultHOL res := by rw [← hResult]
        have hSourceFinalLocals : s1.locals =
            bodyState.locals.resVarEq (name, v1.locals.lookup name) := by
          have hLocalsEq := congrArg (fun state : CrepSemHOLState width σ => state.locals) hFinal
          simpa [sourceBody] using hLocalsEq.symm
        have hMakePreserve : UnassignedGoodRes targetResult → ∀ n old,
            ctxt.vars.lookup name = some n → v1.locals.lookup name = some old →
              sptLookup n targetFinal.locals = sptLookup n prefixState.locals := by
          intro hGood n old hname hOld
          have hmax := hLocalsBefore.2.1 name n hname
          have hneTmp : n ≠ temporary := by omega
          obtain ⟨mapped, hmap, hmem, hslot⟩ :=
            hLocalsBefore.2.2.2 name old hOld
          have hmapped : mapped = n := Option.some.inj (hmap.symm.trans hname)
          subst mapped
          have hslotTarget : sptLookup n targetBody.locals = some (wlabWlocHOL old) := by
            simpa [targetBody, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert,
              hneTmp, wlabWlocExact, wlabWlocHOL] using hslot
          have hNotAssigned : n ∉ holLoopAssignedVars
              (compileHOLExact bodyCtxt bodyLive body) := by
            apply not_mem_context_assigned_mem_gt bodyCtxt bodyLive body n
            refine ⟨hBodyLocals.2.1, ?_, ?_⟩
            · intro var mapped hlookup
              by_cases hvar : var = name
              · subst var
                have hmapped : temporary = mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlookup
                omega
              · have hlookupOld : ctxt.vars.lookup var = some mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hvar] using hlookup
                intro heq
                have hsame := hLocalsBefore.1 name var n mapped hname hlookupOld heq
                exact hvar hsame.symm
            · have hnle : n ≤ ctxt.vmax := hmax
              have hnleBody : n ≤ bodyCtxt.vmax := by
                simpa [bodyCtxt] using (Nat.le_trans hnle (Nat.le_of_lt hFresh))
              exact hnleBody
          have hLive : (sptLookup n bodyLive).isSome = true := by
            exact (sptMem_sptInsert n temporary () l).mpr (Or.inr hmem)
          have hSurvives : survivesHOLExact n
              (compileHOLExact bodyCtxt bodyLive body) = true :=
            member_cutset_survives_comp_prog bodyCtxt bodyLive body n hLive
          have hRunPreserved := unassigned_vars_evaluate_same
            (compileHOLExact bodyCtxt bodyLive body)
            { targetBody with clock := targetBody.clock + bodyClock }
            targetResult targetFinal n (wlabWlocHOL old)
            ⟨hTargetBodyEval, hGood, by
              simpa [targetBody, LoopSemStateFiniteExact.setVar] using hslotTarget,
              hNotAssigned, hSurvives⟩
          have hslotInitial : sptLookup n prefixState.locals = some (wlabWlocHOL old) := hslot
          calc
            sptLookup n targetFinal.locals = sptLookup n targetBody.locals := hRunPreserved
            _ = sptLookup n prefixState.locals := hslotTarget.trans hslotInitial.symm
        have hFinalLocals : crepToLoopResultLocalsHOL ctxt l s1.locals targetFinal.locals res := by
          cases res with
          | none =>
              have hGood : UnassignedGoodRes targetResult := by
                simp [hResultFinal, crepToLoopResultHOL, UnassignedGoodRes]
              have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                  bodyState.locals targetFinal.locals := by
                  simpa [crepToLoopResultLocalsHOL, hResultBody, hResult] using hLocalsBody
              exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                (hMakePreserve hGood)
          | some result =>
              cases result with
              | «break» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, crepToLoopResultHOL, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [crepToLoopResultLocalsHOL, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «continue» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, crepToLoopResultHOL, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [crepToLoopResultLocalsHOL, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «return» _ => trivial
              | exception _ => trivial
              | timeOut => trivial
              | finalFfi _ => trivial
              | error =>
                  exfalso
                  apply hne
                  rw [← hResult]
        refine ⟨prefixClock + bodyClock, targetResult, targetFinal, hRun, ?_, ?_, ?_, ?_, hResultFinal,
          hFinalLocals⟩
        · rw [← hFinal]
          simpa [crepToLoopStateRelExact] using hFinalStateBody
        · rw [← hFinal]
          simpa using hFinalMemBody
        · rw [← hFinal]
          simpa using hFinalGlobalsBody
        · rw [← hFinal]
          simpa [crepToLoopCodeRelExact, bodyCtxt] using hFinalCodeBody

end Flapjack
