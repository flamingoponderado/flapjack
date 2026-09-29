import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Seq
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# Production/exact Loop If case

HOL `loopSem$evaluate_def` (`loopSemScript.sml:341-346`) looks up the left
operand, obtains the immediate/register operand with `get_var_imm`, rejects
missing or location-valued operands with `Error`, compares the two words with
`word_cmp`, evaluates the selected child, and applies `cut_res live_out`.
Production `evaluateLoop` (`LoopSem.lean:190-196`) has the same branch shape,
but its comparison is an abstract hook and its live set is a list. This bridge
therefore requires comparator agreement and the checked `numSetListRel` live
set relation; recursive child behavior is supplied as the two chosen-child
case relations. It does not claim arbitrary hooks or finite-fuel evaluator
equivalence. This is Flapjack-specific infrastructure, not a standalone HOL
theorem, so it has no `@[hol]` tag.
-/

namespace Flapjack.LoopSemStateFiniteExact.EvaluateCases

private def optionStateProdRel {width : Nat} [NeZero width] {F : Type} :
    Option (LoopSemStateFiniteExact width F) →
      Option (LoopMachineState (BitVec width) F) → Prop
  | none, none => True
  | some state, some machine => state.prodRel machine
  | _, _ => False

private theorem liveLocalsGuard_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    {live : NumSet} {runtimeLive : List Nat}
    (hrel : state.prodRel machine)
    (hlive : numSetListRel runtimeLive live) :
    loopLiveLocalsPresent machine.locals runtimeLive = true ↔
      sptSubsetLive live state.locals := by
  constructor
  · intro hguard key hkey
    have hlookup : sptLookup key live = some () :=
      (sptMem_iff_lookup key live).mp hkey |>.choose_spec
    have hmem : key ∈ runtimeLive := (hlive.2 key).mp hlookup
    have hpresent : (machine.locals key).isSome = true := by
      have hAll : ∀ keys, loopLiveLocalsPresent machine.locals keys = true →
          ∀ name, name ∈ keys → (machine.locals name).isSome = true := by
        intro keys
        induction keys with
        | nil => intro _ name hname; simp at hname
        | cons head tail ih =>
            intro hguard name hname
            simp only [loopLiveLocalsPresent, Bool.and_eq_true] at hguard
            simp only [List.mem_cons] at hname
            rcases hname with rfl | hname
            · exact hguard.1
            · exact ih hguard.2 name hname
      exact hAll runtimeLive hguard key hmem
    have hmachine := hrel.1 key
    cases hstate : sptLookup key state.locals with
    | none =>
        rw [hmachine] at hpresent
        simp [hstate] at hpresent
    | some value => exact (sptMem_iff_lookup key state.locals).2 ⟨value, hstate⟩
  · intro hsubset
    have hall : ∀ key, key ∈ runtimeLive → (machine.locals key).isSome = true := by
      intro key hkey
      have hlookup : sptLookup key live = some () := (hlive.2 key).mpr hkey
      have hmem : sptMem key live := (sptMem_iff_lookup key live).mpr ⟨(), hlookup⟩
      have hlocal := hsubset key hmem
      have hmachine := hrel.1 key
      cases hstate : sptLookup key state.locals with
      | none =>
          have hexists := (sptMem_iff_lookup key state.locals).1 hlocal
          rcases hexists with ⟨value, hvalue⟩
          rw [hstate] at hvalue
          contradiction
      | some value => simp [hmachine, hstate]
    have hAll : ∀ keys, (∀ key, key ∈ keys → (machine.locals key).isSome = true) →
        loopLiveLocalsPresent machine.locals keys = true := by
      intro keys
      induction keys with
      | nil => intro _; simp [loopLiveLocalsPresent]
      | cons head tail ih =>
          intro hkeys
          simp only [loopLiveLocalsPresent, Bool.and_eq_true]
          exact ⟨hkeys head (by simp), ih (fun key hkey => hkeys key (by simp [hkey]))⟩
    exact hAll runtimeLive hall

private theorem cutState_cutLoopState_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    {live : NumSet} {runtimeLive : List Nat}
    (hrel : state.prodRel machine)
    (hlive : numSetListRel runtimeLive live) :
    optionStateProdRel (LoopSemStateFiniteExact.cutState live state)
      (cutLoopState runtimeLive machine) := by
  have hguard := liveLocalsGuard_prodRel hrel hlive
  by_cases hsubset : sptSubsetLive live state.locals
  · have hruntime : loopLiveLocalsPresent machine.locals runtimeLive = true :=
      hguard.mpr hsubset
    have hcutRel :
        ({ state with locals := sptInter state.locals live }).prodRel
          { machine with locals := loopRestrictLocals machine.locals runtimeLive } := by
      rcases hrel with
        ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
          hbaseAddr, htopAddr, hcode, hcoverage⟩
      refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
        hbaseAddr, htopAddr, hcode, hcoverage⟩
      intro key
      have hmember : (sptLookup key live).isSome = true ↔ key ∈ runtimeLive := by
        constructor
        · intro hsome
          cases hlookup : sptLookup key live with
          | none => simp [hlookup] at hsome
          | some value =>
              cases value
              exact (hlive.2 key).mp hlookup
        · intro hmem
          have hlookup : sptLookup key live = some () := (hlive.2 key).mpr hmem
          simp [hlookup]
      change loopRestrictLocals machine.locals runtimeLive key =
        (sptLookup key (sptInter state.locals live)).map loopValueOfWordLocW
      unfold loopRestrictLocals
      rw [hlocals key]
      rw [sptLookup_sptInter]
      by_cases hmem : key ∈ runtimeLive
      · have hsome : (sptLookup key live).isSome = true := hmember.mpr hmem
        simp [hmem, hsome]
      · have hnone : (sptLookup key live).isSome = false := by
          cases hsome : (sptLookup key live).isSome with
          | false => rfl
          | true => exact False.elim (hmem (hmember.mp hsome))
        simp [hmem, hnone]
    simp [optionStateProdRel, LoopSemStateFiniteExact.cutState, hsubset,
      cutLoopState, hruntime, hcutRel]
  · have hruntime : loopLiveLocalsPresent machine.locals runtimeLive = false := by
      cases h : loopLiveLocalsPresent machine.locals runtimeLive with
      | false => rfl
      | true => exact False.elim (hsubset (hguard.mp h))
    simp [optionStateProdRel, LoopSemStateFiniteExact.cutState, hsubset,
      cutLoopState, hruntime]

private theorem cutRes_cutLoopResult_prodRel {width : Nat} [NeZero width] {F : Type}
    {live : NumSet} {runtimeLive : List Nat}
    {exactStep : Option (LoopResultExact width) × LoopSemStateFiniteExact width F}
    {productionStep : Option (LoopMachineResult (BitVec width)) × LoopMachineState (BitVec width) F}
  (hlive : numSetListRel runtimeLive live)
    (hstep : loopEvaluationStepRel exactStep productionStep) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.cutRes live exactStep)
      (cutLoopResult runtimeLive productionStep) := by
  rcases exactStep with ⟨exactResult, exactState⟩
  rcases productionStep with ⟨productionResult, productionState⟩
  have hstep' : loopEvaluationStepRel (exactResult, exactState)
      (productionResult, productionState) := by
    simpa [loopEvaluationStepRel] using hstep
  rcases hstep' with ⟨hresult, hstate⟩
  cases hexactResult : exactResult with
  | some result =>
      cases hproductionResult : productionResult with
      | none => simp [loopResultOptionRel, hexactResult, hproductionResult] at hresult
      | some productionResult =>
          simpa [LoopSemStateFiniteExact.cutRes, cutLoopResult,
            loopEvaluationStepRel, hexactResult, hproductionResult] using
            And.intro hresult hstate
  | none =>
      have hproductionNone : productionResult = none := by
        cases hproductionResult : productionResult with
        | none => rfl
        | some productionResult =>
            simp [loopResultOptionRel, hexactResult, hproductionResult] at hresult
      subst productionResult
      have hcuts := cutState_cutLoopState_prodRel hstate hlive
      cases hExactCut : LoopSemStateFiniteExact.cutState live exactState with
      | none =>
          have hProdCut : cutLoopState runtimeLive productionState = none := by
            cases hcut : cutLoopState runtimeLive productionState with
            | none => rfl
            | some cut => simp [optionStateProdRel, hExactCut, hcut] at hcuts
          simp [LoopSemStateFiniteExact.cutRes, cutLoopResult,
            hExactCut, hProdCut, loopEvaluationStepRel, loopResultOptionRel, hstate]
      | some exactCut =>
          cases hProdCut : cutLoopState runtimeLive productionState with
          | none => simp [optionStateProdRel, hExactCut, hProdCut] at hcuts
          | some productionCut =>
              have hcutRel : exactCut.prodRel productionCut := by
                simpa [optionStateProdRel, hExactCut, hProdCut] using hcuts
              have hclock : exactCut.clock = productionCut.clock :=
                hcutRel.2.2.2.2.2.1.symm
              by_cases hzero : exactCut.clock = 0
              · have hprodZero : productionCut.clock = 0 := by
                  rw [← hclock]; exact hzero
                have htimeoutRel :
                    ({ exactCut with locals := .ln }).prodRel
                      ({ productionCut with locals := fun _ => none } :
                        LoopMachineState (BitVec width) F) := by
                  rcases hcutRel with
                    ⟨_hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock,
                      hbe, hffi, hbaseAddr, htopAddr, hcode, hcoverage⟩
                  refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe,
                    hffi, hbaseAddr, htopAddr, hcode, hcoverage⟩
                  intro key
                  simp
                simp [LoopSemStateFiniteExact.cutRes, cutLoopResult, Option.isSome,
                  hExactCut, hProdCut, hzero, hprodZero,
                  loopEvaluationStepRel, loopResultOptionRel]
                exact (by simpa [hzero, hprodZero] using htimeoutRel)
              · have hprodZero : productionCut.clock ≠ 0 := by
                  intro hprod; apply hzero; rw [hclock, hprod]
                have hdecrement :
                    (LoopSemStateFiniteExact.decClock exactCut).prodRel
                      (decrementLoopClock productionCut) := by
                  have hupdated := clockUpdate_prodRel hcutRel (exactCut.clock - 1)
                  simpa [LoopSemStateFiniteExact.decClock, decrementLoopClock,
                    hclock] using hupdated
                simp only [LoopSemStateFiniteExact.cutRes, cutLoopResult,
                  hExactCut, hProdCut, hzero, hprodZero,
                  if_false, loopEvaluationStepRel,
                  loopResultOptionRel]
                exact ⟨trivial, by simpa [LoopSemStateFiniteExact.decClock,
                  decrementLoopClock, hclock] using hdecrement⟩

/-- Compositional exact/production Loop `If` case. HOL's exact operands and
production locals/register reads agree by `prodRel`; missing and location
operands therefore fail with the same `Error`. For word operands, only the
production comparison hook must be shown to implement HOL `word_cmp`. Both
branches are then composed under their own recursive result/state relations,
and `cut_res`/`cutLoopResult` are related by the explicit live-set carrier
relation. No entire-If evaluator equivalence is assumed. -/
theorem evaluateIf_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F) (fuel : Nat)
    (cmp : Cmp) (condition : Nat)
    (right : RegImm (BitVec width))
    (thenBranch elseBranch : HolLoopProg width)
    (runtimeThen runtimeElse : LoopProg (BitVec width))
    (live : NumSet) (runtimeLive : List Nat)
    (hstate : state.prodRel machine)
    (hlive : numSetListRel runtimeLive live)
    (hcompare : ∀ x y : BitVec width,
      hooks.compare cmp (.word x) (.word y) =
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y)
    (hThen : ∀ {state' : LoopSemStateFiniteExact width F}
      {machine' : LoopMachineState (BitVec width) F},
      state'.prodRel machine' →
        loopEvaluationStepRel (LoopSemStateFiniteExact.evaluate thenBranch state')
          (Flapjack.evaluateLoop fuel hooks runtimeThen machine'))
    (hElse : ∀ {state' : LoopSemStateFiniteExact width F}
      {machine' : LoopMachineState (BitVec width) F},
      state'.prodRel machine' →
        loopEvaluationStepRel (LoopSemStateFiniteExact.evaluate elseBranch state')
          (Flapjack.evaluateLoop fuel hooks runtimeElse machine')) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.evaluate (.ite cmp condition right thenBranch elseBranch live) state)
    (Flapjack.evaluateLoop (fuel + 1) hooks
        (.ite cmp condition right runtimeThen runtimeElse runtimeLive) machine) := by
  rw [LoopSemStateFiniteExact.evaluate.eq_13, Flapjack.evaluateLoop.eq_14]
  have hcondition := hstate.1 condition
  have hright := LoopSemStateFiniteExact.getVarImm_map_eq_of_prodRel hstate right
  rw [hcondition, ← hright]
  cases hleft : sptLookup condition state.locals with
  | none =>
      simp [loopEvaluationStepRel, loopResultOptionRel, Option.map,
        loopValueOfWordLocW]
      exact hstate
  | some left =>
      cases left with
      | loc label offset =>
          simp [loopEvaluationStepRel, loopResultOptionRel, Option.map,
            loopValueOfWordLocW]
          exact hstate
      | word x =>
          cases hrightExact : LoopSemStateFiniteExact.getVarImm right state with
          | none =>
              simp [loopEvaluationStepRel, loopResultOptionRel, Option.map,
                loopValueOfWordLocW]
              exact hstate
          | some rightValue =>
              cases rightValue with
              | loc label offset =>
                  simp [loopEvaluationStepRel, loopResultOptionRel, Option.map,
                    loopValueOfWordLocW]
                  exact hstate
              | word y =>
                  simp [Option.map, loopValueOfWordLocW]
                  rw [hcompare x y]
                  cases hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y with
                  | false =>
                      have hchosen := hElse hstate
                      have hcut := cutRes_cutLoopResult_prodRel hlive hchosen
                      simpa [loopEvaluationStepRel, loopResultOptionRel,
                        LoopSemStateFiniteExact.cutRes, cutLoopResult, hleft,
                        hrightExact, hcmp] using hcut
                  | true =>
                      have hchosen := hThen hstate
                      have hcut := cutRes_cutLoopResult_prodRel hlive hchosen
                      simpa [loopEvaluationStepRel, loopResultOptionRel,
                        LoopSemStateFiniteExact.cutRes, cutLoopResult, hleft,
                        hrightExact, hcmp] using hcut

end Flapjack.LoopSemStateFiniteExact.EvaluateCases
