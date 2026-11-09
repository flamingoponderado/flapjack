module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation

@[expose] public section


/-! Tick case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Tick
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Tick case of the original optimizer simulation theorem, with its original
nonzero-clock induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Tick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (ih : s0.clock ≠ 0 → KnownSimulationAt [body] env1full (decClock 1 s0)) :
    KnownSimulationAt [.tick trace body] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have clockEq : s0.clock = t0.clock := state.2.2.2.2.1
  have bodySyntax : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have bodyDisjoint : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have h := exprSafe (.tick trace body) (by simp)
    simpa [esgcFree] using h
  have bodyFree : fvMax env1.length [body] := by
    simpa [fvMax, freeVars, freeVarExp] using free
  have bodyUnique : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_tickSource, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    by_cases zero : s0.clock = 0
    · simp [evaluate, zero] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨.err (.abort .timeoutError), t0, ?_, ?_, state, globals, stateOracle, oracle⟩
      · simp [evaluate, ← clockEq, zero]
      · simp [resultRel, excRel]
    · have bodyRun : evaluate [body] env1full (decClock 1 s0) = (res1, s) := by
        simpa [evaluate, zero] using run
      have stateDec : StateRel c (nextG (decClock 1 s0)) (decClock 1 s0) (decClock 1 t0) := by
        simpa [StateRel, decClock, nextG, clockEq] using state
      have step := ih zero res1 s env1 xenv1 env2 xenv2 (decClock 1 t0) c g0 bodyG aenv [(be, ba)]
        ⟨bodyRun, hk, stateDec, bodySyntax, by simpa [decClock] using coSyntax,
          by simpa [decClock] using bodyDisjoint, by simpa [decClock, nextG] using oracle,
          by simpa [decClock, stateOracleMglobalsDisjoint] using stateOracleDisjoint,
          bodySafe, (ssgcFreeDecClock 1 s0).2 safe, envSafe, approxRel,
          by simpa [decClock] using oracleSafe, globalSafe, approxSafe,
          by simpa [decClock, nextG, stateGlobalsApprox] using globals,
          sub0, by simpa [decClock, nextG] using sub1, by simpa [decClock] using mono,
          bodyFree, by simpa [decClock, nextG] using envRel, by simpa [decClock] using bodyUnique,
          by simpa [decClock] using stateOracle, envEq, noType⟩
      obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
      refine ⟨res2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
      simpa [evaluate, ← clockEq, zero] using targetRun

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Tick
