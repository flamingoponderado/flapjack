module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Raise case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Raise
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Raise case of the original optimizer simulation theorem, with its source
body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Raise {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt [body] env1full s0) :
    KnownSimulationAt [.raise trace body] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have bodySyntax : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have bodyDisjoint : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have h := exprSafe (.raise trace body) (by simp)
    simpa [esgcFree] using h
  have bodyFree : fvMax env1.length [body] := by
    simpa [fvMax, freeVars, freeVarExp] using free
  have bodyUnique : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals] using unique
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_raise, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    cases hr : evaluate [body] env1full s0 with
    | mk bodyResult next =>
      have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
        intro eq
        subst bodyResult
        simp [evaluate, hr] at run
        rcases run with ⟨rfl, rfl⟩
        exact noType rfl
      have step := ih bodyResult next env1 xenv1 env2 xenv2 t0 c g0 bodyG aenv [(be, ba)]
        ⟨hr, hk, state, bodySyntax, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
          bodySafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
          sub0, sub1, mono, bodyFree, envRel, bodyUnique, stateOracle, envEq, bodyNoType⟩
      obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
      cases bodyResult with
      | err error =>
        simp [evaluate, hr] at run
        rcases run with ⟨rfl, rfl⟩
        cases res2 with
        | val vals => simp [resultRel] at result
        | err error2 =>
          refine ⟨.err error2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
          have targetRun' : evaluate [be] (env2 ++ xenv2) t0 = (.err error2, t) := by simpa using targetRun
          simp [evaluate, targetRun']
      | val vals =>
        obtain ⟨v, rfl⟩ := evaluate_singleton_value body env1full s0 next vals hr
        simp [evaluate, hr] at run
        rcases run with ⟨rfl, rfl⟩
        cases res2 with
        | err error2 => simp [resultRel] at result
        | val values2 =>
          obtain ⟨v2, rfl⟩ := evaluate_singleton_value be (env2 ++ xenv2) t0 t values2 (by simpa using targetRun)
          have valRel : ValueRel c (nextG next) v v2 := by cases result with | cons rel _ => exact rel
          refine ⟨.err (.raise v2), t, ?_, ?_, finalState, finalGlobals, finalOracle, finalDisjoint⟩
          · have targetRun' : evaluate [be] (env2 ++ xenv2) t0 = (.val [v2], t) := by simpa using targetRun
            simp [evaluate, targetRun']
          · exact valRel

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Raise
