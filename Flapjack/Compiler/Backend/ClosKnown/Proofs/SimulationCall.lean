module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Direct-call case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Call
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Direct-call case of the source simulation, with the evaluator induction
hypotheses for arguments and a successfully located callee. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Call {C F : Type} (trace : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List ClosLang.Exp) (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (_bodyIH : ∀ (argResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value)
      (entry : List ClosSem.Value × ClosLang.Exp) (args : List ClosSem.Value) (body : ClosLang.Exp),
      evaluate xs env1full s0 = (argResult, middle) ∧ argResult = .val values ∧
      findCode dest values middle.code = some entry ∧ entry = (args, body) ∧
      ¬ (middle.clock < ticks + 1) → KnownSimulationAt [body] args (decClock (ticks + 1) middle))
    (argsIH : KnownSimulationAt xs env1full s0) :
    KnownSimulationAt [.call trace ticks dest xs] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have argsSyntax : everyFnVarsNone xs := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have h := exprSafe (.call trace ticks dest xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  have argsFree : fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp] using free
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    rw [knownListTotal_call, hk] at known
    simp at known
    rcases known with ⟨rfl, rfl⟩
    cases hr : evaluate xs env1full s0 with
    | mk argResult next =>
      rw [evaluate, fixClock_evaluate, hr] at run
      have argsNoType : argResult ≠ .err (.abort .typeError) := by
        intro eq
        subst argResult
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact noType rfl
      have step := argsIH argResult next env1 xenv1 env2 xenv2 t0 c g0 g1 aenv ea
        ⟨hr, hk, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
          argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
          sub0, sub1, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
      obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
      cases argResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        cases res2 with
        | val vals => simp [resultRel] at result
        | err error2 =>
          refine ⟨.err error2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
          simp only [List.map_cons, List.map_nil]
          rw [evaluate, fixClock_evaluate, targetRun]
      | val values =>
        have emptyCode : next.code = HolFiniteMapExact.empty := finalState.2.2.1
        have absent : findCode dest values next.code = none := by simp [findCode, emptyCode, HolFiniteMapExact.empty]
        simp [absent] at run
        rcases run with ⟨rfl, rfl⟩
        exact False.elim (noType rfl)

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Call
