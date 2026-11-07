import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppInline
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppNonInline

/-! Application expression case of the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.App
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Application expression case of the source simulation with the evaluator's
argument, function, and application induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0App {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (x : ClosLang.Exp) (xs : List ClosLang.Exp) (env1full : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F)
    (appIH : ∀ (argResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value)
      (fnResult : Result (List ClosSem.Value) ClosSem.Value)
      (next : State (Spt ValApprox × C) F) (fnValues : List ClosSem.Value),
      0 < xs.length ∧ evaluate xs env1full s0 = (argResult, middle) ∧ argResult = .val values ∧
      evaluate [x] env1full middle = (fnResult, next) ∧ fnResult = .val fnValues →
      KnownAppSimulationAt loc (@Flapjack.holHd ClosSem.Value ⟨.number 0⟩ fnValues) values next)
    (fnIH : ∀ (argResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value),
      0 < xs.length ∧ evaluate xs env1full s0 = (argResult, middle) ∧ argResult = .val values →
      KnownSimulationAt [x] env1full middle)
    (argsIH : 0 < xs.length → KnownSimulationAt xs env1full s0) :
    KnownSimulationAt [.app trace loc x xs] env1full s0 := by
  intro result final env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  cases xs with
  | nil =>
    simp [evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    exact False.elim (noType rfl)
  | cons first rest =>
    have argsInd := argsIH (by simp)
    have fnInd : ∀ middle values, evaluate (first :: rest) env1full s0 = (.val values, middle) →
        KnownSimulationAt [x] env1full middle := by
      intro middle values hr
      exact fnIH (.val values) middle values ⟨by simp, hr, rfl⟩
    have appInd : ∀ middle values next fn, evaluate (first :: rest) env1full s0 = (.val values, middle) →
        evaluate [x] env1full middle = (.val [fn], next) → KnownAppSimulationAt loc fn values next := by
      intro middle values next fn hr hf
      simpa [Flapjack.holHd] using appIH (.val values) middle values (.val [fn]) next [fn]
        ⟨by simp, hr, rfl, hf, rfl⟩
    cases ha : knownListTotal c (first :: rest) aenv g0 with
    | mk argsEas g1 =>
      cases hf : knownListTotal c [x] aenv g1 with
      | mk fnEas g2 =>
        obtain ⟨fnExp, fnApprox, eq⟩ := knownListTotal_single_result c x aenv g1 g2 fnEas hf
        subst fnEas
        rw [knownListTotal_app, ha] at known
        dsimp only at known
        rw [hf] at known
        simp only [knownSourceHead, List.headD_cons] at known
        cases hd : decideInlineHOL c fnApprox loc (first :: rest).length with
        | nothing =>
          simp only [List.length_cons] at hd
          simp [hd] at known
          rcases known with ⟨rfl, rfl⟩
          simpa using AppNonInline.nonInlineApplicationSimulation trace loc loc x first rest
            env1full env1 xenv1 env2 xenv2 s0 final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox
            argsInd fnInd appInd ha hf (Or.inl rfl) run noType
            ⟨state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
              envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
              free, envRel, unique, stateOracle, envEq⟩
        | annotate address =>
          simp only [List.length_cons] at hd
          simp [hd] at known
          rcases known with ⟨rfl, rfl⟩
          simpa using AppNonInline.nonInlineApplicationSimulation trace loc (some address) x first rest
            env1full env1 xenv1 env2 xenv2 s0 final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox
            argsInd fnInd appInd ha hf (Or.inr ⟨address, rfl, hd⟩) run noType
            ⟨state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
              envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
              free, envRel, unique, stateOracle, envEq⟩
        | letInline body =>
          simp only [List.length_cons] at hd
          cases hb : knownListTotal (decInlineFactor c) [body] (argsEas.map Prod.snd) g2 with
          | mk bodyEas after =>
            obtain ⟨targetBody, bodyApprox, eq⟩ := knownListTotal_single_result (decInlineFactor c) body
              (argsEas.map Prod.snd) g2 after bodyEas hb
            subst bodyEas
            simp [hd, hb] at known
            rcases known with ⟨rfl, rfl⟩
            simpa using AppInline.inlineApplicationSimulation trace loc x first rest env1full env1 xenv1 env2 xenv2
              s0 final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox body targetBody bodyApprox after
              argsInd fnInd appInd ha hf hd hb run noType
              ⟨state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
                envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
                free, envRel, unique, stateOracle, envEq⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.App
