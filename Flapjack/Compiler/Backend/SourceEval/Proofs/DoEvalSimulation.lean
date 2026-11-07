import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleReset
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCallback
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording
import Flapjack.Compiler.Backend.SourceEval.Proofs.Concrete
import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
import Flapjack.SemanticPrimitivesHOL.Eval
import Mathlib.Data.List.Forall2
import Lean.Elab.Tactic.Omega

/-! Dynamic evaluation and environment-generation simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

/-- Flapjack proof infrastructure: adding a generation preserves existing environment lookups. -/
private theorem generationForward (oracle : EvalOracleState) (recording : EvalOracleFun) :
    envStoreForward oracle (addEnvGeneration { oracle with oracle := recording }) := by
  constructor
  · simp [addEnvGeneration]
  · intro id env found
    rcases id with ⟨g, i⟩
    simp only [lookupEnv] at found ⊢
    cases h : oracle.envs[g]? with
    | none => simp [h] at found
    | some entry =>
      have bound : g < oracle.envs.length := List.getElem?_eq_some_iff.mp h |>.choose
      simpa [addEnvGeneration, List.getElem?_append, bound, h] using found

/-- Dynamic evaluation preserves related states and restores the caller generation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_eval_sim"]
theorem doEval_sim {Config F : Type} (xs : List Value) (s : State F) (env : SemEnv Value)
    (decs : List Dec) (es : Option EvalState) (ci : CompilerInstance Config)
    (t : State F) (ys : List Value)
    (premises : doEval xs.reverse s.evalState = some (env, decs, es) ∧
      stateRel ci s t ∧ List.Forall₂ (ValueRel (oracleState t.evalState)) xs ys) :
    ∃ env' es', envStoreForward (oracleState t.evalState) (oracleState es') ∧
      doEval ys.reverse t.evalState = some (env', decs, es') ∧
      envRel (ValueRel (oracleState es')) env env' ∧
      stateRel ci { s with evalState := es } { t with evalState := es' } ∧
      ∀ s₂ t₂, stateRel ci (s₂ : State F) t₂ ∧
        envStoreForward (oracleState es') (oracleState t₂.evalState) ∧
        envStackForward (oracleState es') (oracleState t₂.evalState) →
        envStoreForward (oracleState t₂.evalState)
          (oracleState (resetEnvGeneration t.evalState t₂.evalState)) ∧
        stateRel ci { s₂ with evalState := resetEnvGeneration s.evalState s₂.evalState }
          { t₂ with evalState := resetEnvGeneration t.evalState t₂.evalState } ∧
        envStackForward (oracleState t.evalState)
          (oracleState (resetEnvGeneration t.evalState t₂.evalState)) := by
  classical
  obtain ⟨run, ⟨dec, oracle, refs, target, stores, sourceEval, callback,
    compilerState, decoder, compiler, initial, oracleInitial, counter, valid, wf⟩, values⟩ := premises
  subst t
  simp only [oracleState] at values ⊢
  rw [sourceEval] at run
  have reversed := (List.forall₂_reverse_iff).2 values
  generalize hx : xs.reverse = xsr at run reversed
  generalize hy : ys.reverse = ysr at reversed ⊢
  cases reversed with
  | nil => simp [doEval] at run
  | @cons first first' r r' firstRel tail =>
    cases tail with
    | nil => simp [doEval] at run
    | @cons second second' r r' secondRel tail =>
      cases tail with
      | nil => simp [doEval] at run
      | @cons third third' r r' thirdRel tail =>
        cases tail with
        | nil => simp [doEval] at run
        | @cons fourth fourth' r r' fourthRel tail =>
          cases tail with
          | nil => simp [doEval] at run
          | @cons fifth fifth' r r' fifthRel tail =>
            cases tail with
            | nil => simp [doEval] at run
            | @cons sixth sixth' r r' sixthRel tail =>
              cases tail with
              | cons _ _ => simp [doEval] at run
              | nil =>
                cases firstRel with
                | @env sourceEnv targetEnv id encoded decoded lookup envRelated =>
                  cases decDecoded : dec.decodeDecs third with
                  | none => simp [doEval, decDecoded] at run
                  | some decodedDecs =>
                    by_cases validCall : second = dec.compilerState ∧ concreteValue third = true ∧
                        compilerAgrees dec.compiler (id, second, decodedDecs) (fourth, fifth, sixth)
                    · simp [doEval, decDecoded, validCall] at run
                      obtain ⟨_, rfl, rfl, rfl⟩ := run
                      have concrete := compilerAgrees_concrete dec.compiler id second decodedDecs fourth fifth sixth validCall.2.2
                      have sameSecond := concreteValue_rel oracle second second' secondRel concrete.1
                      have sameThird := concreteValue_rel oracle third third' thirdRel validCall.2.1
                      have sameFourth := concreteValue_rel oracle fourth fourth' fourthRel concrete.2.1
                      have sameFifth := concreteValue_rel oracle fifth fifth' fifthRel concrete.2.2.1
                      have sameSixth := concreteValue_rel oracle sixth sixth' sixthRel concrete.2.2.2
                      subst second'; subst third'; subst fourth'; subst fifth'; subst sixth'
                      let recording : EvalOracleFun := fun j =>
                        if j = 0 then (((oracle.oracle 0).1.1 + 1, 0), fourth, [])
                        else if j = (oracle.oracle 0).1.1 + 1 then (id, second, decodedDecs)
                        else oracle.oracle j
                      let updated := addEnvGeneration { oracle with oracle := recording }
                      have forward : envStoreForward oracle updated := generationForward oracle recording
                      refine ⟨targetEnv, some (.evalOracle updated), forward, ?_, ?_, ?_, ?_⟩
                      · have dec' : vFunAbs ci.decsDom ci.decsV third = some decodedDecs := by
                          simpa [decoder] using decDecoded
                        have agrees : compilerAgrees (mkCompilerFunFromCi ci)
                            (id, second, decodedDecs) (fourth, fifth, sixth) := by
                          simpa [compiler] using validCall.2.2
                        have previous : second = (oracle.oracle 0).2.1 := validCall.1.trans compilerState
                        rw [previous] at agrees
                        simp [doEval, callback, doEvalRecord, decoded, dec', agrees, previous,
                          lookup, updated, recording]
                      · exact (forwardRules oracle (.conv none []) (.conv none []) updated [] []
                          sourceEnv targetEnv).2.2.1 ⟨(valueEnvRel_iff _ _ _).mp envRelated, forward⟩
                      · refine ⟨addDecsGeneration { dec with compilerState := fourth }, updated,
                          refs, rfl, (forwardRules oracle (.conv none []) (.conv none []) updated [] []
                          sourceEnv targetEnv).2.2.2 _ _ ⟨stores, forward⟩, rfl, ?_⟩
                        simp only [updated, addEnvGeneration]
                        refine ⟨callback, ?_, decoder, compiler, ?_, ?_, ?_, ?_, ?_⟩
                        · simp [addDecsGeneration, recording]
                        · simp [recording]
                        · intro positive
                          by_cases zero : (oracle.oracle 0).1.1 = 0
                          · simpa [recording, zero] using validCall.1.trans (initial zero.symm)
                          · have : (oracle.oracle 0).1.1 + 1 ≠ 1 := by omega
                            simpa [recording, zero] using oracleInitial (by omega)
                        · simp [addDecsGeneration, counter, Flapjack.holEl_eq_getElem,
                            List.getElem_append_right]
                        · simp
                        · apply recordedOracleWellFormed_step
                          refine ⟨wf, ?_, ?_⟩
                          · simpa [compiler] using validCall.2.2
                          · intro _
                            exact validCall.1.trans compilerState
                      · intro s₂ t₂ ⟨related₂, forward₂, stack₂⟩
                        obtain ⟨dec₂, oracle₂, refs₂, target₂, stores₂, sourceEval₂, callback₂,
                          compilerState₂, decoder₂, compiler₂, initial₂, oracleInitial₂,
                          counter₂, valid₂, wf₂⟩ := related₂
                        subst t₂
                        simp only at forward₂ stack₂ ⊢
                        rw [sourceEval, sourceEval₂]
                        simp only [resetEnvGeneration]
                        have oldEntries : ∀ j, j < oracle.envs.length →
                            Flapjack.holEl j oracle₂.envs = Flapjack.holEl j oracle.envs := by
                          intro j bound
                          have found := stack₂.2 j (by simpa [updated, addEnvGeneration] using bound)
                          rw [found]
                          change Flapjack.holEl j (oracle.envs ++ [[]]) = Flapjack.holEl j oracle.envs
                          rw [Flapjack.holEl_eq_getElem _ _ (by simp; omega),
                            Flapjack.holEl_eq_getElem _ _ bound]
                          simp [bound]
                        refine ⟨?_, ?_, ?_⟩
                        · exact ⟨le_rfl, fun _ _ h => h⟩
                        · let resetOracle := { oracle₂ with generation := oracle.generation }
                          have resetForward : envStoreForward oracle₂ resetOracle :=
                            ⟨le_rfl, fun _ _ found => found⟩
                          refine ⟨{ dec₂ with envIdCounter :=
                              (dec.envIdCounter.1, dec.envIdCounter.2.1, dec₂.envIdCounter.2.2) },
                            resetOracle, refs₂, rfl,
                            (forwardRules oracle₂ (.conv none []) (.conv none []) resetOracle [] []
                              sourceEnv targetEnv).2.2.2 _ _ ⟨stores₂, resetForward⟩, rfl, ?_⟩
                          simp only [resetOracle]
                          refine ⟨callback₂, compilerState₂, decoder₂, compiler₂, initial₂,
                            oracleInitial₂, ?_, ?_, wf₂⟩
                          · simp [counter, counter₂, oldEntries oracle.generation valid]
                          · have length := forward₂.1
                            simp [updated, addEnvGeneration] at length
                            omega
                        · refine ⟨rfl, ?_⟩
                          intro j bound
                          exact oldEntries j (by omega)
                    · simp [doEval, decDecoded, validCall] at run
                | _ => simp [doEval] at run

end Flapjack.Compiler.Backend.SourceEval.Proofs
