import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations

/-! Type and exception stamp cases of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Flapjack proof infrastructure: updating both stamp counters on related
states preserves their recording relation. -/
private theorem stateRel_updateStamps {Config F : Type} (ci : CompilerInstance Config)
    (source target : State F) (typeStamp exnStamp : Nat) (related : stateRel ci source target) :
    stateRel ci { source with nextTypeStamp := typeStamp, nextExnStamp := exnStamp }
      { target with nextTypeStamp := typeStamp, nextExnStamp := exnStamp } := by
  obtain ⟨dec, oracle, refs, targetEq, stores, sourceEval, callback, compilerState,
    decoder, compiler, initial, oracleInitial, counter, valid, wf⟩ := related
  subst target
  exact ⟨dec, oracle, refs, rfl, stores, sourceEval, callback, compilerState,
    decoder, compiler, initial, oracleInitial, counter, valid, wf⟩

/-- Type declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dtype {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (types : TypeDef) :
    DecsSimAt ci s env [.dtype loc types] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  have stampRelated := stateRel_updateStamps ci s t (s.nextTypeStamp + types.length) s.nextExnStamp related
  obtain ⟨_, oracle, refs, targetEq, _⟩ := related
  subst t
  by_cases check : types.all checkDupCtors = true
  · simp [evaluateDecs, check] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨oracle, { s with refs := refs, evalState := some (.evalOracle oracle), nextTypeStamp := s.nextTypeStamp + types.length },
      .val { v := nsEmpty, c := buildTdefs s.nextTypeStamp types }, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp [evaluateDecs, check]
    · simpa using stampRelated
    · simp [resultRel, envRel, nsLookup_nsEmpty]
    · exact envStoreForward_refl _
    · intro _
      exact envStackForward_refl _
  · simp [evaluateDecs, check, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim

/-- Exception declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dexn {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT) :
    DecsSimAt ci s env [.dexn loc name types] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  have stampRelated := stateRel_updateStamps ci s t s.nextTypeStamp (s.nextExnStamp + 1) related
  obtain ⟨_, oracle, refs, targetEq, _⟩ := related
  subst t
  simp [evaluateDecs] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracle, { s with refs := refs, evalState := some (.evalOracle oracle), nextExnStamp := s.nextExnStamp + 1 },
    .val { v := nsEmpty, c := nsSing name (types.length, .exnStamp s.nextExnStamp) }, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp [evaluateDecs]
  · simpa using stampRelated
  · simp [resultRel, envRel, nsLookup_nsEmpty]
  · exact envStoreForward_refl _
  · intro _
    exact envStackForward_refl _
end Flapjack.Compiler.Backend.SourceEval.Proofs
