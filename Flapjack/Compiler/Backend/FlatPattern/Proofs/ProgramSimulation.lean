module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedInduction
public import Flapjack.Compiler.Backend.FlatProps.SemanticsSimulation

@[expose] public section

/-! Program-level simulation for the flat pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- Related installation configurations give a program evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_eval_sim"]
theorem compileDecs_evalSim {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig) :
    FlatProps.evalSim ffi source target sourceConfig targetConfig
      (fun decs decs' => decs.map (compileDec cfg2) = decs') false := by
  intro clock sourceResult sourceState ⟨run, safe, programs⟩
  have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa using safe
  subst target
  have states := stateRel_initial cfg ffi clock sourceConfig targetConfig configs
  obtain ⟨targetState, targetResult, targetRun, results, finalStates⟩ :=
    (compileExps_evaluate cfg).2 _ source _ sourceState cfg2 _ sourceResult ⟨run, rfl, states, sourceSafe⟩
  refine ⟨0, targetResult, targetState, by simpa using targetRun, finalStates.2.2.1.symm, ?_, ?_, ?_⟩
  · intro isNone
    subst sourceResult
    cases targetResult <;> simp_all [optionRel]
  · intro value isRaise
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases error <;> simp_all [optionRel, SemanticPrimitivesProps.excRel]
  · intro abort isAbort
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases error <;> simp_all [optionRel, SemanticPrimitivesProps.excRel]

/-- Pattern compilation preserves the semantics of a non-failing program. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_semantics"]
theorem compileDecs_semantics {C F : Type} (cfg : Config) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (ffi : HolFfiState F) (source : List FlatLang.Exp) (cfg2 : Config)
    (premises : installConfRel cfg sourceConfig targetConfig ∧
      FlatSem.semantics sourceConfig ffi source ≠ .fail) :
    FlatSem.semantics sourceConfig ffi source = FlatSem.semantics targetConfig ffi (source.map (compileDec cfg2)) := by
  obtain ⟨configs, notFail⟩ := premises
  exact FlatProps.imp_semanticsEq ffi source (source.map (compileDec cfg2)) sourceConfig targetConfig
    (fun decs decs' => decs.map (compileDec cfg2) = decs')
    ⟨compileDecs_evalSim cfg cfg2 ffi source (source.map (compileDec cfg2)) sourceConfig targetConfig configs, notFail⟩ rfl

end Flapjack.Compiler.Backend.FlatPattern
