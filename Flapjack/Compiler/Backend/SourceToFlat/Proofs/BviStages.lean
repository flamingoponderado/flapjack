import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.BviInline.Proofs.Pipeline
import Flapjack.Compiler.Backend.SourceToFlat.ToDataIncremental
import Flapjack.Compiler.Backend.BviToData.Proofs.Install

/-! Executed BVI stage witnesses for the configured source pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- A successful configured run contains successful executions of every
source-to-BVI stage, with the returned state and code assembled from those
executions. This is Flapjack pipeline infrastructure. -/
theorem configured_bvi_all_stage_witnesses (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (config : BvlToBvi.Config) (decls : List AstHOL.Dec)
    (resultSource : Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (output : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure config decls =
      some (resultSource, resultClosure, resultConfig, output, names)) :
    ∃ source' exps closure' bvl names' inlines optimized start beforeTail next1 tailLast afterTail
      tmcLast afterTmc cache,
      compileCakeToClosFuel fuel source decls = some (source', exps) ∧
      ClosToBvl.compileCallMtiFuel? fuel closure exps = some (closure', bvl, names') ∧
      BvlInline.compileProgFuel fuel config.inlineSizeLimit config.expCut config.splitMainAtSeq bvl =
        some (inlines, optimized) ∧
      BvlToBvi.compileProgFuel fuel fuel closure'.start 0 optimized = some (start, beforeTail, next1) ∧
      BviTailrec.compileProgFuel fuel config.doTailrec (Flapjack.bvlNumStubs + 2) beforeTail =
        some (tailLast, afterTail) ∧
      BviTmc.compileProgFuel fuel config.doTmc (Flapjack.bvlNumStubs + 3) afterTail =
        some (tmcLast, afterTmc) ∧
      BviInline.compileProgFuel fuel afterTmc = some (cache, output) ∧
      resultSource = source' ∧ resultClosure = { closure' with start := start } ∧
      resultConfig = { config with inlines := inlines, bviInlines := cache, nextName1 := next1, nextName2 := tailLast, nextName3 := tmcLast } ∧
      names = BvlToBvi.getNames (output.map fun (n, _, _) => n) names' := by
  unfold compileCakeToBviConfiguredFuel at run
  cases first : compileCakeToClosFuel fuel source decls with
  | none => simp [first] at run
  | some firstResult =>
    obtain ⟨source', exps⟩ := firstResult
    cases second : ClosToBvl.compileCallMtiFuel? fuel closure exps with
    | none => simp [first, second] at run
    | some secondResult =>
      obtain ⟨closure', bvl, names'⟩ := secondResult
      cases third : BvlInline.compileProgFuel fuel config.inlineSizeLimit config.expCut config.splitMainAtSeq bvl with
      | none => simp [first, second, third] at run
      | some thirdResult =>
        obtain ⟨inlines, optimized⟩ := thirdResult
        cases fourth : BvlToBvi.compileProgFuel fuel fuel closure'.start 0 optimized with
        | none => simp [first, second, third, fourth] at run
        | some fourthResult =>
          obtain ⟨start, beforeTail, next1⟩ := fourthResult
          cases fifth : BviTailrec.compileProgFuel fuel config.doTailrec (Flapjack.bvlNumStubs + 2) beforeTail with
          | none => simp [first, second, third, fourth, fifth] at run
          | some fifthResult =>
            obtain ⟨tailLast, afterTail⟩ := fifthResult
            cases sixth : BviTmc.compileProgFuel fuel config.doTmc (Flapjack.bvlNumStubs + 3) afterTail with
            | none => simp [first, second, third, fourth, fifth, sixth] at run
            | some sixthResult =>
              obtain ⟨tmcLast, afterTmc⟩ := sixthResult
              cases seventh : BviInline.compileProgFuel fuel afterTmc with
              | none => simp [first, second, third, fourth, fifth, sixth, seventh] at run
              | some seventhResult =>
                obtain ⟨cache, code⟩ := seventhResult
                simp [first, second, third, fourth, fifth, sixth, seventh] at run
                obtain ⟨sourceEq, closureEq, configEq, outputEq, namesEq⟩ := run
                subst code
                refine ⟨source', exps, closure', bvl, names', inlines, optimized, start, beforeTail,
                  next1, tailLast, afterTail, tmcLast, afterTmc, cache, ?_⟩
                simp_all

/-- Flapjack infrastructure: a successful configured source-to-BVI run
contains the actual tail-recursion, TMC, and inlining executions, and stores
the inliner's resulting cache in its returned configuration. -/
theorem configured_bvi_stage_witnesses (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (config : BvlToBvi.Config) (decls : List AstHOL.Dec)
    (resultSource : Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (output : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure config decls =
      some (resultSource, resultClosure, resultConfig, output, names)) :
    ∃ beforeTail afterTail afterTmc tailLast tmcLast cache,
      BviTailrec.compileProgFuel fuel config.doTailrec (Flapjack.bvlNumStubs + 2) beforeTail =
        some (tailLast, afterTail) ∧
      BviTmc.compileProgFuel fuel config.doTmc (Flapjack.bvlNumStubs + 3) afterTail =
        some (tmcLast, afterTmc) ∧
      BviInline.compileProgFuel fuel afterTmc = some (cache, output) ∧
      resultConfig.bviInlines = cache := by
  obtain ⟨source', exps, closure', bvl, names', inlines, optimized, start, beforeTail,
    next1, tailLast, afterTail, tmcLast, afterTmc, cache, _, _, _, _, tailRun, tmcRun,
    inlineRun, _, _, configEq, _⟩ :=
    configured_bvi_all_stage_witnesses fuel source closure config decls resultSource resultClosure
      resultConfig output names run
  refine ⟨beforeTail, afterTail, afterTmc, tailLast, tmcLast, cache, tailRun, tmcRun, inlineRun, ?_⟩
  rw [configEq]

/-- Flapjack infrastructure: the inlining stage in a successful configured
pipeline preserves the TMC output labels and stores its cache. -/
theorem configured_bvi_inline_names (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (config : BvlToBvi.Config) (decls : List AstHOL.Dec)
    (resultSource : Config) (resultClosure : ClosToBvl.Config) (resultConfig : BvlToBvi.Config)
    (output : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure config decls =
      some (resultSource, resultClosure, resultConfig, output, names)) :
    ∃ beforeTail afterTail afterTmc tailLast tmcLast,
      BviTailrec.compileProgFuel fuel config.doTailrec (Flapjack.bvlNumStubs + 2) beforeTail =
        some (tailLast, afterTail) ∧
      BviTmc.compileProgFuel fuel config.doTmc (Flapjack.bvlNumStubs + 3) afterTail =
        some (tmcLast, afterTmc) ∧
      BviInline.compileProgFuel fuel afterTmc = some (resultConfig.bviInlines, output) ∧
      output.map Prod.fst = afterTmc.map Prod.fst := by
  obtain ⟨beforeTail, afterTail, afterTmc, tailLast, tmcLast, cache, tailRun, tmcRun, inlineRun, cacheEq⟩ :=
    configured_bvi_stage_witnesses fuel source closure config decls resultSource resultClosure resultConfig output names run
  subst cache
  exact ⟨beforeTail, afterTail, afterTmc, tailLast, tmcLast, tailRun, tmcRun, inlineRun,
    BviInline.compileProgFuel_names fuel afterTmc output resultConfig.bviInlines inlineRun⟩

/-- A successful incremental source-to-BVI stage is followed by the exact
executed BVI-to-data program traversal, whose resulting code tree satisfies
the simulation's code relation. This is Flapjack pipeline infrastructure;
it does not establish correctness of the preceding frontend passes. -/
theorem incremental_bvi_to_data_codeRel (fuel : Nat)
    (config : Config × ClosToBvl.Config × BvlToBvi.Config) (envId : Nat × Nat)
    (decls : List AstHOL.Dec)
    (nextConfig : Config × ClosToBvl.Config × BvlToBvi.Config)
    (program : List (Nat × Nat × Bvi.Exp))
    (run : compileCakeIncToBviFuel fuel config envId decls = some (nextConfig, program)) :
    ∃ compiled,
      compileCakeIncToDataFuel fuel config envId decls = some (nextConfig, compiled) ∧
      BviToData.codeRel (sptFromAList program) (sptFromAList compiled) := by
  refine ⟨BviToData.compileProg program, ?_, BviToData.codeRel_compileProg program⟩
  unfold compileCakeIncToDataFuel
  rw [run]
  simp only [bind, Option.bind]
  have agreement := BviToData.compileProgBounded_agrees fuel program
  simp only [bind, Option.bind] at agreement
  rw [agreement]
  rfl

end Flapjack.Compiler.Backend.SourceToFlat
