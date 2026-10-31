import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.BviInline.Proofs.Pipeline

/-! Executed BVI stage witnesses for the configured source pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

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
        obtain ⟨inlines, bvl'⟩ := thirdResult
        cases fourth : BvlToBvi.compileProgFuel fuel fuel closure'.start 0 bvl' with
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
                obtain ⟨_, _, configEq, outputEq, _⟩ := run
                subst code
                refine ⟨beforeTail, afterTail, afterTmc, tailLast, tmcLast, cache,
                  fifth, sixth, seventh, ?_⟩
                rw [← configEq]

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

end Flapjack.Compiler.Backend.SourceToFlat
