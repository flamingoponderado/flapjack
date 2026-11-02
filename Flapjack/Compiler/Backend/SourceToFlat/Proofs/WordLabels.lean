import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordTotal
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BviStages
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.OutputLabels
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberedPrepared

/-! Label invariants for the configured CakeML-to-word driver. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- In the multi-argument-introduction configuration, the executed source
pipeline generates distinct BVI labels above the data runtime-stub range. -/
theorem configured_bvi_labels_mti (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (enabled : closure.doMti = true) (calls : closure.doCall = false) (known : closure.knownConf = none) :
    (bviCode.map Prod.fst).Nodup ∧ ∀ label ∈ bviCode.map Prod.fst, dataNumStubs ≤ label := by
  obtain ⟨source', expressions, output, compiled, names', cache, optimized, targetStart, lowered,
    targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
    optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, rest⟩ :=
    configured_bvi_all_stage_witnesses fuel source closure bvlConfig declarations nextSource nextClosure nextBvlConfig bviCode names run
  obtain ⟨current, program, output', names'', pre', compiled', _⟩ :=
    ClosToBvl.compileCallMtiFuel_mtiOnly_erasure fuel closure output expressions compiled names' enabled calls known closureRun
  have distinct := ClosToBvl.compileNoOpts_prepared_labels_nodup { closure with doMti := false } current output'
    (ClosMti.introList closure.maxApp expressions) program compiled names'' pre' compiled'
  exact BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_labels fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
    fuel fuel output.start 0 bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiled optimized cache
    targetStart targetNext lowered beforeTmc afterTmc bviCode tailLast tmcLast bviCache distinct
    optimizedRun lowerRun tailRun tmcRun inlineRun

/-- For this configured pipeline, its actual word output satisfies the
production data-to-word code relation without an extra label assumption. -/
theorem compileCakeToWord64ConfiguredFuel_codeRel_mti (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (enabled : closure.doMti = true) (calls : closure.doCall = false) (known : closure.knownConf = none) :
    ∃ code, compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      DataToWord.Proofs.Gc.codeRel64 word (sptFromAList (BviToData.compileProg bviCode)) (sptFromAList code) := by
  have labels := configured_bvi_labels_mti fuel source nextSource closure nextClosure bvlConfig nextBvlConfig declarations
    bviCode names run enabled calls known
  exact compileCakeToWord64ConfiguredFuel_codeRel_of_bviLabels fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run labels.1 labels.2

/-- With direct-call and known-function optimization disabled, label
uniqueness and the data-stub bound hold regardless of the multi-argument flag. -/
theorem configured_bvi_labels_noCallKnown (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none) :
    (bviCode.map Prod.fst).Nodup ∧ ∀ label ∈ bviCode.map Prod.fst, dataNumStubs ≤ label := by
  cases mti : closure.doMti with
  | true =>
    exact configured_bvi_labels_mti fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run mti calls known
  | false =>
    obtain ⟨source', expressions, output, compiled, names', cache, optimized, targetStart, lowered,
      targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
      optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, rest⟩ :=
      configured_bvi_all_stage_witnesses fuel source closure bvlConfig declarations nextSource nextClosure nextBvlConfig bviCode names run
    have noOpts : ClosToBvl.compileNoOpts? closure expressions = some (output, compiled, names') := by
      rw [← ClosToBvl.compileCallMtiFuel_noOpts fuel closure expressions mti calls known]
      exact closureRun
    cases preprocess : ClosToBvl.compileCommonNoOpts? closure expressions with
    | none => simp [ClosToBvl.compileNoOpts?, preprocess] at noOpts
    | some pair =>
      obtain ⟨current, program⟩ := pair
      have distinct := ClosToBvl.compileNoOpts_prepared_labels_nodup closure current output expressions
        program compiled names' preprocess noOpts
      exact BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_labels fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
        fuel fuel output.start 0 bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiled optimized cache
        targetStart targetNext lowered beforeTmc afterTmc bviCode tailLast tmcLast bviCache distinct
        optimizedRun lowerRun tailRun tmcRun inlineRun

/-- The configured word output satisfies the code relation for either setting
of multi-argument introduction, with direct-call and known-function passes disabled. -/
theorem compileCakeToWord64ConfiguredFuel_codeRel_noCallKnown (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none) :
    ∃ code, compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      DataToWord.Proofs.Gc.codeRel64 word (sptFromAList (BviToData.compileProg bviCode)) (sptFromAList code) := by
  have labels := configured_bvi_labels_noCallKnown fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    declarations bviCode names run calls known
  exact compileCakeToWord64ConfiguredFuel_codeRel_of_bviLabels fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run labels.1 labels.2

end Flapjack.Compiler.Backend.SourceToFlat
