import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordTotal
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BviStages
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.OutputLabels
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberedPrepared
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiKnownDriverSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiKnownCallDriver

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

/-- The configured pipeline has distinct BVI labels with direct-call conversion
disabled, for either known-function and multi-argument setting. This is
Flapjack composition infrastructure rather than a separate HOL declaration. -/
theorem configured_bvi_labels_noCall (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) :
    (bviCode.map Prod.fst).Nodup ∧ ∀ label ∈ bviCode.map Prod.fst, dataNumStubs ≤ label := by
  cases known : closure.knownConf with
  | none =>
    exact configured_bvi_labels_noCallKnown fuel source nextSource closure nextClosure
      bvlConfig nextBvlConfig declarations bviCode names run calls known
  | some knownConfig =>
    obtain ⟨source', expressions, output, compiled, names', cache, optimized, targetStart, lowered,
      targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
      optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, rest⟩ :=
      configured_bvi_all_stage_witnesses fuel source closure bvlConfig declarations nextSource nextClosure nextBvlConfig bviCode names run
    have distinct : (compiled.map Prod.fst).Nodup := by
      cases mti : closure.doMti with
      | false =>
        exact ClosToBvl.compileCallMtiFuel_knownOnly_labels fuel closure output knownConfig expressions
          compiled names' mti calls known closureRun
      | true =>
        obtain ⟨output', names'', alternate, _⟩ :=
          ClosToBvl.compileCallMtiFuel_mtiKnown_erasure fuel closure output knownConfig expressions
            compiled names' mti calls known closureRun
        exact ClosToBvl.compileCallMtiFuel_knownOnly_labels fuel { closure with doMti := false }
          output' knownConfig (ClosMti.introList closure.maxApp expressions) compiled names'' rfl
          (by simpa using calls) (by simpa using known) alternate
    exact BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_labels fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
      fuel fuel output.start 0 bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiled optimized cache
      targetStart targetNext lowered beforeTmc afterTmc bviCode tailLast tmcLast bviCache distinct
      optimizedRun lowerRun tailRun tmcRun inlineRun

/-- The emitted word code satisfies the candidate code relation with known
optimization either enabled or disabled. Direct calls remain disabled. -/
theorem compileCakeToWord64ConfiguredFuel_codeRel_noCall (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) :
    ∃ code, compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      DataToWord.Proofs.Gc.codeRel64 word (sptFromAList (BviToData.compileProg bviCode)) (sptFromAList code) := by
  have labels := configured_bvi_labels_noCall fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    declarations bviCode names run calls
  exact compileCakeToWord64ConfiguredFuel_codeRel_of_bviLabels fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run labels.1 labels.2

/-- With known-function optimization enabled, the generated BVI labels are
distinct for either direct-call and multi-argument setting. -/
theorem configured_bvi_labels_known (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (knownConfig : ClosKnown.Config) (known : closure.knownConf = some knownConfig) :
    (bviCode.map Prod.fst).Nodup ∧ ∀ label ∈ bviCode.map Prod.fst, dataNumStubs ≤ label := by
  cases calls : closure.doCall with
  | false =>
    exact configured_bvi_labels_noCall fuel source nextSource closure nextClosure
      bvlConfig nextBvlConfig declarations bviCode names run calls
  | true =>
    obtain ⟨source', expressions, output, compiled, names', cache, optimized, targetStart, lowered,
      targetNext, tailLast, beforeTmc, tmcLast, afterTmc, bviCache, sourceRun, closureRun,
      optimizedRun, lowerRun, tailRun, tmcRun, inlineRun, sourceEq, closureEq, configEq, rest⟩ :=
      configured_bvi_all_stage_witnesses fuel source closure bvlConfig declarations nextSource nextClosure nextBvlConfig bviCode names run
    have distinct : (compiled.map Prod.fst).Nodup := by
      cases mti : closure.doMti with
      | false =>
        let next := closure.nextLoc + max 1 expressions.length
        let aligned := if next % 2 = 0 then next else next + 1
        let numbered := (ClosNumber.renumberList aligned expressions).2
        let opt := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
        obtain ⟨⟨called, callState⟩, callRun⟩ := ClosCall.compileFuel_succeeds fuel true
          (ClosLetop.compileList (ClosTicks.removeList (opt.map Prod.fst)))
        exact ClosToBvl.compileCallMtiFuel_knownCall_labels fuel closure output knownConfig expressions called
          callState compiled names' mti calls known closureRun (by simpa [next, aligned, numbered, opt] using callRun)
      | true =>
        let transformed := ClosMti.introList closure.maxApp expressions
        let next := closure.nextLoc + max 1 transformed.length
        let aligned := if next % 2 = 0 then next else next + 1
        let numbered := (ClosNumber.renumberList aligned transformed).2
        let opt := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
        obtain ⟨⟨called, callState⟩, callRun⟩ := ClosCall.compileFuel_succeeds fuel true
          (ClosLetop.compileList (ClosTicks.removeList (opt.map Prod.fst)))
        exact ClosToBvl.compileCallMtiFuel_mtiKnownCall_labels fuel closure output knownConfig expressions called
          callState compiled names' mti calls known closureRun (by simpa [transformed, next, aligned, numbered, opt] using callRun)
    exact BvlToBvi.Proofs.optimizedLowerTailrecTmcInline_labels fuel bvlConfig.inlineSizeLimit bvlConfig.expCut
      fuel fuel output.start 0 bvlConfig.splitMainAtSeq bvlConfig.doTailrec bvlConfig.doTmc compiled optimized cache
      targetStart targetNext lowered beforeTmc afterTmc bviCode tailLast tmcLast bviCache distinct
      optimizedRun lowerRun tailRun tmcRun inlineRun

/-- The emitted word code has the candidate code relation when either known
optimization is enabled or direct-call conversion is disabled. The remaining
direct-call-only configuration still needs its label proof. -/
theorem compileCakeToWord64ConfiguredFuel_codeRel_knownOrNoCall (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (covered : closure.doCall = false ∨ closure.knownConf.isSome = true) :
    ∃ code, compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      DataToWord.Proofs.Gc.codeRel64 word (sptFromAList (BviToData.compileProg bviCode)) (sptFromAList code) := by
  have labels : (bviCode.map Prod.fst).Nodup ∧ ∀ label ∈ bviCode.map Prod.fst, dataNumStubs ≤ label := by
    rcases covered with calls | known
    · exact configured_bvi_labels_noCall fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
        declarations bviCode names run calls
    · cases h : closure.knownConf with
      | none => simp [h] at known
      | some knownConfig =>
        exact configured_bvi_labels_known fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
          declarations bviCode names run knownConfig h
  exact compileCakeToWord64ConfiguredFuel_codeRel_of_bviLabels fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run labels.1 labels.2

end Flapjack.Compiler.Backend.SourceToFlat
