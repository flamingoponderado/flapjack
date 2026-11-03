import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownPreparedSemantics

/-! Known-function optimization in the production closure driver. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- The production closure driver with known-function optimization enabled
and the multi-argument and direct-call passes disabled preserves the current
closure observations through BVL conversion. This Lean-side composition is
not a standalone HOL declaration; its oracle and source safety premises remain
explicit. -/
theorem compileCallMtiFuel_knownOnly_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel : Nat) (config output : Config) (knownConfig : ClosKnown.Config)
    (program : List ClosLang.Exp) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (targetCompiler : BvlSem.Compiler C)
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp)
    (run : compileCallMtiFuel? fuel config program = some (output, compiled, names))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))))))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome config.maxApp (oracle n).2.1)
    (knownSafe :
      let next := config.nextLoc + max 1 program.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned program).2
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound :
      let next := config.nextLoc + max 1 program.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned program).1 ≤ (oracle 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ knownClosureFuture knownConfig oracle)
      targetCompiler output.start =
    semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))))))) program := by
  let next := config.nextLoc + max 1 program.length
  let aligned := if next % 2 = 0 then next else next + 1
  have numberLower : config.nextLoc + max 1 program.length ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  cases numbered : ClosNumber.renumberList aligned program with
  | mk nextLoc numberedProgram =>
    cases knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numberedProgram) [] .ln with
    | mk optimized globals =>
      let optimizedOutput := ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))
      let current : Config := { config with start := config.nextLoc, nextLoc := nextLoc, knownConf := some { knownConfig with valApproxSpt := globals }, callState := (.ln, []) }
      have prepared : compilePrepared? config current program
          (ClosAnnotate.compile (chainExps config.nextLoc optimizedOutput)) = some (output, compiled, names) := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedProgram optimized globals knownRun
        simpa [compileCallMtiFuel?, mti, calls, known, ClosMti.compileFuel, ClosCall.compileFuel,
          numbered, knownCompiled, current, optimizedOutput, next, aligned] using run
      have sourceSafe : syntaxOracleOk knownConfig numberedProgram
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals := by
        simpa [next, aligned, numbered, knownRun] using knownSafe
      have boundary : nextLoc ≤ (oracle 0).1.1 := by
        simpa [next, aligned, numbered] using initialBound
      have optRun := ticks_letop_bounded fuel (optimized.map Prod.fst)
      have result := known_pipeline_prepared_semantics ffi fuel config.maxApp aligned config.nextLoc knownConfig
        oracle targetCompiler program optimized globals optimizedOutput config current output compiled names positive
        nonfail numberSafe (by simpa [numbered] using And.intro sourceSafe knownRun)
        optRun rfl rfl prepared numberLower oracleState (by simpa [numbered] using boundary)
      exact result

/-- The actual known-enabled driver emits distinct BVL labels. This is
Lean-side assembly infrastructure, not a separate HOL theorem. -/
theorem compileCallMtiFuel_knownOnly_labels (fuel : Nat) (config output : Config)
    (knownConfig : ClosKnown.Config) (program : List ClosLang.Exp) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = some knownConfig)
    (run : compileCallMtiFuel? fuel config program = some (output, compiled, names)) :
    (compiled.map Prod.fst).Nodup := by
  let next := config.nextLoc + max 1 program.length
  let aligned := if next % 2 = 0 then next else next + 1
  have numberLower : config.nextLoc + max 1 program.length ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  cases numbered : ClosNumber.renumberList aligned program with
  | mk nextLoc numberedProgram =>
    cases knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numberedProgram) [] .ln with
    | mk optimized globals =>
      let optimizedOutput := ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))
      let current : Config := { config with start := config.nextLoc, nextLoc := nextLoc, knownConf := some { knownConfig with valApproxSpt := globals }, callState := (.ln, []) }
      have prepared : compilePrepared? config current program
          (ClosAnnotate.compile (chainExps config.nextLoc optimizedOutput)) = some (output, compiled, names) := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedProgram optimized globals knownRun
        simpa [compileCallMtiFuel?, mti, calls, known, ClosMti.compileFuel, ClosCall.compileFuel,
          numbered, knownCompiled, current, optimizedOutput, next, aligned] using run
      have outputLabels := numberedKnown_output_labels fuel aligned knownConfig program optimized globals optimizedOutput
        (by simpa [numbered] using knownRun) (ticks_letop_bounded fuel (optimized.map Prod.fst))
      have numberingBound := ClosNumber.renumberList_start_le program aligned
      have entryBound : config.nextLoc + max 1 optimizedOutput.length ≤
          (ClosNumber.renumberList aligned program).1 := by
        rw [outputLabels.1]
        exact Nat.le_trans numberLower numberingBound
      have properties := preparedChain_label_properties config current output program config.nextLoc
        (ClosNumber.renumberList aligned program).1 optimizedOutput compiled names prepared outputLabels.2.1
        (by intro location member; have b := outputLabels.2.2 location member; omega) entryBound
      exact properties.1

end Flapjack.Compiler.Backend.ClosToBvl
