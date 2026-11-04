import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownCallSemantics

/-! The production closure driver with known-function and direct-call passes. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- The executed closure driver preserves observations when known-function
optimization and direct-call conversion are enabled and multi-argument
introduction is disabled. Source and oracle safety remain explicit. -/
theorem compileCallMtiFuel_knownCall_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel relationFuel : Nat) (config output : Config) (knownConfig : ClosKnown.Config)
    (program called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (Nat × (Spt ValApprox × (NumSet × C)))) (targetCompiler : BvlSem.Compiler C)
    (mti : config.doMti = false) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp) (nonempty : program ≠ [])
    (run : compileCallMtiFuel? fuel config program = some (output, compiled, names))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
              (pureCc (compileInc config.maxApp) targetCompiler)))))))) program ≠ .fail)
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
      (ClosNumber.renumberList aligned program).1 ≤ (oracle 0).1.1)
    (callRun :
      let next := config.nextLoc + max 1 program.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned program).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel fuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState))
    (knownState : callState.1 = (knownClosureFuture knownConfig oracle 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        ClosCall.compileIncFuelOracle fuel (knownClosureFuture knownConfig oracle)) targetCompiler output.start =
    semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
              (pureCc (compileInc config.maxApp) targetCompiler)))))))) program := by
  let next := config.nextLoc + max 1 program.length
  let aligned := if next % 2 = 0 then next else next + 1
  have numberLower : config.nextLoc + max 1 program.length ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  have numberEven : aligned % 2 = 0 := by dsimp [aligned]; split <;> omega
  cases numbered : ClosNumber.renumberList aligned program with
  | mk nextLoc numberedProgram =>
    cases knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numberedProgram) [] .ln with
    | mk optimized globals =>
      let optimizedOutput := ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))
      let current : Config := { config with start := config.nextLoc, nextLoc := nextLoc, knownConf := some { knownConfig with valApproxSpt := globals }, callState := callState }
      have callRun' : ClosCall.compileFuel fuel true optimizedOutput = some (called, callState) := by
        simpa [next, aligned, numbered, knownRun, optimizedOutput] using callRun
      have prepared : compilePrepared? config current program
          (ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)) = some (output, compiled, names) := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedProgram optimized globals knownRun
        simpa [compileCallMtiFuel?, mti, calls, known, ClosMti.compileFuel, numbered,
          knownCompiled, callRun', current, optimizedOutput, next, aligned] using run
      have sourceSafe : syntaxOracleOk knownConfig numberedProgram
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals := by
        simpa [next, aligned, numbered, knownRun] using knownSafe
      have boundary : nextLoc ≤ (oracle 0).1.1 := by simpa [next, aligned, numbered] using initialBound
      have result := knownCall_prepared_semantics ffi fuel relationFuel aligned knownConfig oracle targetCompiler
        program optimized globals optimizedOutput called callState config current output compiled names positive nonempty
        numberEven numberLower oracleState (by simpa [numbered] using boundary) knownState
        nonfail numberSafe (by simpa [numbered] using And.intro sourceSafe knownRun)
        (ticks_letop_bounded fuel (optimized.map Prod.fst)) callRun' prepared
      exact result

/-- The executed known-function and direct-call driver emits distinct BVL
labels when multi-argument introduction is disabled. -/
theorem compileCallMtiFuel_knownCall_labels (fuel : Nat) (config output : Config)
    (knownConfig : ClosKnown.Config) (program called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (mti : config.doMti = false) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (run : compileCallMtiFuel? fuel config program = some (output, compiled, names))
    (callRun :
      let next := config.nextLoc + max 1 program.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned program).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel fuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState)) : (compiled.map Prod.fst).Nodup := by
  let next := config.nextLoc + max 1 program.length
  let aligned := if next % 2 = 0 then next else next + 1
  have numberLower : config.nextLoc + max 1 program.length ≤ aligned := by
    dsimp [aligned, next]
    split <;> omega
  have numberEven : aligned % 2 = 0 := by dsimp [aligned]; split <;> omega
  cases numbered : ClosNumber.renumberList aligned program with
  | mk nextLoc numberedProgram =>
    cases knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numberedProgram) [] .ln with
    | mk optimized globals =>
      let optimizedOutput := ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))
      let current : Config := { config with start := config.nextLoc, nextLoc := nextLoc, knownConf := some { knownConfig with valApproxSpt := globals }, callState := callState }
      have callRun' : ClosCall.compileFuel fuel true optimizedOutput = some (called, callState) := by
        simpa [next, aligned, numbered, knownRun, optimizedOutput] using callRun
      have prepared : compilePrepared? config current program
          (ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)) = some (output, compiled, names) := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedProgram optimized globals knownRun
        simpa [compileCallMtiFuel?, mti, calls, known, ClosMti.compileFuel, numbered,
          knownCompiled, callRun', current, optimizedOutput, next, aligned] using run
      exact knownCall_prepared_labels_nodup fuel aligned knownConfig program optimized globals optimizedOutput
        called callState config current output compiled names numberEven numberLower (by simpa [numbered] using knownRun)
        (ticks_letop_bounded fuel (optimized.map Prod.fst)) callRun' prepared

end Flapjack.Compiler.Backend.ClosToBvl
