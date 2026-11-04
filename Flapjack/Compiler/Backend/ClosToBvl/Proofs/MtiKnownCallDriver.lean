import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownCallDriver
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiKnownDriverSemantics

/-! Multi-argument introduction, known-function optimization, and direct calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- Replaying the multi-argument output with the flag disabled preserves
compiled code and entry point with known and direct-call passes enabled. -/
theorem compileCallMtiFuel_mtiKnownCall_erasure (fuel : Nat) (config output : Config)
    (knownConfig : ClosKnown.Config) (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (run : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel fuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState)) :
    ∃ output' names',
      compileCallMtiFuel? fuel { config with doMti := false }
        (ClosMti.introList config.maxApp expressions) = some (output', compiled, names') ∧
      output'.start = output.start := by
  let transformed := ClosMti.introList config.maxApp expressions
  let next := config.nextLoc + max 1 transformed.length
  let aligned := if next % 2 = 0 then next else next + 1
  cases numbered : ClosNumber.renumberList aligned transformed with
  | mk nextLoc numberedExpressions =>
    cases knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile numberedExpressions) [] .ln with
    | mk optimized globals =>
      let optimizedOutput := ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))
      let current : Config := { config with doMti := false, start := config.nextLoc, nextLoc := nextLoc, knownConf := some { knownConfig with valApproxSpt := globals }, callState := callState }
      let source := ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)
      have callRun' : ClosCall.compileFuel fuel true optimizedOutput = some (called, callState) := by
        simpa [transformed, next, aligned, numbered, knownRun, optimizedOutput] using callRun
      have prepared : compilePrepared? config { current with doMti := config.doMti } expressions source =
          some (output, compiled, names) := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedExpressions optimized globals knownRun
        simpa [compileCallMtiFuel?, enabled, calls, known, ClosMti.compileFuel_introList,
          transformed, numbered, knownCompiled, callRun', current, optimizedOutput, source, next, aligned] using run
      obtain ⟨names', reference⟩ := compilePrepared_entries { config with doMti := false } current transformed source
      obtain ⟨actualNames, actual⟩ := compilePrepared_entries config { current with doMti := config.doMti } expressions source
      have result := Option.some.inj (prepared.symm.trans actual)
      have codeEq : compiled = codeSort (initialCompiledEntries current.maxApp current.start source) := by
        simpa using congrArg (fun x => x.2.1) result
      have startEq : output.start = numStubs current.maxApp - 1 := by
        simpa using congrArg (fun x => x.1.start) result
      let output' := { current with start := numStubs current.maxApp - 1 }
      have alternate : compileCallMtiFuel? fuel { config with doMti := false } transformed =
          some (output', compiled, names') := by
        have knownCompiled := known_compileFuel_eq fuel knownConfig numberedExpressions optimized globals knownRun
        simpa [compileCallMtiFuel?, calls, known, ClosMti.compileFuel, numbered, knownCompiled, callRun',
          current, optimizedOutput, source, next, aligned, output', codeEq] using reference
      exact ⟨output', names', alternate, startEq.symm⟩

/-- The executed driver emits distinct BVL labels with all three closure
optimizations enabled. -/
theorem compileCallMtiFuel_mtiKnownCall_labels (fuel : Nat) (config output : Config)
    (knownConfig : ClosKnown.Config) (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (run : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel fuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState)) : (compiled.map Prod.fst).Nodup := by
  obtain ⟨output', names', alternate, _⟩ :=
    compileCallMtiFuel_mtiKnownCall_erasure fuel config output knownConfig expressions called callState compiled names
      enabled calls known run callRun
  exact compileCallMtiFuel_knownCall_labels fuel { config with doMti := false } output' knownConfig
    (ClosMti.introList config.maxApp expressions) called callState compiled names' rfl
    (by simpa using calls) (by simpa using known) alternate (by simpa using callRun)

/-- The executed closure driver preserves observations with
multi-argument introduction, known-function optimization, and direct-call
conversion enabled, subject to the source and oracle safety premises. -/
theorem compileCallMtiFuel_mtiKnownCall_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel relationFuel : Nat) (config output : Config) (knownConfig : ClosKnown.Config)
    (expressions called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : CompileOracle (Nat × (Spt ValApprox × (NumSet × C)))) (targetCompiler : BvlSem.Compiler C)
    (enabled : config.doMti = true) (calls : config.doCall = true) (known : config.knownConf = some knownConfig)
    (positive : 1 ≤ config.maxApp) (nonempty : expressions ≠ [])
    (unary : ∀ e ∈ expressions, noMti e)
    (oracleUnary : ∀ i, (oracle i).2.2 = [] ∧ ∀ e ∈ (oracle i).2.1, noMti e)
    (run : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc (ClosMti.compileInc config.maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
            (pureCc ticksInc (pureCc letopInc
              (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
                (pureCc (compileInc config.maxApp) targetCompiler))))))))) expressions ≠ .fail)
    (knownSafe :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let transformedOracle := pureCo (ClosMti.compileInc config.maxApp) ∘ oracle
      let globals := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).2
      syntaxOracleOk knownConfig numbered (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) transformedOracle) globals)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (ClosMti.compileInc (Output := Nat × Nat × ClosLang.Exp) config.maxApp) ∘ oracle))
    (initialBound :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned transformed).1 ≤ (oracle 0).1.1)
    (callRun :
      let transformed := ClosMti.introList config.maxApp expressions
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      let numbered := (ClosNumber.renumberList aligned transformed).2
      let optimized := (ClosKnown.knownListTotal knownConfig (ClosFvs.compile numbered) [] .ln).1
      ClosCall.compileFuel fuel true (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) =
        some (called, callState))
    (knownState : callState.1 = (knownClosureFuture knownConfig
      (pureCo (ClosMti.compileInc config.maxApp) ∘ oracle) 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        ClosCall.compileIncFuelOracle fuel (knownClosureFuture knownConfig
          (pureCo (ClosMti.compileInc config.maxApp) ∘ oracle)))
      targetCompiler output.start =
    semantics ffi config.maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc (ClosMti.compileInc config.maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
            (pureCc ticksInc (pureCc letopInc
              (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
                (pureCc (compileInc config.maxApp) targetCompiler))))))))) expressions := by
  let transformed := ClosMti.introList config.maxApp expressions
  let transformedOracle : CompileOracle (Nat × (Spt ValApprox × (NumSet × C))) :=
    pureCo (ClosMti.compileInc config.maxApp) ∘ oracle
  let intermediate := stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
    (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
      (pureCc ticksInc (pureCc letopInc
        (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) targetCompiler)))))))
  have mtiEq := ClosMti.semantics_introMulti_candidate ffi config.maxApp oracle intermediate expressions
    positive oracleUnary unary
  have transformedNonfail : semantics ffi config.maxApp HolFiniteMapExact.holEmpty transformedOracle
      intermediate transformed ≠ .fail := by
    change semantics ffi config.maxApp HolFiniteMapExact.holEmpty
      (pureCo (ClosMti.compileInc config.maxApp) ∘ oracle) intermediate
      (ClosMti.introList config.maxApp expressions) ≠ .fail
    simp only [HolFiniteMapExact.holEmpty] at nonfail ⊢
    rw [← mtiEq]
    exact nonfail
  have transformedSafe : ¬ containsAppSome config.maxApp transformed :=
    ClosMti.introList_numberingSafe config.maxApp expressions positive unary
  have transformedOracleSafe : ∀ i, (transformedOracle i).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (transformedOracle i).2.1 := by
    intro i
    change (ClosMti.compileInc config.maxApp (oracle i).2).2 = [] ∧
      ¬ containsAppSome config.maxApp (ClosMti.compileInc config.maxApp (oracle i).2).1
    exact ⟨rfl, ClosMti.introList_numberingSafe config.maxApp _ positive (oracleUnary i).2⟩
  have transformedNonempty : transformed ≠ [] := by
    intro empty
    have len := ClosMti.introList_length config.maxApp expressions
    have sourceLength := List.length_pos_iff.mpr nonempty
    change transformed.length = expressions.length at len
    simp [empty] at len
    omega
  obtain ⟨output', names', alternate, starts⟩ :=
    compileCallMtiFuel_mtiKnownCall_erasure fuel config output knownConfig expressions called callState compiled names
      enabled calls known run callRun
  have compiledEq := compileCallMtiFuel_knownCall_semantics ffi fuel relationFuel { config with doMti := false } output' knownConfig
    transformed called callState compiled names' transformedOracle targetCompiler rfl (by simpa using calls) (by simpa using known)
    positive transformedNonempty alternate transformedNonfail ⟨transformedSafe, transformedOracleSafe⟩
    (by simpa [transformed, transformedOracle] using knownSafe) oracleState
    (by simpa [transformed, transformedOracle, pureCo] using initialBound)
    (by simpa [transformed] using callRun) knownState
  rw [starts] at compiledEq
  simp only [HolFiniteMapExact.holEmpty] at compiledEq ⊢
  exact compiledEq.trans mtiEq.symm

end Flapjack.Compiler.Backend.ClosToBvl
