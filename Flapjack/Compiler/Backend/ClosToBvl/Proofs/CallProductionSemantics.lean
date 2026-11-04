import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallPreparedSemantics

/-! Executed closure compiler with direct-call conversion enabled. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- In the direct-call-only configuration, the production compiler uses
the numbered program and passes its generated auxiliary code to BVL
preparation. -/
theorem compileCallMtiFuel_callOnly_decompose (fuel : Nat) (config output : Config)
    (source : List ClosLang.Exp) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (mtiOff : config.doMti = false) (knownOff : config.knownConf = none)
    (callOn : config.doCall = true)
    (run : compileCallMtiFuel? fuel config source = some (output, compiled, names)) :
    let next := config.nextLoc + max 1 source.length
    let aligned := if next % 2 = 0 then next else next + 1
    ∃ called callState,
      ClosCall.compileFuel fuel true (ClosNumber.renumberList aligned source).2 = some (called, callState) ∧
      compilePrepared? config
        { config with start := config.nextLoc, nextLoc := (ClosNumber.renumberList aligned source).1, knownConf := none, callState := callState } source
        (ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)) =
          some (output, compiled, names) := by
  simp only [compileCallMtiFuel?, mtiOff, ClosMti.compileFuel, Bool.false_eq_true, ↓reduceIte,
    knownOff, ClosKnown.compileFuel, callOn, Bind.bind, Option.bind, Pure.pure] at run
  cases callRun : ClosCall.compileFuel fuel true
      (ClosNumber.renumberList (if (config.nextLoc + max 1 source.length) % 2 = 0 then
        config.nextLoc + max 1 source.length else config.nextLoc + max 1 source.length + 1) source).2 with
  | none => simp [callRun] at run
  | some result =>
    obtain ⟨called, callState⟩ := result
    refine ⟨called, callState, callRun, ?_⟩
    simpa [callRun, mtiOff, callOn] using run

/-- The executed direct-call-only closure compiler preserves closure
observations through BVL preparation under the stated source and oracle
conditions. Multi-argument introduction and known-function optimization
are disabled in this specialization. -/
theorem compileCallMtiFuel_callOnly_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel relationFuel : Nat) (config output : Config) (targetCompiler : BvlSem.Compiler C)
    (source called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (mtiOff : config.doMti = false) (knownOff : config.knownConf = none) (callOn : config.doCall = true)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (sourceVarsNone : everyFnVarsNone source) (sourceNonempty : source ≠ [])
    (futureStartsAfter :
      (ClosNumber.renumberList (if (config.nextLoc + max 1 source.length) % 2 = 0 then
        config.nextLoc + max 1 source.length else config.nextLoc + max 1 source.length + 1) source).1 ≤
        (oracle 0).1.1)
    (passRun : ClosCall.compileFuel fuel true
      (ClosNumber.renumberList (if (config.nextLoc + max 1 source.length) % 2 = 0 then
        config.nextLoc + max 1 source.length else config.nextLoc + max 1 source.length + 1) source).2 =
          some (called, callState))
    (known : callState.1 = ((stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) 0).1.1)
    (varsNone : ∀ n, everyFnVarsNone (oracle n).2.1) (oracleAuxEmpty : ∀ n, (oracle n).2.2 = [])
    (sourceNoApps : ¬ containsAppSome config.maxApp source)
    (oracleNoApps : ∀ n, ¬ containsAppSome config.maxApp (oracle n).2.1)
    (sourceSafe : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) targetCompiler)))) source ≠ .fail)
    (run : compileCallMtiFuel? fuel config source = some (output, compiled, names)) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        ClosCall.compileIncFuelOracle fuel (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
      targetCompiler output.start =
    semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) targetCompiler)))) source := by
  let next := config.nextLoc + max 1 source.length
  let aligned := if next % 2 = 0 then next else next + 1
  let current := { config with start := config.nextLoc, nextLoc := (ClosNumber.renumberList aligned source).1, knownConf := none, callState := callState }
  have even : aligned % 2 = 0 := by dsimp [aligned]; split <;> omega
  have reserved : current.start + source.length ≤ aligned := by
    dsimp [current, aligned, next]
    split <;> omega
  obtain ⟨actual, actualState, actualRun, prepared⟩ :=
    compileCallMtiFuel_callOnly_decompose fuel config output source compiled names mtiOff knownOff callOn run
  have equal := Option.some.inj (actualRun.symm.trans passRun)
  cases equal
  exact renumberedCall_to_preparedBvl_semantics ffi fuel relationFuel aligned config current output targetCompiler
    source called source callState compiled names oracle oracleState sourceVarsNone sourceNonempty even reserved
    futureStartsAfter passRun known varsNone oracleAuxEmpty sourceNoApps oracleNoApps sourceSafe prepared

end Flapjack.Compiler.Backend.ClosToBvl
