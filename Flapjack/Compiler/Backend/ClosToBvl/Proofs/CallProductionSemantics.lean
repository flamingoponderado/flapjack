import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallPreparedSemantics
import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic

/-! Executed closure compiler with direct-call conversion enabled. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Multi-argument oracle pass specialized to closure programs. -/
noncomputable abbrev mtiInc (maxApp : Nat) : ClosSem.Program → ClosSem.Program := ClosMti.compileInc maxApp

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

/-- With known-function optimization disabled, the executable compiler
passes the multi-argument result through numbering and direct-call conversion
before preparing BVL code. -/
theorem compileCallMtiFuel_mtiCall_decompose (fuel : Nat) (config output : Config)
    (source transformed : List ClosLang.Exp) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (knownOff : config.knownConf = none) (callOn : config.doCall = true)
    (mtiRun : ClosMti.compileFuel fuel config.doMti config.maxApp source = some transformed)
    (run : compileCallMtiFuel? fuel config source = some (output, compiled, names)) :
    let next := config.nextLoc + max 1 transformed.length
    let aligned := if next % 2 = 0 then next else next + 1
    ∃ called callState,
      ClosCall.compileFuel fuel true (ClosNumber.renumberList aligned transformed).2 = some (called, callState) ∧
      compilePrepared? config
        { config with start := config.nextLoc, nextLoc := (ClosNumber.renumberList aligned transformed).1, knownConf := none, callState := callState } source
        (ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)) =
          some (output, compiled, names) := by
  simp only [compileCallMtiFuel?, mtiRun, knownOff, ClosKnown.compileFuel, callOn,
    Bind.bind, Option.bind, Pure.pure] at run
  cases callRun : ClosCall.compileFuel fuel true
      (ClosNumber.renumberList (if (config.nextLoc + max 1 transformed.length) % 2 = 0 then
        config.nextLoc + max 1 transformed.length else config.nextLoc + max 1 transformed.length + 1) transformed).2 with
  | none => simp [callRun] at run
  | some result =>
    obtain ⟨called, callState⟩ := result
    refine ⟨called, callState, callRun, ?_⟩
    simpa [callRun, callOn, knownOff] using run

/-- The direct-call driver produces distinct BVL labels with known-function
optimization disabled, for either multi-argument setting. This is a
Flapjack-side consequence of the numbering and call-pass invariants. -/
theorem compileCallMtiFuel_mtiCall_labels (fuel : Nat) (config output : Config)
    (source : List ClosLang.Exp) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (knownOff : config.knownConf = none) (callOn : config.doCall = true)
    (run : compileCallMtiFuel? fuel config source = some (output, compiled, names)) :
    (compiled.map Prod.fst).Nodup := by
  obtain ⟨transformed, mtiRun⟩ := ClosMti.compileFuel_succeeds fuel config.doMti config.maxApp source
  let next := config.nextLoc + max 1 transformed.length
  let aligned := if next % 2 = 0 then next else next + 1
  let numbered := (ClosNumber.renumberList aligned transformed).2
  obtain ⟨called, callState, callRun, prepared⟩ :=
    compileCallMtiFuel_mtiCall_decompose fuel config output source transformed compiled names
      knownOff callOn mtiRun run
  have numberEven : aligned % 2 = 0 := by dsimp [aligned]; split <;> omega
  have numberLower : config.nextLoc + max 1 transformed.length ≤ aligned := by
    dsimp [aligned, next]; split <;> omega
  have distinct : (codeLocations numbered).Nodup :=
    ClosNumber.renumberList_codeLocations_nodup transformed aligned
  have sourceEven : ∀ loc ∈ codeLocations numbered, loc % 2 = 0 := by
    intro loc member
    have parity := ClosNumber.renumberList_location_parity transformed aligned loc member
    omega
  have sourceLower : ∀ loc ∈ codeLocations numbered, config.nextLoc + max 1 numbered.length ≤ loc := by
    intro loc member
    have bounds := ClosNumber.renumberList_location_bounds transformed aligned loc member
    have length : numbered.length = transformed.length := ClosNumber.renumberList_length transformed aligned
    omega
  have rawDistinct := initialCall_annotated_chain_source_nodup fuel config.nextLoc numbered called callState
    (by simpa [numbered] using callRun) distinct sourceEven sourceLower
  exact compilePrepared_labels_nodup_of_source config
    { config with start := config.nextLoc, nextLoc := (ClosNumber.renumberList aligned transformed).1, knownConf := none, callState := callState } output source
    (ClosAnnotate.compile (chainExps config.nextLoc called ++ callState.2)) compiled names
    (by simpa [next, aligned] using prepared) rawDistinct

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

/-- The executed closure compiler preserves observations with both
multi-argument introduction and direct-call conversion enabled, when
known-function optimization is disabled and the stated source and oracle
conditions hold. -/
theorem compileCallMtiFuel_mtiCall_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel relationFuel : Nat) (config output : Config) (targetCompiler : BvlSem.Compiler C)
    (source called : List ClosLang.Exp) (callState : ClosCall.State)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : Nat → (Nat × (NumSet × C)) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (mtiOn : config.doMti = true) (knownOff : config.knownConf = none) (callOn : config.doCall = true)
    (positive : 1 ≤ config.maxApp)
    (unary : ∀ e ∈ source, noMti e)
    (oracleUnary : ∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, noMti e)
    (sourceVarsNone : everyFnVarsNone source) (sourceNonempty : source ≠ [])
    (oracleVarsNone : ∀ n, everyFnVarsNone (oracle n).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (mtiInc config.maxApp) ∘ oracle))
    (futureStartsAfter :
      let transformed := ClosMti.introList config.maxApp source
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      (ClosNumber.renumberList aligned transformed).1 ≤ (oracle 0).1.1)
    (passRun :
      let transformed := ClosMti.introList config.maxApp source
      let next := config.nextLoc + max 1 transformed.length
      let aligned := if next % 2 = 0 then next else next + 1
      ClosCall.compileFuel fuel true (ClosNumber.renumberList aligned transformed).2 = some (called, callState))
    (known : callState.1 = ((stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
      (pureCo (mtiInc config.maxApp) ∘ oracle)) 0).1.1)
    (sourceSafe : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (pureCc (mtiInc config.maxApp) (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) targetCompiler))))) source ≠ .fail)
    (run : compileCallMtiFuel? fuel config source = some (output, compiled, names)) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        ClosCall.compileIncFuelOracle fuel (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCo (mtiInc config.maxApp) ∘ oracle))) targetCompiler output.start =
    semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (pureCc (mtiInc config.maxApp) (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
          (pureCc (compileInc config.maxApp) targetCompiler))))) source := by
  let transformed := ClosMti.introList config.maxApp source
  let transformedOracle := pureCo (mtiInc config.maxApp) ∘ oracle
  let next := config.nextLoc + max 1 transformed.length
  let aligned := if next % 2 = 0 then next else next + 1
  let current := { config with start := config.nextLoc, nextLoc := (ClosNumber.renumberList aligned transformed).1, knownConf := none, callState := callState }
  let callCompiler := ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
    (pureCc (compileInc config.maxApp) targetCompiler))
  have mtiRun : ClosMti.compileFuel fuel config.doMti config.maxApp source = some transformed := by
    simpa [mtiOn, transformed] using ClosMti.compileFuel_introList fuel config.maxApp source
  have mtiSem := ClosMti.semantics_introMulti_candidate ffi config.maxApp oracle
    (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) callCompiler) source positive oracleUnary unary
  have transformedSafe : semantics ffi config.maxApp HolFiniteMapExact.empty transformedOracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) callCompiler) transformed ≠ .fail := by
    rw [← mtiSem]
    exact sourceSafe
  have transformedVars : everyFnVarsNone transformed :=
    (ClosMti.introList_varsNone config.maxApp source).1 sourceVarsNone
  have transformedNonempty : transformed ≠ [] := by
    intro empty
    have len := ClosMti.introList_length config.maxApp source
    have positiveLength := List.length_pos_iff.mpr sourceNonempty
    change transformed.length = source.length at len
    simp [empty] at len
    omega
  have futureVars : ∀ n, everyFnVarsNone (transformedOracle n).2.1 := by
    intro n
    simpa [transformedOracle, pureCo, mtiInc, ClosMti.compileInc] using
      (ClosMti.introList_varsNone config.maxApp (oracle n).2.1).1 (oracleVarsNone n)
  have futureAux : ∀ n, (transformedOracle n).2.2 = [] := by
    intro n
    simp [transformedOracle, pureCo, mtiInc, ClosMti.compileInc]
  have noApps : ¬ containsAppSome config.maxApp transformed :=
    ClosMti.introList_numberingSafe config.maxApp source positive unary
  have futureNoApps : ∀ n, ¬ containsAppSome config.maxApp (transformedOracle n).2.1 := by
    intro n
    simpa [transformedOracle, pureCo, mtiInc, ClosMti.compileInc] using
      ClosMti.introList_numberingSafe config.maxApp (oracle n).2.1 positive (oracleUnary n).2
  have even : aligned % 2 = 0 := by dsimp [aligned]; split <;> omega
  have reserved : current.start + transformed.length ≤ aligned := by dsimp [current, aligned, next]; split <;> omega
  obtain ⟨actual, actualState, actualRun, prepared⟩ :=
    compileCallMtiFuel_mtiCall_decompose fuel config output source transformed compiled names knownOff callOn mtiRun run
  have equal := Option.some.inj (actualRun.symm.trans passRun)
  cases equal
  have callSem := renumberedCall_to_preparedBvl_semantics ffi fuel relationFuel aligned config current output targetCompiler
    transformed called source callState compiled names transformedOracle oracleState transformedVars transformedNonempty
    even reserved futureStartsAfter passRun known futureVars futureAux noApps futureNoApps transformedSafe prepared
  exact callSem.trans mtiSem.symm

end Flapjack.Compiler.Backend.ClosToBvl
