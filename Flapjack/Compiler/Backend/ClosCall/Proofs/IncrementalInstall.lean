import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalCode
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantDirectCall

/-! Incremental installation under direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosSem ClosProps SemanticPrimitivesProps

/-- Extending target code preserves the fixed compiler-state relation. -/
theorem stateRelFuel_extendCode {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (states : StateRelFuel fuel g allowed source target)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (distinct : (g.2.map Prod.fst).Nodup)
    (growth : ∀ key value, target.code.lookup key = some value → code.lookup key = some value) :
    StateRelFuel fuel g allowed source { target with code := code } := by
  obtain ⟨ffi, clock, maxApp, globals, refs, sourceCode⟩ := states
  have grow : ∀ a b, ValueRelFuel fuel g allowed target.code a b → ValueRelFuel fuel g allowed code a b := by
    intro a b rel
    exact valueRelFuel_mono rel (stateExtends_refl g distinct) Set.Subset.rfl growth
  refine ⟨ffi, clock, maxApp, ?_, ?_, sourceCode⟩
  · apply List.Forall₂.imp (β := Option ClosSem.Value) ?_ globals
    intro a b related
    cases a <;> cases b <;> simp_all [optionRel]
  · refine ⟨refs.1, ?_⟩
    intro key value lookup
    obtain ⟨other, found, related⟩ := refs.2 key value lookup
    exact ⟨other, found, refRel_mono grow related⟩

/-- A non-type-error source installation has a matching target installation
using the executed incremental direct-call compiler. Freshness and distinct
source locations establish the target code checks. This fixed-state result
does not yet establish the full growing compiler-oracle invariant. -/
theorem doInstall_nonType_incremental {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (states : StateRelFuel relationFuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (distinctState : (g.2.map Prod.fst).Nodup)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (sourceAuxEmpty : (source.compileOracle 0).2.2 = [])
    (locationsDistinct : (codeLocations (source.compileOracle 0).2.1).Nodup)
    (fresh : ∀ loc ∈ codeLocations (source.compileOracle 0).2.1, target.code.lookup (loc + 1) = none)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ expressions converted nextKnown targetFinal,
      compileIncFuel? fuel (source.compileOracle 0).1.1 (expressions, []) = some (nextKnown, converted) ∧
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted.1, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions = (source.compileOracle 0).2.1 ∧ expressions ≠ [] ∧
      targetFinal.code = target.code.updateListEq converted.2 ∧
      targetFinal.compileOracle = holShiftSeq 1 target.compileOracle ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      StateRelFuel relationFuel g allowed final targetFinal ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  classical
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valueEq, bytesRun, wordsRun, oracleRun, compileRun, _, _, nextEq, nonempty, finalEq, resultEq⟩ :=
    doInstall_nonType_parts sourceValues source final result run notType
  have auxEmpty : auxiliary = [] := by simpa [oracleRun] using sourceAuxEmpty
  subst auxiliary
  subst sourceValues
  cases values with
  | cons bytesRel rest =>
    cases rest with
    | cons wordsRel rest =>
      cases rest
      rename_i targetByte targetWord
      have targetBytes : valueToBytes targetByte = some bytes := by
        rw [← ClosProps.simpleValRel_valueToBytes (ValueRelFuel relationFuel g allowed target.code) byteValue targetByte
          ⟨valueRelFuel_simple relationFuel g allowed target.code, bytesRel⟩, bytesRun]
      have targetWords : valueToWords targetWord = some words := by
        rw [← ClosProps.simpleValRel_valueToWords wordValue targetWord (ValueRelFuel relationFuel g allowed target.code)
          ⟨valueRelFuel_simple relationFuel g allowed target.code, wordsRel⟩, wordsRun]
      have callbackRun : compileIncFuelCallback fuel compiler (source.compileOracle 0).1
          (source.compileOracle 0).2 = some (bytes, words, nextConfig) := by
        simpa [sourceCompiler, oracleRun] using compileRun
      have nextOracle : (source.compileOracle (0 + 1)).1 = nextConfig := by
        simpa [holShiftSeq] using nextEq
      obtain ⟨targetCompile, converted, passRun, convertedEq⟩ :=
        compileIncFuelOracle_callback_head fuel compiler source.compileOracle 0 bytes words nextConfig.1 nextConfig.2
          (by simpa using callbackRun) (by simpa using nextOracle)
      have convertedRun : compileIncFuel? fuel config.1 (expressions, []) = some (nextConfig.1, converted) := by
        simpa [oracleRun] using passRun
      have targetOracleRun : target.compileOracle 0 = (config.2, converted) := by
        rw [targetOracle]
        simp only [convertedEq, compileIncFuelOracle, BackendProps.stateCo, oracleRun]
      have targetCompileRun : target.compile config.2 converted = some (bytes, words, nextConfig.2) := by
        rw [targetCompiler]
        simpa [oracleRun, convertedEq, compileIncFuelOracle, BackendProps.stateCo, nextOracle] using targetCompile
      have sourceDistinct : (codeLocations expressions).Nodup := by simpa [oracleRun] using locationsDistinct
      have sourceFresh : ∀ loc ∈ codeLocations expressions, target.code.lookup (loc + 1) = none := by
        simpa [oracleRun] using fresh
      have generated := compileIncFuel_generated fuel config.1 (expressions, []) nextConfig.1 converted
        convertedRun sourceDistinct
      have targetFresh := compileIncFuel_generated_fresh fuel config.1 (expressions, []) nextConfig.1 converted
        target.code convertedRun sourceFresh
      have targetFresh' : ∀ index arity body, (index, arity, body) ∈ converted.2 →
          target.code.lookup index = none := by
        intro index arity body member
        exact targetFresh index (List.mem_map.mpr ⟨(index, arity, body), member, rfl⟩)
      have codeGrowth := compileIncFuel_install_preserves fuel config.1 (expressions, []) nextConfig.1 converted
        target.code convertedRun sourceFresh
      have traversal := compileIncFuel_traversal fuel config.1 (expressions, []) nextConfig.1 converted convertedRun
      have length := callsListBounded_length fuel expressions (config.1, []) (nextConfig.1, converted.2)
        converted.1 traversal
      have targetNonempty : converted.1 ≠ [] := by
        intro empty
        rw [empty] at length
        exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
      have targetNext : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig.2 := by
        rw [targetOracle]
        simp [holShiftSeq, compileIncFuelOracle, BackendProps.stateCo, nextOracle]
      let targetFinal : ClosSem.State C F :=
        { target with
          code := target.code.updateListEq converted.2
          compileOracle := holShiftSeq 1 target.compileOracle
          clock := target.clock - 1 }
      refine ⟨expressions, converted, nextConfig.1, targetFinal, ?_, ?_, resultEq, ?_, nonempty,
        rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [oracleRun] using convertedRun
      · by_cases zero : source.clock = 0 <;>
          simp [doInstall, targetBytes, targetWords, targetOracleRun, targetCompileRun,
            targetNext, targetNonempty, generated.1, targetFinal, ← states.2.1, zero] <;>
          exact targetFresh'
      · simp [oracleRun]
      · simpa [finalEq] using sourceCompiler
      · exact targetCompiler
      · rw [finalEq]
        change holShiftSeq 1 target.compileOracle =
          compileIncFuelOracle fuel (holShiftSeq 1 source.compileOracle)
        rw [targetOracle]
        exact (compileIncFuelOracle_shift fuel 1 source.compileOracle).symm
      · rw [finalEq]
        have grown := stateRelFuel_extendCode states (target.code.updateListEq converted.2) distinctState codeGrowth
        have clocked := stateRelFuel_decClock grown 1
        simpa [StateRelFuel, targetFinal, decClock, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using clocked
      · exact codeGrowth

/-- After a non-type-error source installation, installing the transformed
head entry preserves freshness for all entries of the shifted source oracle,
provided the original later entries were fresh and disjoint from the head.
This is the future-code component of the invariant, not its full simulation. -/
theorem doInstall_shiftedOracle_fresh {C F : Type} (fuel : Nat)
    (source : ClosSem.State (NumSet × C) F) (sourceValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (oldCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (fresh : ∀ later, 0 < later → ∀ loc ∈ codeLocations (source.compileOracle later).2.1,
      oldCode.lookup (loc + 1) = none)
    (disjoint : ∀ later, 0 < later → ∀ loc ∈ codeLocations (source.compileOracle later).2.1,
      loc ∉ codeLocations (source.compileOracle 0).2.1) :
    ∀ index loc, loc ∈ codeLocations (final.compileOracle index).2.1 →
      (oldCode.updateListEq (compileIncFuelOracle fuel source.compileOracle 0).2.2).lookup (loc + 1) = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, finalEq, _⟩ :=
    doInstall_nonType_parts sourceValues source final result run notType
  have preserved := compileIncFuelOracle_preserves_later_fresh fuel source.compileOracle 0 oldCode fresh disjoint
  intro index loc member
  apply preserved (index + 1) (by omega) loc
  simpa [finalEq, holShiftSeq] using member

end Flapjack.Compiler.Backend.ClosCall
