import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalCode
import Flapjack.Compiler.Backend.ClosCall.Proofs.AuxiliaryAppend
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantDirectCall
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantListSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.InstallWellformed
import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracle
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantOrdinaryOp
import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation
import Flapjack.Compiler.Backend.ClosCall.Proofs.FunctionInvariant
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantRecursiveBinding
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantRetainedApplication
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantBodyPureApplication
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantBodyImpureApplication
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateOracleAdvance

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

/-- When the old compiler state's generated code is included in the target
map, target freshness implies freshness against that old auxiliary list. -/
theorem labelsFresh_of_codeIncludes (g : State) (locations : List Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (distinct : (g.2.map Prod.fst).Nodup) (included : codeIncludes g.2 code)
    (fresh : ∀ loc ∈ locations, code.lookup (loc + 1) = none) :
    LabelsFresh locations g := by
  intro loc member labelMember
  obtain ⟨⟨label, value⟩, entryMember, labelEq⟩ := List.mem_map.mp labelMember
  dsimp at labelEq
  subst label
  have lookup : logicalAssocLookup (loc + 1) g.2 = some value := by
    rw [logicalAssocLookup_nat]
    apply sptAListLookup_eq_of_mem_unique _ _ _ entryMember
    intro other otherMember
    have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst distinct)).mp distinct
    have eq : (loc + 1, other) = (loc + 1, value) := injective _ otherMember _ entryMember rfl
    exact congrArg Prod.snd eq
  have found := included (loc + 1) value lookup
  rw [fresh loc member] at found
  contradiction

/-- The installed map includes both the newly generated entries and the
previously included entries when installation preserves old lookups. -/
theorem codeIncludes_append_after_install
    (oldEntries newEntries : List (Nat × (Nat × ClosLang.Exp)))
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oldDistinct : (oldEntries.map Prod.fst).Nodup)
    (newDistinct : (newEntries.map Prod.fst).Nodup)
    (included : codeIncludes oldEntries code)
    (growth : ∀ key entry, code.lookup key = some entry →
      (code.updateListEq newEntries).lookup key = some entry) :
    codeIncludes (newEntries ++ oldEntries) (code.updateListEq newEntries) := by
  intro key value lookup
  rw [logicalAssocLookup_nat] at lookup
  have member := sptAListLookup_mem key (newEntries ++ oldEntries) value lookup
  rcases List.mem_append.mp member with newMember | oldMember
  · exact lookup_updateListEq_of_mem_unique code newEntries newDistinct key value newMember
  · apply growth key value
    apply included key value
    rw [logicalAssocLookup_nat]
    apply sptAListLookup_eq_of_mem_unique _ _ _ oldMember
    intro other otherMember
    have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst oldDistinct)).mp oldDistinct
    have eq : (key, other) = (key, value) := injective _ otherMember _ oldMember rfl
    exact congrArg Prod.snd eq

/-- A successful incremental installation extends the old compiler state
with its newly generated auxiliary code, provided the old state is well
formed and included in the pre-install target code. -/
theorem doInstall_nonType_compilerState_growth {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (states : StateRelFuel relationFuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (oldWell : wellFormed g) (included : codeIncludes g.2 target.code)
    (knownEq : g.1 = (source.compileOracle 0).1.1)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (sourceAuxEmpty : (source.compileOracle 0).2.2 = [])
    (locationsDistinct : (codeLocations (source.compileOracle 0).2.1).Nodup)
    (fresh : ∀ loc ∈ codeLocations (source.compileOracle 0).2.1, target.code.lookup (loc + 1) = none)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ expressions converted nextKnown targetFinal,
      compileIncFuel? fuel g.1 (expressions, []) = some (nextKnown, converted) ∧
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted.1, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions = (source.compileOracle 0).2.1 ∧ expressions ≠ [] ∧
      wellFormed (nextKnown, converted.2 ++ g.2) ∧ stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      targetFinal.code = target.code.updateListEq converted.2 ∧
      codeIncludes (converted.2 ++ g.2) targetFinal.code ∧
      StateRelFuel relationFuel (nextKnown, converted.2 ++ g.2) allowed final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq,
    nonempty, targetCodeEq, _, finalCompiler, targetFinalCompiler, oracleEq, finalStates, codeGrowth⟩ :=
    doInstall_nonType_incremental fuel relationFuel g allowed compiler source target sourceValues targetValues
      result final states values oldWell.2 sourceCompiler targetCompiler targetOracle sourceAuxEmpty
      locationsDistinct fresh run notType
  have passRun' : compileIncFuel? fuel g.1 (expressions, []) = some (nextKnown, converted) := by
    simpa [knownEq] using passRun
  have oldFresh : LabelsFresh (codeLocations expressions) g := by
    apply labelsFresh_of_codeIncludes g (codeLocations expressions) target.code oldWell.2 included
    simpa [exprEq] using fresh
  have sourceDistinct : (codeLocations expressions).Nodup := by simpa [exprEq] using locationsDistinct
  have merged := compileIncFuel_merge_state fuel g.1 g.2 (expressions, []) nextKnown converted
    passRun' oldWell sourceDistinct oldFresh
  have gEq : (g.1, g.2) = g := by cases g; rfl
  have mergedWell : wellFormed (nextKnown, converted.2 ++ g.2) := merged.1
  have extended : stateExtends g (nextKnown, converted.2 ++ g.2) := by
    simpa only [gEq] using merged.2
  have newDistinct : (converted.2.map Prod.fst).Nodup := by
    exact (compileIncFuel_generated fuel g.1 (expressions, []) nextKnown converted passRun' sourceDistinct).1
  have combinedIncluded : codeIncludes (converted.2 ++ g.2) targetFinal.code := by
    rw [targetCodeEq]
    apply codeIncludes_append_after_install g.2 converted.2 target.code oldWell.2 newDistinct included
    simpa [targetCodeEq] using codeGrowth
  refine ⟨expressions, converted, nextKnown, targetFinal, passRun', targetRun, resultEq, exprEq,
    nonempty, mergedWell, extended, targetCodeEq, combinedIncluded, ?_, finalCompiler,
    targetFinalCompiler, oracleEq, codeGrowth⟩
  exact stateRelFuel_mono finalStates extended Set.Subset.rfl

/-- Conditions on the remaining source oracle and target code needed for
successive incremental installations. This Lean-side invariant does not
establish evaluation simulation. -/
structure IncrementalInstallReady {C F : Type} (g : State)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) : Prop where
  well : wellFormed g
  included : codeIncludes g.2 target.code
  known : g.1 = (source.compileOracle 0).1.1
  auxEmpty : ∀ index, (source.compileOracle index).2.2 = []
  distinct : ∀ index, (codeLocations (source.compileOracle index).2.1).Nodup
  disjoint : ∀ earlier later, earlier < later → ∀ loc ∈ codeLocations (source.compileOracle later).2.1,
    loc ∉ codeLocations (source.compileOracle earlier).2.1
  fresh : ∀ index loc, loc ∈ codeLocations (source.compileOracle index).2.1 →
    target.code.lookup (loc + 1) = none

/-- Future source installations avoid the locations of currently open
closures. This is one component of the HOL oracle monotonicity invariant;
it is Flapjack-specific and does not assert the remaining components. -/
def OracleLocationsAvoid {C F : Type} (allowed : Set Nat) (source : ClosSem.State C F) : Prop :=
  ∀ index loc, loc ∈ codeLocations (source.compileOracle index).2.1 → loc ∉ allowed

/-- Oracle-location avoidance survives any finite oracle shift. This is
Flapjack-specific infrastructure for the open-location invariant. -/
theorem oracleLocationsAvoid_of_advance {C F : Type} (allowed : Set Nat)
    (source final : ClosSem.State C F)
    (advance : OracleAdvance source.compileOracle final.compileOracle)
    (avoids : OracleLocationsAvoid allowed source) : OracleLocationsAvoid allowed final := by
  obtain ⟨offset, shifted⟩ := advance
  intro index loc member
  apply avoids (index + offset) loc
  simpa [shifted, holShiftSeq] using member

/-- Every expression evaluation preserves oracle-location avoidance,
including timeouts and installation errors. This is Flapjack-specific
infrastructure based on the evaluator's oracle-advance theorem. -/
theorem evaluate_oracleLocationsAvoid {C F : Type} (allowed : Set Nat)
    (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
    (source final : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (run : evaluate expressions env source = (result, final))
    (avoids : OracleLocationsAvoid allowed source) : OracleLocationsAvoid allowed final := by
  exact oracleLocationsAvoid_of_advance allowed source final
    ((evaluate_oracle_advance (C := C) (F := F)).1 expressions env source final result run) avoids

/-- Closure application preserves oracle-location avoidance for every
result. This is Flapjack-specific infrastructure. -/
theorem evaluateApp_oracleLocationsAvoid {C F : Type} (allowed : Set Nat)
    (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
    (source final : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (run : evaluateApp location function args source = (result, final))
    (avoids : OracleLocationsAvoid allowed source) : OracleLocationsAvoid allowed final := by
  have advance := (evaluate_oracle_advance (C := C) (F := F)).2 (source.clock + 1)
    location function args source final result (by omega) run
  exact oracleLocationsAvoid_of_advance allowed source final advance avoids

/-- A non-type-error installation shifts the source oracle and preserves
avoidance of the open locations. This is Flapjack-specific infrastructure. -/
theorem doInstall_nonType_oracleLocationsAvoid {C F : Type} (allowed : Set Nat)
    (values : List ClosSem.Value) (source final : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (run : doInstall values source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (avoids : OracleLocationsAvoid allowed source) : OracleLocationsAvoid allowed final := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, finalEq, _⟩ :=
    doInstall_nonType_parts values source final result run notType
  intro index loc member
  apply avoids (index + 1) loc
  simpa [finalEq, holShiftSeq] using member

/-- A non-type-error installation advances the oracle and preserves the
conditions for later installations, along with the growing state relation.
The result applies to the actual incremental callback and target code update. -/
theorem doInstall_nonType_ready {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ expressions converted nextKnown targetFinal,
      compileIncFuel? fuel g.1 (expressions, []) = some (nextKnown, converted) ∧
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted.1, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions = (source.compileOracle 0).2.1 ∧ expressions ≠ [] ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) final targetFinal ∧
      StateRelFuel relationFuel (nextKnown, converted.2 ++ g.2) allowed final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq,
    nonempty, newWell, extended, codeEq, included, finalStates, finalCompiler, targetFinalCompiler,
    oracleEq, growth⟩ :=
    doInstall_nonType_compilerState_growth fuel relationFuel g allowed compiler source target sourceValues
      targetValues result final states values ready.well ready.included ready.known sourceCompiler
      targetCompiler targetOracle (ready.auxEmpty 0) (ready.distinct 0) (ready.fresh 0) run notType
  obtain ⟨_, _, bytes, words, config, input, aux, nextConfig, _, _, _, oracleRun, compileRun,
    _, _, nextEq, _, finalEq, _⟩ := doInstall_nonType_parts sourceValues source final result run notType
  have emptyAux : aux = [] := by simpa [oracleRun] using ready.auxEmpty 0
  have callback : compileIncFuelCallback fuel compiler config (input, aux) =
      some (bytes, words, nextConfig) := by simpa [sourceCompiler] using compileRun
  obtain ⟨actual, actualRun, _⟩ := compileIncFuelCallback_success fuel compiler config.1 config.2
    (input, aux) bytes words nextConfig.1 nextConfig.2 (by simpa using callback)
  have inputEq : input = expressions := by simpa [oracleRun] using exprEq.symm
  have configEq : config.1 = g.1 := by simpa [oracleRun] using ready.known.symm
  have sameRun : compileIncFuel? fuel config.1 (input, aux) = some (nextKnown, converted) := by
    simpa [inputEq, configEq, emptyAux] using passRun
  rw [sameRun] at actualRun
  have nextKnownEq : nextConfig.1 = nextKnown := congrArg Prod.fst (Option.some.inj actualRun).symm
  have newKnown : nextKnown = (final.compileOracle 0).1.1 := by
    rw [finalEq]
    simpa [nextKnownEq] using congrArg Prod.fst nextEq.symm
  have laterFresh := doInstall_shiftedOracle_fresh fuel source sourceValues result final target.code run notType
    (fun later _ => ready.fresh later) (fun later positive => ready.disjoint 0 later positive)
  have newReady : IncrementalInstallReady (nextKnown, converted.2 ++ g.2) final targetFinal := by
    refine ⟨newWell, included, newKnown, ?_, ?_, ?_, ?_⟩
    · intro index
      simpa [finalEq, holShiftSeq] using ready.auxEmpty (index + 1)
    · intro index
      simpa [finalEq, holShiftSeq] using ready.distinct (index + 1)
    · intro earlier later order loc member
      have disjoint := ready.disjoint (earlier + 1) (later + 1) (by omega) loc
        (by simpa [finalEq, holShiftSeq] using member)
      simpa [finalEq, holShiftSeq] using disjoint
    · intro index loc member
      rw [codeEq]
      have convertedEq : converted = (compileIncFuelOracle fuel source.compileOracle 0).2 := by
        obtain ⟨k, oraclePass, _⟩ := compileIncFuelOracle_entry fuel source.compileOracle 0
        have same : compileIncFuel? fuel (source.compileOracle 0).1.1 (source.compileOracle 0).2 =
            some (nextKnown, converted) := by
          simpa [oracleRun, emptyAux, configEq, inputEq] using passRun
        rw [same] at oraclePass
        exact (Prod.mk.inj (Option.some.inj oraclePass)).2
      rw [convertedEq]
      exact laterFresh index loc member
  refine ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq,
    nonempty, extended, newReady, finalStates, finalCompiler, targetFinalCompiler, oracleEq, growth⟩

/-- A non-type-error installation preserves both open-location disjointness
and avoidance by the remaining source oracle. This is Flapjack-specific
infrastructure for the disjointness part of the HOL code invariant. -/
theorem doInstall_nonType_ready_disjoint {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (disjoint : Disjoint allowed (sptDomain g.1))
    (avoids : OracleLocationsAvoid allowed source) :
    ∃ expressions converted nextKnown targetFinal,
      compileIncFuel? fuel g.1 (expressions, []) = some (nextKnown, converted) ∧
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted.1, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions = (source.compileOracle 0).2.1 ∧ expressions ≠ [] ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) final targetFinal ∧
      StateRelFuel relationFuel (nextKnown, converted.2 ++ g.2) allowed final targetFinal ∧
      Disjoint allowed (sptDomain nextKnown) ∧ OracleLocationsAvoid allowed final ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq,
    nonempty, extended, newReady, newStates, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      result final ready states values sourceCompiler targetCompiler targetOracle run notType
  have sourceAvoids : ∀ loc ∈ codeLocations expressions, loc ∉ allowed := by
    intro loc member
    apply avoids 0 loc
    simpa [exprEq] using member
  have newDisjoint := compileIncFuel_disjoint_known fuel g.1 (expressions, []) nextKnown converted allowed
    passRun disjoint sourceAvoids
  exact ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq, nonempty,
    extended, newReady, newStates, newDisjoint,
    doInstall_nonType_oracleLocationsAvoid allowed sourceValues source final result run notType avoids,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Installation can enlarge the open-location set by the current program's
locations that remain unknown after compilation. The enlarged set stays
disjoint from known locations and from every later oracle program, and the
related states remain related under it. This is Flapjack-specific
infrastructure for the open-set component of the HOL invariant. -/
theorem doInstall_nonType_ready_open_growth {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (disjoint : Disjoint allowed (sptDomain g.1))
    (avoids : OracleLocationsAvoid allowed source) :
    ∃ expressions converted nextKnown targetFinal nextAllowed,
      compileIncFuel? fuel g.1 (expressions, []) = some (nextKnown, converted) ∧
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted.1, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions = (source.compileOracle 0).2.1 ∧ expressions ≠ [] ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) final targetFinal ∧
      allowed ⊆ nextAllowed ∧
      (∀ loc ∈ codeLocations expressions, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) ∧
      Disjoint nextAllowed (sptDomain nextKnown) ∧ OracleLocationsAvoid nextAllowed final ∧
      StateRelFuel relationFuel (nextKnown, converted.2 ++ g.2) nextAllowed final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetFinal, passRun, targetRun, resultEq, exprEq,
    nonempty, extended, newReady, newStates, oldDisjoint, oldAvoids, finalCompiler,
    targetFinalCompiler, finalOracle, codeGrowth⟩ :=
    doInstall_nonType_ready_disjoint fuel relationFuel g allowed compiler source target sourceValues targetValues
      result final ready states values sourceCompiler targetCompiler targetOracle run notType disjoint avoids
  let nextAllowed : Set Nat := allowed ∪ { loc | loc ∈ codeLocations expressions ∧ ¬ sptDomain nextKnown loc }
  have allowedGrowth : allowed ⊆ nextAllowed := Set.subset_union_left
  have coverage : ∀ loc ∈ codeLocations expressions, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed := by
    intro loc member unknown
    exact Or.inr ⟨member, unknown⟩
  have nextDisjoint : Disjoint nextAllowed (sptDomain nextKnown) := by
    apply Set.disjoint_left.mpr
    intro loc member known
    rcases member with old | ⟨_, unknown⟩
    · exact Set.disjoint_left.mp oldDisjoint old known
    · exact unknown known
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, finalEq, _⟩ :=
    doInstall_nonType_parts sourceValues source final result run notType
  have nextAvoids : OracleLocationsAvoid nextAllowed final := by
    intro index loc laterMember member
    rcases member with old | ⟨currentMember, _⟩
    · exact oldAvoids index loc laterMember old
    · have laterOriginal : loc ∈ codeLocations (source.compileOracle (index + 1)).2.1 := by
        simpa [finalEq, holShiftSeq] using laterMember
      have separate := ready.disjoint 0 (index + 1) (by omega) loc laterOriginal
      apply separate
      simpa [exprEq] using currentMember
  have nextStates := stateRelFuel_mono newStates
    (stateExtends_refl (nextKnown, converted.2 ++ g.2) newReady.well.2) allowedGrowth
  exact ⟨expressions, converted, nextKnown, targetFinal, nextAllowed, passRun, targetRun, resultEq, exprEq,
    nonempty, extended, newReady, allowedGrowth, coverage, nextDisjoint, nextAvoids, nextStates,
    finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩

/-- Simulation at empty environments for source evaluations starting below a
clock bound. It is Lean-side infrastructure for the installed-program case. -/
def InstalledProgramSimBelow {C F : Type} (passFuel fuel limit : Nat) (compiler : ClosSem.Compiler C)
    (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp) : Prop :=
  ∀ (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit →
    evaluate program [] source = (result, final) →
    result ≠ .err (.abort .typeError) →
    StateWellFormedFuel fuel g allowed target.code source →
    StateRelFuel fuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧
      evaluate targetProgram [] target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel finalG allowed targetFinal.code))
        (ValueRelFuel fuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel fuel finalG allowed final targetFinal ∧
      StateWellFormedFuel fuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Installed-program simulation with existential target clock allowance.
This is Flapjack-specific infrastructure, not a HOL correctness theorem. -/
def InstalledProgramSimBelowWithClock {C F : Type} (passFuel fuel limit : Nat) (compiler : ClosSem.Compiler C)
    (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp) : Prop :=
  ∀ (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit →
    evaluate program [] source = (result, final) →
    result ≠ .err (.abort .typeError) →
    StateWellFormedFuel fuel g allowed target.code source →
    StateRelFuel fuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧
      evaluate targetProgram [] { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel finalG allowed targetFinal.code))
        (ValueRelFuel fuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel fuel finalG allowed final targetFinal ∧
      StateWellFormedFuel fuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Installed-program simulation allowing both target clock and open locations
to grow. This is Flapjack-specific induction infrastructure. -/
def InstalledProgramSimBelowWithOpenClock {C F : Type} (passFuel fuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp) : Prop :=
  ∀ (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit →
    evaluate program [] source = (result, final) →
    result ≠ .err (.abort .typeError) →
    StateWellFormedFuel fuel g allowed target.code source →
    StateRelFuel fuel g allowed source target →
    IncrementalInstallReady g source target →
    Disjoint allowed (sptDomain g.1) → OracleLocationsAvoid allowed source →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ extraClock finalG finalAllowed targetResult targetFinal,
      stateExtends g finalG ∧ allowed ⊆ finalAllowed ∧
      Disjoint finalAllowed (sptDomain finalG.1) ∧ OracleLocationsAvoid finalAllowed final ∧
      evaluate targetProgram [] { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel finalG finalAllowed targetFinal.code))
        (ValueRelFuel fuel finalG finalAllowed targetFinal.code) result targetResult ∧
      StateRelFuel fuel finalG finalAllowed final targetFinal ∧
      StateWellFormedFuel fuel finalG finalAllowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- A successfully installed source program can use the list-simulation
induction hypothesis at the compiler state produced by the actual incremental
pass. This is the installed-program part of the Lean-side simulation; the
argument evaluation and preservation of the oracle invariant through the
program remain separate obligations. -/
theorem doInstall_success_evaluate {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (programIH : ∀ nextKnown converted,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) allowed program converted.1) :
    ∃ nextKnown converted targetInstalled finalG targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      evaluate converted.1 [] targetInstalled = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetInstalled, passRun, targetRun, resultEq,
    _, _, extended, newReady, newStates, installedCompiler, targetInstalledCompiler,
    installedOracle, installGrowth⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = expressions := by simpa [nonzero] using resultEq
  have programPass : compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) := by
    simpa [programEq] using passRun
  have targetInstall : doInstall targetValues target = (.val converted.1, targetInstalled) := by
    simpa [nonzero] using targetRun
  have installedWf := doInstall_wellFormedFuel sourceValues source installed (.val program)
    sourceWf (ready.auxEmpty 0) installRun
  have installedWf' := stateWellFormedFuel_mono installedWf extended Set.Subset.rfl installGrowth
  have smaller : installed.clock < source.clock := by
    have clock := doInstall_success_clock sourceValues source installed program installRun
    omega
  obtain ⟨finalG, targetResult, targetFinal, bodyExtended, targetEval, related, finalStates,
    finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, bodyGrowth⟩ :=
    programIH nextKnown converted programPass installed targetInstalled result final smaller programRun notType
      installedWf' newStates newReady installedCompiler targetInstalledCompiler installedOracle
  exact ⟨nextKnown, converted, targetInstalled, finalG, targetResult, targetFinal, programPass, targetInstall,
    newReady, extended, bodyExtended, targetEval, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle,
    fun key entry found => bodyGrowth key entry (installGrowth key entry found)⟩

/-- A successful installation can invoke a clock-allowing simulation of
the installed program. This is Flapjack-specific induction infrastructure;
the caller must still account for the allowance in the enclosing evaluation. -/
theorem doInstall_success_evaluate_withClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (programIH : ∀ nextKnown converted,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelowWithClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) allowed program converted.1) :
    ∃ nextKnown converted targetInstalled extraClock finalG targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      doInstall targetValues { target with clock := target.clock + extraClock } =
        (.val converted.1, { targetInstalled with clock := targetInstalled.clock + extraClock }) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      evaluate converted.1 [] { targetInstalled with clock := targetInstalled.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetInstalled, passRun, targetRun, resultEq,
    _, _, extended, newReady, newStates, installedCompiler, targetInstalledCompiler,
    installedOracle, installGrowth⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = expressions := by simpa [nonzero] using resultEq
  have programPass : compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) := by
    simpa [programEq] using passRun
  have targetInstall : doInstall targetValues target = (.val converted.1, targetInstalled) := by
    simpa [nonzero] using targetRun
  have installedWf := doInstall_wellFormedFuel sourceValues source installed (.val program)
    sourceWf (ready.auxEmpty 0) installRun
  have installedWf' := stateWellFormedFuel_mono installedWf extended Set.Subset.rfl installGrowth
  have smaller : installed.clock < source.clock := by
    have clock := doInstall_success_clock sourceValues source installed program installRun
    omega
  obtain ⟨extraClock, finalG, targetResult, targetFinal, bodyExtended, targetEval, related, finalStates,
    finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, bodyGrowth⟩ :=
    programIH nextKnown converted programPass installed targetInstalled result final smaller programRun notType
      installedWf' newStates newReady installedCompiler targetInstalledCompiler installedOracle
  exact ⟨nextKnown, converted, targetInstalled, extraClock, finalG, targetResult, targetFinal,
    programPass, targetInstall, doInstall_success_addClock targetValues target targetInstalled converted.1
      extraClock targetInstall, newReady, extended, bodyExtended, targetEval, related, finalStates, finalWf,
    finalReady, finalCompiler, targetFinalCompiler, finalOracle,
    fun key entry found => bodyGrowth key entry (installGrowth key entry found)⟩

/-- A successful installation supplies the enlarged open-location set to the
installed-program induction hypothesis. This is Flapjack-specific simulation
infrastructure; it does not by itself establish that induction hypothesis. -/
theorem doInstall_success_evaluate_withOpenClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (disjoint : Disjoint allowed (sptDomain g.1))
    (avoids : OracleLocationsAvoid allowed source)
    (programIH : ∀ nextKnown converted nextAllowed,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      (∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) →
      InstalledProgramSimBelowWithOpenClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) nextAllowed program converted.1) :
    ∃ nextKnown converted targetInstalled nextAllowed extraClock finalG finalAllowed targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      doInstall targetValues { target with clock := target.clock + extraClock } =
        (.val converted.1, { targetInstalled with clock := targetInstalled.clock + extraClock }) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      allowed ⊆ nextAllowed ∧ nextAllowed ⊆ finalAllowed ∧
      (∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) ∧
      Disjoint finalAllowed (sptDomain finalG.1) ∧ OracleLocationsAvoid finalAllowed final ∧
      evaluate converted.1 [] { targetInstalled with clock := targetInstalled.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG finalAllowed targetFinal.code))
        (ValueRelFuel relationFuel finalG finalAllowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG finalAllowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG finalAllowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, converted, nextKnown, targetInstalled, nextAllowed, passRun, targetRun, resultEq,
    _, _, extended, newReady, allowedGrowth, coverage, nextDisjoint, nextAvoids, newStates,
    installedCompiler, targetInstalledCompiler, installedOracle, installGrowth⟩ :=
    doInstall_nonType_ready_open_growth fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
      disjoint avoids
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = expressions := by simpa [nonzero] using resultEq
  have programPass : compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) := by
    simpa [programEq] using passRun
  have programCoverage : ∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed := by
    simpa [programEq] using coverage
  have targetInstall : doInstall targetValues target = (.val converted.1, targetInstalled) := by
    simpa [nonzero] using targetRun
  have installedWf := doInstall_wellFormedFuel sourceValues source installed (.val program)
    sourceWf (ready.auxEmpty 0) installRun
  have installedWf' := stateWellFormedFuel_mono installedWf extended allowedGrowth installGrowth
  have smaller : installed.clock < source.clock := by
    have clock := doInstall_success_clock sourceValues source installed program installRun
    omega
  obtain ⟨extraClock, finalG, finalAllowed, targetResult, targetFinal, bodyExtended, bodyAllowed,
    finalDisjoint, finalAvoids, targetEval, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, bodyGrowth⟩ :=
    programIH nextKnown converted nextAllowed programPass programCoverage installed targetInstalled result final
      smaller programRun notType installedWf' newStates newReady nextDisjoint nextAvoids
      installedCompiler targetInstalledCompiler installedOracle
  exact ⟨nextKnown, converted, targetInstalled, nextAllowed, extraClock, finalG, finalAllowed,
    targetResult, targetFinal, programPass, targetInstall,
    doInstall_success_addClock targetValues target targetInstalled converted.1 extraClock targetInstall,
    newReady, extended, bodyExtended, allowedGrowth, bodyAllowed, programCoverage, finalDisjoint,
    finalAvoids, targetEval, related, finalStates, finalWf, finalReady, finalCompiler,
    targetFinalCompiler, finalOracle, fun key entry found => bodyGrowth key entry (installGrowth key entry found)⟩

/-- Related nonempty result lists have related HOL last elements. This is
used by the install evaluator, which returns only the installed program's
last result. -/
theorem forall₂_holLast {A B : Type} [Nonempty A] [Nonempty B] {R : A → B → Prop}
    {xs : List A} {ys : List B} (related : List.Forall₂ R xs ys) (nonempty : xs ≠ []) :
    R (holLast xs) (holLast ys) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons a b as bs head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons a' b' as' bs' head' tail' =>
      simp only [holLast]
      exact ih (by simp)

/-- Returning the last value of a nonempty installed program preserves the
result relation, including exceptions and aborts. -/
theorem resultRel_install_last {C F : Type} {R : ClosSem.Value → ClosSem.Value → Prop}
    (program : List ClosLang.Exp) (start last : ClosSem.State C F)
    (source target : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (programNonempty : program ≠ []) (run : evaluate program [] start = (source, last))
    (related : resultRel (List.Forall₂ R) R source target) :
    resultRel (List.Forall₂ R) R
      (match source with
       | .err error => .err error
       | .val values => .val [@holLast ClosSem.Value ⟨unitValue⟩ values])
      (match target with
       | .err error => .err error
       | .val values => .val [@holLast ClosSem.Value ⟨unitValue⟩ values]) := by
  cases source with
  | err error =>
    cases target with
    | err targetError => exact related
    | val values => exact related.elim
  | val values =>
    cases target with
    | err error => exact related.elim
    | val targets =>
      have length := (evaluate_length (C := C) (F := F)).1 program [] start last values run
      have valuesNonempty : values ≠ [] := by
        intro empty
        subst values
        exact programNonempty (List.eq_nil_of_length_eq_zero length.symm)
      exact .cons (@forall₂_holLast ClosSem.Value ClosSem.Value ⟨unitValue⟩ ⟨unitValue⟩ R
        values targets related valuesNonempty) .nil

/-- A successful installation supplies the nonempty-program premise needed
to relate the evaluator's final-value results. -/
theorem doInstall_success_resultRel_last {C F : Type} {R : ClosSem.Value → ClosSem.Value → Prop}
    (values : List ClosSem.Value) (source installed last : ClosSem.State C F)
    (program : List ClosLang.Exp)
    (sourceResult targetResult : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (installRun : doInstall values source = (.val program, installed))
    (programRun : evaluate program [] installed = (sourceResult, last))
    (related : resultRel (List.Forall₂ R) R sourceResult targetResult) :
    resultRel (List.Forall₂ R) R
      (match sourceResult with
       | .err error => .err error
       | .val results => .val [@holLast ClosSem.Value ⟨unitValue⟩ results])
      (match targetResult with
       | .err error => .err error
       | .val results => .val [@holLast ClosSem.Value ⟨unitValue⟩ results]) := by
  obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, _, _, _, _, _, nonempty, _, resultEq⟩ :=
    doInstall_nonType_parts values source installed (.val program) installRun (by simp)
  have programEq : program = expressions := by
    split at resultEq <;> simp_all
  have programNonempty : program ≠ [] := by simpa [programEq] using nonempty
  have lastRelated := resultRel_install_last program installed last sourceResult targetResult
    programNonempty programRun related
  cases sourceResult <;> cases targetResult <;> exact lastRelated

/-- The installed-program continuation simulates using the actual incremental
compiler step. The program simulation is an induction hypothesis; this does
not yet include evaluation of the install expression's arguments. -/
theorem runInstalled_incremental_sim {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : ClosProps.AdjustOracle.runInstalled sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (programIH : ∀ program nextKnown converted,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧
      ClosProps.AdjustOracle.runInstalled targetValues target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  unfold ClosProps.AdjustOracle.runInstalled at run ⊢
  cases installRun : doInstall sourceValues source with
  | mk installResult installed =>
    rw [installRun] at run
    cases installResult with
    | err error =>
      have installSafe : (SemanticPrimitivesHOL.Result.err error :
          SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value) ≠ .err (.abort .typeError) := by
        intro bad
        have equal : error = .abort .typeError := by cases bad; rfl
        cases run
        exact notType (by rw [equal])
      obtain ⟨expressions, converted, nextKnown, targetInstalled, _, targetRun, resultEq,
        _, _, extended, newReady, newStates, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
        doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
          (.err error) installed ready states values sourceCompiler targetCompiler targetOracle installRun installSafe
      have zero : source.clock = 0 := by
        by_contra nonzero
        simp [nonzero] at resultEq
      have errorEq : error = .abort .timeoutError := by simpa [zero] using resultEq
      have targetInstall : doInstall targetValues target = (.err (.abort .timeoutError), targetInstalled) := by
        simpa [zero] using targetRun
      have installedWf := doInstall_wellFormedFuel sourceValues source installed (.err error)
        sourceWf (ready.auxEmpty 0) installRun
      have newWf := stateWellFormedFuel_mono installedWf extended Set.Subset.rfl growth
      cases run
      subst error
      refine ⟨(nextKnown, converted.2 ++ g.2), .err (.abort .timeoutError), targetInstalled,
        extended, ?_, ?_, newStates, newWf, newReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
      · simp [targetInstall]
      · rfl
    | val program =>
      dsimp only at run
      cases programRun : evaluate program [] installed with
      | mk programResult programFinal =>
        rw [programRun] at run
        have programSafe : programResult ≠ .err (.abort .typeError) := by
          intro bad
          rw [bad] at run
          cases run
          exact notType rfl
        obtain ⟨nextKnown, converted, targetInstalled, finalG, targetProgramResult, targetFinal, _, targetInstall,
          _, extended, bodyExtended, targetProgramRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          doInstall_success_evaluate fuel relationFuel g allowed compiler source target sourceValues targetValues
            program installed programResult programFinal ready states sourceWf values sourceCompiler targetCompiler
            targetOracle installRun programRun programSafe (programIH program)
        have resultRelated := doInstall_success_resultRel_last sourceValues source installed programFinal program
          programResult targetProgramResult installRun programRun related
        cases programResult with
        | err sourceError =>
          cases targetProgramResult with
          | val targetResults => simp [resultRel] at related
          | err targetError =>
            have eq : result = .err sourceError ∧ final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨finalG, .err targetError, targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, ?_, related, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            simp [targetInstall, targetProgramRun]
        | val sourceResults =>
          cases targetProgramResult with
          | err targetError => simp [resultRel] at related
          | val targetResults =>
            have eq : result = .val [@holLast ClosSem.Value ⟨unitValue⟩ sourceResults] ∧
                final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨finalG,
              .val [@holLast ClosSem.Value ⟨unitValue⟩ targetResults], targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, ?_, ?_, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            · simp [targetInstall, targetProgramRun]
            · exact resultRelated

/-- The installed-program continuation admits an additional target clock
allowance. This Flapjack-specific simulation assumes the installed-program
induction hypothesis and does not cover evaluation of install arguments. -/
theorem runInstalled_incremental_sim_withClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : ClosProps.AdjustOracle.runInstalled sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (programIH : ∀ program nextKnown converted,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelowWithClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) allowed program converted.1) :
    ∃ extraClock nextG targetResult targetFinal,
      stateExtends g nextG ∧
      ClosProps.AdjustOracle.runInstalled targetValues { target with clock := target.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  unfold ClosProps.AdjustOracle.runInstalled at run ⊢
  cases installRun : doInstall sourceValues source with
  | mk installResult installed =>
    rw [installRun] at run
    cases installResult with
    | err error =>
      have installSafe : (SemanticPrimitivesHOL.Result.err error :
          SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value) ≠ .err (.abort .typeError) := by
        intro bad
        have equal : error = .abort .typeError := by cases bad; rfl
        cases run
        exact notType (by rw [equal])
      obtain ⟨expressions, converted, nextKnown, targetInstalled, _, targetRun, resultEq,
        _, _, extended, newReady, newStates, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
        doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
          (.err error) installed ready states values sourceCompiler targetCompiler targetOracle installRun installSafe
      have zero : source.clock = 0 := by
        by_contra nonzero
        simp [nonzero] at resultEq
      have errorEq : error = .abort .timeoutError := by simpa [zero] using resultEq
      have targetInstall : doInstall targetValues target = (.err (.abort .timeoutError), targetInstalled) := by
        simpa [zero] using targetRun
      have installedWf := doInstall_wellFormedFuel sourceValues source installed (.err error)
        sourceWf (ready.auxEmpty 0) installRun
      have newWf := stateWellFormedFuel_mono installedWf extended Set.Subset.rfl growth
      cases run
      subst error
      refine ⟨0, (nextKnown, converted.2 ++ g.2), .err (.abort .timeoutError), targetInstalled,
        extended, ?_, ?_, newStates, newWf, newReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
      · simp [targetInstall]
      · rfl
    | val program =>
      dsimp only at run
      cases programRun : evaluate program [] installed with
      | mk programResult programFinal =>
        rw [programRun] at run
        have programSafe : programResult ≠ .err (.abort .typeError) := by
          intro bad
          rw [bad] at run
          cases run
          exact notType rfl
        obtain ⟨nextKnown, converted, targetInstalled, extraClock, finalG, targetProgramResult, targetFinal, _, _, targetInstall,
          _, extended, bodyExtended, targetProgramRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          doInstall_success_evaluate_withClock fuel relationFuel g allowed compiler source target sourceValues targetValues
            program installed programResult programFinal ready states sourceWf values sourceCompiler targetCompiler
            targetOracle installRun programRun programSafe (programIH program)
        have resultRelated := doInstall_success_resultRel_last sourceValues source installed programFinal program
          programResult targetProgramResult installRun programRun related
        cases programResult with
        | err sourceError =>
          cases targetProgramResult with
          | val targetResults => simp [resultRel] at related
          | err targetError =>
            have eq : result = .err sourceError ∧ final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨extraClock, finalG, .err targetError, targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, ?_, related, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            simp [targetInstall, targetProgramRun]
        | val sourceResults =>
          cases targetProgramResult with
          | err targetError => simp [resultRel] at related
          | val targetResults =>
            have eq : result = .val [@holLast ClosSem.Value ⟨unitValue⟩ sourceResults] ∧
                final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨extraClock, finalG,
              .val [@holLast ClosSem.Value ⟨unitValue⟩ targetResults], targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, ?_, ?_, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            · simp [targetInstall, targetProgramRun]
            · exact resultRelated

/-- The installed-program continuation preserves the growing open-location
invariant. This is Flapjack-specific induction infrastructure; the installed
program simulation remains an explicit hypothesis. -/
theorem runInstalled_incremental_sim_withOpenClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (run : ClosProps.AdjustOracle.runInstalled sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (disjoint : Disjoint allowed (sptDomain g.1))
    (avoids : OracleLocationsAvoid allowed source)
    (programIH : ∀ program nextKnown converted nextAllowed,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) →
      (∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) →
      InstalledProgramSimBelowWithOpenClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ g.2) nextAllowed program converted.1) :
    ∃ extraClock nextG nextAllowed targetResult targetFinal,
      stateExtends g nextG ∧ allowed ⊆ nextAllowed ∧
      Disjoint nextAllowed (sptDomain nextG.1) ∧ OracleLocationsAvoid nextAllowed final ∧
      ClosProps.AdjustOracle.runInstalled targetValues { target with clock := target.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG nextAllowed targetFinal.code))
        (ValueRelFuel relationFuel nextG nextAllowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG nextAllowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG nextAllowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  unfold ClosProps.AdjustOracle.runInstalled at run ⊢
  cases installRun : doInstall sourceValues source with
  | mk installResult installed =>
    rw [installRun] at run
    cases installResult with
    | err error =>
      have installSafe : (SemanticPrimitivesHOL.Result.err error :
          SemanticPrimitivesHOL.Result (List ClosLang.Exp) ClosSem.Value) ≠ .err (.abort .typeError) := by
        intro bad
        have equal : error = .abort .typeError := by cases bad; rfl
        cases run
        exact notType (by rw [equal])
      obtain ⟨expressions, converted, nextKnown, targetInstalled, _, targetRun, resultEq,
        _, _, extended, newReady, newStates, newDisjoint, newAvoids, finalCompiler,
        targetFinalCompiler, finalOracle, growth⟩ :=
        doInstall_nonType_ready_disjoint fuel relationFuel g allowed compiler source target sourceValues targetValues
          (.err error) installed ready states values sourceCompiler targetCompiler targetOracle installRun installSafe
          disjoint avoids
      have zero : source.clock = 0 := by
        by_contra nonzero
        simp [nonzero] at resultEq
      have errorEq : error = .abort .timeoutError := by simpa [zero] using resultEq
      have targetInstall : doInstall targetValues target = (.err (.abort .timeoutError), targetInstalled) := by
        simpa [zero] using targetRun
      have installedWf := doInstall_wellFormedFuel sourceValues source installed (.err error)
        sourceWf (ready.auxEmpty 0) installRun
      have newWf := stateWellFormedFuel_mono installedWf extended Set.Subset.rfl growth
      cases run
      subst error
      refine ⟨0, (nextKnown, converted.2 ++ g.2), allowed, .err (.abort .timeoutError), targetInstalled,
        extended, Set.Subset.rfl, newDisjoint, newAvoids, ?_, ?_, newStates, newWf, newReady,
        finalCompiler, targetFinalCompiler, finalOracle, growth⟩
      · simp [targetInstall]
      · rfl
    | val program =>
      dsimp only at run
      cases programRun : evaluate program [] installed with
      | mk programResult programFinal =>
        rw [programRun] at run
        have programSafe : programResult ≠ .err (.abort .typeError) := by
          intro bad
          rw [bad] at run
          cases run
          exact notType rfl
        obtain ⟨nextKnown, converted, targetInstalled, nextAllowed, extraClock, finalG, finalAllowed,
          targetProgramResult, targetFinal, _, _, targetInstall, _, extended, bodyExtended,
          allowedGrowth, bodyAllowed, _, finalDisjoint, finalAvoids, targetProgramRun, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          doInstall_success_evaluate_withOpenClock fuel relationFuel g allowed compiler source target
            sourceValues targetValues program installed programResult programFinal ready states sourceWf values
            sourceCompiler targetCompiler targetOracle installRun programRun programSafe disjoint avoids (programIH program)
        have resultRelated := doInstall_success_resultRel_last sourceValues source installed programFinal program
          programResult targetProgramResult installRun programRun related
        cases programResult with
        | err sourceError =>
          cases targetProgramResult with
          | val targetResults => simp [resultRel] at related
          | err targetError =>
            have eq : result = .err sourceError ∧ final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨extraClock, finalG, finalAllowed, .err targetError, targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, Set.Subset.trans allowedGrowth bodyAllowed,
              finalDisjoint, finalAvoids, ?_, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            simp [targetInstall, targetProgramRun]
        | val sourceResults =>
          cases targetProgramResult with
          | err targetError => simp [resultRel] at related
          | val targetResults =>
            have eq : result = .val [@holLast ClosSem.Value ⟨unitValue⟩ sourceResults] ∧
                final = programFinal := by simpa using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨extraClock, finalG, finalAllowed,
              .val [@holLast ClosSem.Value ⟨unitValue⟩ targetResults], targetFinal,
              stateExtends_trans g _ finalG extended bodyExtended, Set.Subset.trans allowedGrowth bodyAllowed,
              finalDisjoint, finalAvoids, ?_, ?_, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩
            · simp [targetInstall, targetProgramRun]
            · exact resultRelated

/-- Composition of the install expression with its argument and dynamically
installed-program induction hypotheses. The argument hypothesis carries the
oracle invariant and compiler state to the point of installation; proving it
for all expression forms remains part of the enclosing simulation. -/
theorem evaluate_install_incremental_sim {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (argsIH : ∀ sourceResult sourceMiddle,
      evaluate sourceArgs sourceEnv source = (sourceResult, sourceMiddle) →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ middleG targetResult targetMiddle,
        evaluate targetArgs targetEnv target = (targetResult, targetMiddle) ∧
        stateExtends g middleG ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel middleG allowed targetMiddle.code))
          (ValueRelFuel relationFuel middleG allowed targetMiddle.code) sourceResult targetResult ∧
        StateRelFuel relationFuel middleG allowed sourceMiddle targetMiddle ∧
        StateWellFormedFuel relationFuel middleG allowed targetMiddle.code sourceMiddle ∧
        IncrementalInstallReady middleG sourceMiddle targetMiddle ∧
        sourceMiddle.compile = compileIncFuelCallback fuel compiler ∧ targetMiddle.compile = compiler ∧
        targetMiddle.compileOracle = compileIncFuelOracle fuel sourceMiddle.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetMiddle.code.lookup key = some entry))
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  rw [ClosProps.AdjustOracle.evaluateInstallEq trace sourceArgs sourceEnv source] at run
  rw [ClosProps.AdjustOracle.evaluateInstallEq trace targetArgs targetEnv target]
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult sourceMiddle =>
    rw [argsRun] at run
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact notType rfl
    obtain ⟨middleG, targetArgsResult, targetMiddle, targetArgsRun, firstExt, argsRelated,
      middleStates, middleWf, middleReady, sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩ :=
      argsIH argsResult sourceMiddle argsRun argsSafe
    rw [targetArgsRun]
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val targetValues => simp [resultRel] at argsRelated
      | err targetError =>
        cases run
        exact ⟨middleG, .err targetError, targetMiddle, firstExt, rfl, argsRelated, middleStates,
          middleWf, middleReady, sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩
    | val sourceValues =>
      cases targetArgsResult with
      | err targetError => simp [resultRel] at argsRelated
      | val targetValues =>
        have reversed : List.Forall₂ (ValueRelFuel relationFuel middleG allowed targetMiddle.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRelated
        have clockBound : sourceMiddle.clock ≤ source.clock := by
          have bound := evaluate_clock_le sourceArgs sourceEnv source
          simpa [argsRun] using bound
        have programIH' : ∀ program nextKnown converted,
            compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
            InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel sourceMiddle.clock compiler
              (nextKnown, converted.2 ++ middleG.2) allowed program converted.1 := by
          intro program nextKnown converted pass start targetStart bodyResult bodyFinal smaller
          exact programIH middleG program nextKnown converted pass start targetStart bodyResult bodyFinal
            (by omega)
        obtain ⟨nextG, targetResult, targetFinal, secondExt, targetRun, related, finalStates,
          finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runInstalled_incremental_sim fuel relationFuel middleG allowed compiler sourceMiddle targetMiddle
            sourceValues.reverse targetValues.reverse result final middleReady middleStates middleWf reversed
            sourceCompiler targetCompiler targetOracle run notType programIH'
        exact ⟨nextG, targetResult, targetFinal, stateExtends_trans g middleG nextG firstExt secondExt,
          targetRun, related, finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle,
          fun key entry found => growth key entry (argsGrowth key entry found)⟩

/-- Clock-allowing composition of an install expression with its argument and dynamically
installed-program induction hypotheses. The argument hypothesis carries the
oracle invariant and compiler state to the point of installation; proving it
for all expression forms remains part of the enclosing simulation. -/
theorem evaluate_install_incremental_sim_withClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (argsIH : ∀ sourceResult sourceMiddle,
      evaluate sourceArgs sourceEnv source = (sourceResult, sourceMiddle) →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ argsExtra middleG targetResult targetMiddle,
        evaluate targetArgs targetEnv { target with clock := target.clock + argsExtra } = (targetResult, targetMiddle) ∧
        stateExtends g middleG ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel middleG allowed targetMiddle.code))
          (ValueRelFuel relationFuel middleG allowed targetMiddle.code) sourceResult targetResult ∧
        StateRelFuel relationFuel middleG allowed sourceMiddle targetMiddle ∧
        StateWellFormedFuel relationFuel middleG allowed targetMiddle.code sourceMiddle ∧
        IncrementalInstallReady middleG sourceMiddle targetMiddle ∧
        sourceMiddle.compile = compileIncFuelCallback fuel compiler ∧ targetMiddle.compile = compiler ∧
        targetMiddle.compileOracle = compileIncFuelOracle fuel sourceMiddle.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetMiddle.code.lookup key = some entry))
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelowWithClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ extraClock nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv { target with clock := target.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  rw [ClosProps.AdjustOracle.evaluateInstallEq trace sourceArgs sourceEnv source] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult sourceMiddle =>
    rw [argsRun] at run
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact notType rfl
    obtain ⟨argsExtra, middleG, targetArgsResult, targetMiddle, targetArgsRun, firstExt, argsRelated,
      middleStates, middleWf, middleReady, sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩ :=
      argsIH argsResult sourceMiddle argsRun argsSafe
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val targetValues => simp [resultRel] at argsRelated
      | err targetError =>
        cases run
        refine ⟨argsExtra, middleG, .err targetError, targetMiddle, firstExt, ?_, argsRelated, middleStates,
          middleWf, middleReady, sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩
        rw [ClosProps.AdjustOracle.evaluateInstallEq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err targetError => simp [resultRel] at argsRelated
      | val targetValues =>
        have reversed : List.Forall₂ (ValueRelFuel relationFuel middleG allowed targetMiddle.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRelated
        have clockBound : sourceMiddle.clock ≤ source.clock := by
          have bound := evaluate_clock_le sourceArgs sourceEnv source
          simpa [argsRun] using bound
        have programIH' : ∀ program nextKnown converted,
            compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
            InstalledProgramSimBelowWithClock (C := C) (F := F) fuel relationFuel sourceMiddle.clock compiler
              (nextKnown, converted.2 ++ middleG.2) allowed program converted.1 := by
          intro program nextKnown converted pass start targetStart bodyResult bodyFinal smaller
          exact programIH middleG program nextKnown converted pass start targetStart bodyResult bodyFinal
            (by omega)
        obtain ⟨bodyExtra, nextG, targetResult, targetFinal, secondExt, targetRun, related, finalStates,
          finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runInstalled_incremental_sim_withClock fuel relationFuel middleG allowed compiler sourceMiddle targetMiddle
            sourceValues.reverse targetValues.reverse result final middleReady middleStates middleWf reversed
            sourceCompiler targetCompiler targetOracle run notType programIH'
        have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
          { target with clock := target.clock + argsExtra } targetMiddle (.val targetValues) bodyExtra
          targetArgsRun (by simp)
        refine ⟨argsExtra + bodyExtra, nextG, targetResult, targetFinal,
          stateExtends_trans g middleG nextG firstExt secondExt, ?_, related, finalStates, finalWf,
          finalReady, finalCompiler, targetFinalCompiler, finalOracle,
          fun key entry found => growth key entry (argsGrowth key entry found)⟩
        rw [ClosProps.AdjustOracle.evaluateInstallEq]
        have shiftedArgs' : evaluate targetArgs targetEnv
            { target with clock := target.clock + (argsExtra + bodyExtra) } =
            (.val targetValues, { targetMiddle with clock := targetMiddle.clock + bodyExtra }) := by
          simpa [Nat.add_assoc] using shiftedArgs
        rw [shiftedArgs']
        exact targetRun

/-- An install expression composes argument evaluation with installation while
allowing the set of open locations to grow in both phases. This is
Flapjack-specific induction infrastructure, not a HOL correctness theorem. -/
theorem evaluate_install_incremental_sim_withOpenClock {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (argsIH : ∀ sourceResult sourceMiddle,
      evaluate sourceArgs sourceEnv source = (sourceResult, sourceMiddle) →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ argsExtra middleG middleAllowed targetResult targetMiddle,
        evaluate targetArgs targetEnv { target with clock := target.clock + argsExtra } = (targetResult, targetMiddle) ∧
        stateExtends g middleG ∧ allowed ⊆ middleAllowed ∧
        Disjoint middleAllowed (sptDomain middleG.1) ∧ OracleLocationsAvoid middleAllowed sourceMiddle ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel middleG middleAllowed targetMiddle.code))
          (ValueRelFuel relationFuel middleG middleAllowed targetMiddle.code) sourceResult targetResult ∧
        StateRelFuel relationFuel middleG middleAllowed sourceMiddle targetMiddle ∧
        StateWellFormedFuel relationFuel middleG middleAllowed targetMiddle.code sourceMiddle ∧
        IncrementalInstallReady middleG sourceMiddle targetMiddle ∧
        sourceMiddle.compile = compileIncFuelCallback fuel compiler ∧ targetMiddle.compile = compiler ∧
        targetMiddle.compileOracle = compileIncFuelOracle fuel sourceMiddle.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetMiddle.code.lookup key = some entry))
    (programIH : ∀ (middleG : State) program nextKnown converted nextAllowed,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      (∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) →
      InstalledProgramSimBelowWithOpenClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) nextAllowed program converted.1) :
    ∃ extraClock nextG nextAllowed targetResult targetFinal,
      stateExtends g nextG ∧ allowed ⊆ nextAllowed ∧
      Disjoint nextAllowed (sptDomain nextG.1) ∧ OracleLocationsAvoid nextAllowed final ∧
      evaluate [.op trace .install targetArgs] targetEnv { target with clock := target.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG nextAllowed targetFinal.code))
        (ValueRelFuel relationFuel nextG nextAllowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG nextAllowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG nextAllowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  rw [ClosProps.AdjustOracle.evaluateInstallEq trace sourceArgs sourceEnv source] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult sourceMiddle =>
    rw [argsRun] at run
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at run
      cases run
      exact notType rfl
    obtain ⟨argsExtra, middleG, middleAllowed, targetArgsResult, targetMiddle, targetArgsRun, firstExt,
      firstAllowed, middleDisjoint, middleAvoids, argsRelated, middleStates, middleWf, middleReady,
      sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩ := argsIH argsResult sourceMiddle argsRun argsSafe
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val targetValues => simp [resultRel] at argsRelated
      | err targetError =>
        cases run
        refine ⟨argsExtra, middleG, middleAllowed, .err targetError, targetMiddle, firstExt,
          firstAllowed, middleDisjoint, middleAvoids, ?_, argsRelated, middleStates, middleWf,
          middleReady, sourceCompiler, targetCompiler, targetOracle, argsGrowth⟩
        rw [ClosProps.AdjustOracle.evaluateInstallEq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err targetError => simp [resultRel] at argsRelated
      | val targetValues =>
        have reversed : List.Forall₂ (ValueRelFuel relationFuel middleG middleAllowed targetMiddle.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRelated
        have clockBound : sourceMiddle.clock ≤ source.clock := by
          have bound := evaluate_clock_le sourceArgs sourceEnv source
          simpa [argsRun] using bound
        have programIH' : ∀ program nextKnown converted nextAllowed,
            compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
            (∀ loc ∈ codeLocations program, ¬ sptDomain nextKnown loc → loc ∈ nextAllowed) →
            InstalledProgramSimBelowWithOpenClock (C := C) (F := F) fuel relationFuel sourceMiddle.clock compiler
              (nextKnown, converted.2 ++ middleG.2) nextAllowed program converted.1 := by
          intro program nextKnown converted nextAllowed pass coverage start targetStart bodyResult bodyFinal smaller
          exact programIH middleG program nextKnown converted nextAllowed pass coverage start targetStart bodyResult
            bodyFinal (by omega)
        obtain ⟨bodyExtra, nextG, nextAllowed, targetResult, targetFinal, secondExt, secondAllowed,
          finalDisjoint, finalAvoids, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runInstalled_incremental_sim_withOpenClock fuel relationFuel middleG middleAllowed compiler
            sourceMiddle targetMiddle sourceValues.reverse targetValues.reverse result final middleReady middleStates
            middleWf reversed sourceCompiler targetCompiler targetOracle run notType middleDisjoint middleAvoids programIH'
        have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
          { target with clock := target.clock + argsExtra } targetMiddle (.val targetValues) bodyExtra
          targetArgsRun (by simp)
        refine ⟨argsExtra + bodyExtra, nextG, nextAllowed, targetResult, targetFinal,
          stateExtends_trans g middleG nextG firstExt secondExt, Set.Subset.trans firstAllowed secondAllowed,
          finalDisjoint, finalAvoids, ?_, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle,
          fun key entry found => growth key entry (argsGrowth key entry found)⟩
        rw [ClosProps.AdjustOracle.evaluateInstallEq]
        have shiftedArgs' : evaluate targetArgs targetEnv
            { target with clock := target.clock + (argsExtra + bodyExtra) } =
            (.val targetValues, { targetMiddle with clock := targetMiddle.clock + bodyExtra }) := by
          simpa [Nat.add_assoc] using shiftedArgs
        rw [shiftedArgs']
        exact targetRun

/-- A source-driven simulation that carries the incremental compiler and
oracle invariants through a list of expressions. This Lean-side predicate is
for composing the cases of the bounded direct-call simulation. -/
def GrowingExprsSim {C F : Type} (passFuel relationFuel : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    evaluate sourceExps sourceEnv source = (result, final) →
    result ≠ .err (.abort .typeError) →
    EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
    ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
    StateWellFormedFuel relationFuel g allowed target.code source →
    StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧
      evaluate targetExps targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Single-expression simulations compose in evaluation order while threading
the growing compiler state and installation invariants. -/
theorem growingExprsSim_of_forall₂ {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (sims : List.Forall₂ (fun source target =>
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [source] [target])
      sourceExps targetExps) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro g sourceEnv targetEnv source target result final run _ _ _ stateWf states ready sourceCompiler targetCompiler oracle
    have eq : result = .val [] ∧ final = source := by simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .val [], target, stateExtends_refl g ready.well.2, by simp [evaluate], .nil,
      states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headSim tailSims tailIH =>
    intro g sourceEnv targetEnv source target result final run notType envs envWf stateWf states ready
      sourceCompiler targetCompiler oracle
    have headEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headSafe : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have eq : result = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType eq
      obtain ⟨headG, targetHeadResult, targetHeadFinal, headExt, targetHeadRun, headRel, headStates,
        headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩ :=
        headSim g sourceEnv targetEnv source target headResult headFinal headRun headSafe headEnv envWf
          stateWf states ready sourceCompiler targetCompiler oracle
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have eq : result = .err error ∧ final = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨headG, .err targetError, targetHeadFinal, headExt,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv target targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv target targetHeadFinal targetValues targetHeadRun
          have valueRel : ValueRelFuel relationFuel headG allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv headExt Set.Subset.rfl headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf headExt Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailSafe : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            obtain ⟨finalG, targetTailResult, targetFinal, tailExt, targetTailRun, tailRel, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, tailGrowth⟩ :=
              tailIH headG sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal tailRun tailSafe
                tailEnv' tailEnvWf headWf headStates headReady headCompiler targetHeadCompiler headOracle
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv target targetHeadFinal targetValue targetHeadRun
            rw [targetTailRun] at targetOuter
            have combinedExt := stateExtends_trans g headG finalG headExt tailExt
            have combinedGrowth : ∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry :=
              fun key entry found => tailGrowth key entry (headGrowth key entry found)
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨finalG, .err targetError, targetFinal, combinedExt, targetOuter, tailRel, finalStates,
                  finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valueRel tailExt Set.Subset.rfl tailGrowth
                exact ⟨finalG, .val (targetValue :: targetTailValues), targetFinal, combinedExt,
                  targetOuter, .cons grownValue tailRel, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, combinedGrowth⟩

/-- A growing list simulation supplies the empty-environment, smaller-clock
simulation needed for an installed program. -/
theorem growingExprsSim_installedBelow {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp)
    (sim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed program targetProgram) :
    InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel limit compiler g allowed program targetProgram := by
  intro source target result final _ run notType sourceWf states ready sourceCompiler targetCompiler oracle
  have envs : EnvRelFuel relationFuel g allowed target.code [] [] 0 (targetProgram.map (0, ·)) := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel]
  exact sim g [] [] source target result final run notType envs .nil sourceWf states ready
    sourceCompiler targetCompiler oracle

/-- A growing list simulation discharges the argument hypothesis of the
incremental install case at the current source and target states. -/
theorem evaluate_install_growing_args {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)))
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (argsSim : GrowingExprsSim (F := F) fuel relationFuel compiler allowed sourceArgs targetArgs)
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  apply evaluate_install_incremental_sim fuel relationFuel g allowed compiler trace sourceArgs targetArgs
    sourceEnv targetEnv source target result final run notType ?_ programIH
  intro sourceResult sourceMiddle argsRun argsSafe
  obtain ⟨middleG, targetResult, targetMiddle, extended, targetRun, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩ :=
    argsSim g sourceEnv targetEnv source target sourceResult sourceMiddle argsRun argsSafe envs envWf sourceWf
      states ready sourceCompiler targetCompiler targetOracle
  exact ⟨middleG, targetResult, targetMiddle, targetRun, extended, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩

/-- Variable evaluation preserves the incremental compiler state and oracle
invariants while relating the selected environment entries. -/
theorem growingExprsSim_var {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (index : Nat) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.var trace index] [.var trace index] := by
  intro g sourceEnv targetEnv source target result final run notType envs _ stateWf states ready
    sourceCompiler targetCompiler oracle
  cases lookup : sourceEnv[index]? with
  | none =>
    have failed : result = .err (.abort .typeError) := by
      simpa [evaluate, lookup] using congrArg Prod.fst run.symm
    exact (notType failed).elim
  | some value =>
    have eq : result = .val [value] ∧ final = source := by simpa [evaluate, lookup] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    have related := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .var trace index)]).mp (by simpa using envs)
    have used : ∃ fn ∈ [(0, .var trace index)], ClosProps.freeVar (fn.1 + 0 + index) fn.2 := by
      refine ⟨(0, .var trace index), by simp, ?_⟩
      simp [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp]
    obtain ⟨next, nextLookup, valueRel⟩ := envRel_lookup related used lookup
    exact ⟨g, .val [next], target, stateExtends_refl g ready.well.2, by simp [evaluate, nextLookup],
      .cons valueRel .nil, states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩

/-- Clock updates preserve the installation invariant because it observes
only the compiler states, oracle and code. -/
theorem incrementalInstallReady_decClock {C F : Type} (g : State)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (amount : Nat)
    (ready : IncrementalInstallReady g source target) :
    IncrementalInstallReady g (decClock amount source) (decClock amount target) := by
  obtain ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩ := ready
  exact ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩

/-- Matching ticks preserve the growing-state simulation of their bodies. -/
theorem growingExprsSim_tick {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceBody] [targetBody]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.tick trace sourceBody] [.tick trace targetBody] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have eq : result = .err (.abort .timeoutError) ∧ final = source := by simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .err (.abort .timeoutError), target, stateExtends_refl g ready.well.2,
      by simp [evaluate, targetZero], rfl, states, sourceWf, ready, sourceCompiler, targetCompiler, oracle,
      fun _ _ h => h⟩
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp (by simpa using envs)
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g sourceEnv targetEnv (decClock 1 source) (decClock 1 target) result final bodyRun notType
        (by simpa [decClock] using bodyEnv) envWf (stateWellFormedFuel_clock sourceWf _)
        (stateRelFuel_decClock states 1) (incrementalInstallReady_decClock g source target 1 ready)
        (by simpa [decClock] using sourceCompiler) (by simpa [decClock] using targetCompiler)
        (by simpa [decClock] using oracle)
    refine ⟨finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    simpa [evaluate, targetNonzero] using targetRun

/-- Matching raises preserve the growing-state simulation of their bodies. -/
theorem growingExprsSim_raise {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceBody] [targetBody]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.raise trace sourceBody] [.raise trace targetBody] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp (by simpa using envs)
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodySafe (by simpa using bodyEnv)
        envWf sourceWf states ready sourceCompiler targetCompiler oracle
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err targetError =>
        have eq : result = .err error ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        exact ⟨finalG, .err targetError, targetFinal, extended, by simp [evaluate, targetRun], related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv target targetFinal targetValues targetRun
        have eq : result = .err (.raise value) ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        have valueRel : ValueRelFuel relationFuel finalG allowed targetFinal.code value targetValue := by
          simpa [resultRel] using related
        exact ⟨finalG, .err (.raise targetValue), targetFinal, extended, by simp [evaluate, targetRun], valueRel,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- The production traversal's variable case has the growing simulation. -/
theorem callsFuel_var_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (index : Nat)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.var trace index) initial = some (out, final)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.var trace index] [out] := by
  simp [callsFuel] at run
  obtain ⟨rfl, rfl⟩ := run
  exact growingExprsSim_var passFuel relationFuel compiler allowed trace index

/-- The production traversal's tick case uses its actual body output. -/
theorem callsFuel_tick_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [body] [target]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.tick trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSim_tick passFuel relationFuel compiler allowed trace body target (bodyIH target bodyRun)

/-- The production traversal's raise case uses its actual body output. -/
theorem callsFuel_raise_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [body] [target]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.raise trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSim_raise passFuel relationFuel compiler allowed trace body target (bodyIH target bodyRun)

/-- The production list traversal composes the smaller-depth expression
simulations while retaining the growing compiler and oracle invariants. -/
theorem callsListFuel_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel traversalFuel source initial = some (target, final))
    (exprIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [expression] [output]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed source target := by
  apply growingExprsSim_of_forall₂ passFuel relationFuel compiler allowed
  induction traversalFuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      refine List.Forall₂.cons ?_ ?_
      · exact exprIH depth (by omega) e e' initial middle headRun
      · apply ih es es' middle _ tailRun
        intro n bound expression output before after exprRun
        exact exprIH n (by omega) expression output before after exprRun

/-- Successful ordinary primitive dispatch preserves the compiler/oracle
installation conditions on a pair of states. -/
theorem incrementalInstallReady_doApp {C F : Type} (g : State)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceNext : ClosSem.State (NumSet × C) F) (targetNext : ClosSem.State C F)
    (sourceArgs targetArgs : List ClosSem.Value) (sourceValue targetValue : ClosSem.Value)
    (op : ClosLang.Op) (ready : IncrementalInstallReady g source target)
    (sourceRun : doApp op sourceArgs source = .val (sourceValue, sourceNext))
    (targetRun : doApp op targetArgs target = .val (targetValue, targetNext)) :
    IncrementalInstallReady g sourceNext targetNext := by
  have sourceFields := ClosInterp.doApp_compilerFields op sourceArgs source sourceNext sourceValue sourceRun
  have targetFields := ClosInterp.doApp_compilerFields op targetArgs target targetNext targetValue targetRun
  obtain ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩ := ready
  refine ⟨well, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ClosInterp.CompilerFieldsPreserved, targetFields.2.2.1] using included
  · simpa [ClosInterp.CompilerFieldsPreserved, sourceFields.2.1] using known
  · simpa [ClosInterp.CompilerFieldsPreserved, sourceFields.2.1] using auxEmpty
  · simpa [ClosInterp.CompilerFieldsPreserved, sourceFields.2.1] using distinct
  · simpa [ClosInterp.CompilerFieldsPreserved, sourceFields.2.1] using disjoint
  · simpa [ClosInterp.CompilerFieldsPreserved, sourceFields.2.1, targetFields.2.2.1] using fresh

/-- Ordinary primitive operations compose the growing simulation of their
arguments with primitive simulation and source well-formedness preservation.
Install and force-thunk are separate evaluator cases. -/
theorem growingExprsSim_ordinaryOp {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (sourceArgs targetArgs : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsSim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.op trace op sourceArgs] [.op trace op targetArgs] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace op targetArgs (by simpa using envs)
  have sourceArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  rw [evaluate_ordinaryOp_eq trace op sourceArgs sourceEnv source notInstall notForce] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    rw [argsRun] at sourceArgsWf
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsSim g sourceEnv targetEnv source target argsResult argsFinal argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRel
        have valuesWf : ValuesWellFormedFuel relationFuel argsG allowed targetArgsFinal.code sourceValues := by
          apply valuesWellFormedFuel_mono _ argsExt Set.Subset.rfl argsGrowth
          exact sourceArgsWf.1
        have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp
          (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
          (fun (s : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F) =>
            t.code = targetArgsFinal.code ∧ StateRelFuel relationFuel argsG allowed s t)
          argsFinal targetArgsFinal sourceValues.reverse targetValues.reverse op
          ⟨valueRelFuel_simple relationFuel argsG allowed targetArgsFinal.code,
            stateRelFuel_simple relationFuel argsG allowed targetArgsFinal.code⟩ ⟨⟨rfl, argsStates⟩, valuesRel⟩
        have primWf := doApp_result_wellFormedFuel op sourceValues.reverse argsFinal argsStateWf
          (valuesWellFormedFuel_reverse valuesWf)
        cases primRun : doApp op sourceValues.reverse argsFinal with
        | err error =>
          simp only [primRun] at sim
          obtain ⟨targetError, targetPrim, errors⟩ := sim
          have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, errors, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
        | val pair =>
          obtain ⟨value, sourceFinal⟩ := pair
          simp only [primRun] at sim primWf
          obtain ⟨targetValue, targetFinal, valueRel, ⟨codeEq, finalStates⟩, targetPrim⟩ := sim
          have eq : result = .val [value] ∧ final = sourceFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          have finalReady := incrementalInstallReady_doApp argsG argsFinal targetArgsFinal final targetFinal
            sourceValues.reverse targetValues.reverse value targetValue op argsReady primRun targetPrim
          have srcFields := ClosInterp.doApp_compilerFields op sourceValues.reverse argsFinal final value primRun
          have tgtFields := ClosInterp.doApp_compilerFields op targetValues.reverse targetArgsFinal targetFinal targetValue targetPrim
          refine ⟨argsG, .val [targetValue], targetFinal, argsExt, ?_, ?_, ?_, ?_, finalReady, ?_, ?_, ?_, ?_⟩
          · simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
          · change List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetFinal.code) [value] [targetValue]
            rw [codeEq]
            exact .cons valueRel .nil
          · simpa [codeEq] using finalStates
          · simpa [codeEq, PrimitiveResultWellFormedFuel] using primWf.2
          · exact srcFields.1.trans argsCompiler
          · exact tgtFields.1.trans targetArgsCompiler
          · rw [tgtFields.2.1, srcFields.2.1]
            exact argsOracle
          · intro key entry found
            rw [codeEq]
            exact argsGrowth key entry found

/-- The direct-call traversal's ordinary-operation case uses its actual
transformed argument list and the source well-formedness hypothesis. -/
theorem callsFuel_ordinaryOp_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace op args) initial = some (out, final))
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed args target)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate args env state)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.op trace op args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSim_ordinaryOp passFuel relationFuel compiler allowed trace op args targetArgs
    notInstall notForce (argsIH targetArgs argsRun) argsWf

/-- Restoring the surrounding clock does not alter installation invariants. -/
theorem incrementalInstallReady_fixClock {C F : Type} (g : State)
    (source sourceNext : ClosSem.State (NumSet × C) F) (target targetNext : ClosSem.State C F)
    (ready : IncrementalInstallReady g sourceNext targetNext) :
    IncrementalInstallReady g (fixClock source ((), sourceNext)).2 (fixClock target ((), targetNext)).2 := by
  obtain ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩ := ready
  exact ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩

/-- Condition evaluation and either branch simulate with the compiler state
and oracle invariants produced by the condition. -/
theorem growingExprsSim_if {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sc sy sn tc ty tn : ClosLang.Exp)
    (conditionIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sc] [tc])
    (yesIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sy] [ty])
    (noIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sn] [tn]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.ifThenElse trace sc sy sn] [.ifThenElse trace tc ty tn] := by
  intro g sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have ifEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .ifThenElse trace tc ty tn)] := by simpa using envs
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) ifEnv
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condSafe : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨condG, targetCondResult, targetCondFinal, condExt, targetCondRun, condRel, condStates,
      condWf, condReady, condCompiler, targetCondCompiler, condOracle, condGrowth⟩ :=
      conditionIH g sourceEnv targetEnv source target condResult condFinal condRun condSafe
        (by simpa using conditionEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), condFinal)).2
    let targetNext := (fixClock target ((), targetCondFinal)).2
    have nextStates : StateRelFuel relationFuel condG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 condStates
    have nextWf : StateWellFormedFuel relationFuel condG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock condWf (min source.clock condFinal.clock)
    have nextReady : IncrementalInstallReady condG sourceNext targetNext :=
      incrementalInstallReady_fixClock condG source condFinal target targetCondFinal condReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using condCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by
      simpa [targetNext, fixClock] using targetCondCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using condOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := condGrowth
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have eq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, condRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨condG, .err targetError, targetNext, condExt, ?_, condRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetCondRun, fixClock, targetNext]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv target targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel relationFuel condG allowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have eq : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact (notType eq).elim
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          have branchEnvWf := valuesWellFormedFuel_mono envWf condExt Set.Subset.rfl nextGrowth
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              noIH condG sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              yesIH condG sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- The direct-call traversal's conditional case composes its three actual
child outputs under the growing compiler-state simulation. -/
theorem callsFuel_if_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (conditionIH : ∀ target middle, callsFuel traversalFuel condition initial = some (target, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [condition] [target])
    (yesIH : ∀ target before after, callsFuel traversalFuel yes before = some (target, after) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [yes] [target])
    (noIH : ∀ target middle, callsFuel traversalFuel no middle = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [no] [target]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.ifThenElse trace condition yes no] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact growingExprsSim_if passFuel relationFuel compiler allowed trace condition yes no targetCondition targetYes targetNo
    (conditionIH targetCondition middle1 conditionRun) (yesIH targetYes middle1 middle2 yesRun)
    (noIH targetNo middle2 noRun)

/-- Let bindings and the body compose while carrying any compiler-state
growth from the bindings into the body's environment and invariants. -/
theorem growingExprsSim_let {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBindings targetBindings : List ClosLang.Exp) (sourceBody targetBody : ClosLang.Exp)
    (bindingsIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceBindings targetBindings)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceBody] [targetBody]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.let trace sourceBindings sourceBody] [.let trace targetBindings targetBody] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have letEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .let trace targetBindings targetBody)] := by simpa using envs
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody letEnv
  have bindingWf := bindingsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingSafe : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bindingG, targetBindingResult, targetBindingFinal, bindingExt, targetBindingRun, bindingRel,
      bindingStates, bindingStateWf, bindingReady, bindingCompiler, targetBindingCompiler, bindingOracle, bindingGrowth⟩ :=
      bindingsIH g sourceEnv targetEnv source target bindingResult bindingFinal bindingRun bindingSafe
        bindingsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextStates : StateRelFuel relationFuel bindingG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextWf : StateWellFormedFuel relationFuel bindingG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bindingStateWf (min source.clock bindingFinal.clock)
    have nextReady : IncrementalInstallReady bindingG sourceNext targetNext :=
      incrementalInstallReady_fixClock bindingG source bindingFinal target targetBindingFinal bindingReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bindingCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBindingCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bindingOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have eq : result = .err error ∧ final = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bindingG, .err targetError, targetNext, bindingExt, ?_, bindingRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBindingRun, fixClock, targetNext]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel bindingG allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv target
            targetBindingFinal targetValues targetBindingRun
          exact valuesRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody letEnv
        have outerEnv' := envRelFuel_mono outerEnv bindingExt Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valuesRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf) bindingExt Set.Subset.rfl nextGrowth
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (result, final) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          bodyIH bindingG (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) sourceNext targetNext result final
            bodyRun notType (by simpa using bodyEnv) bodyEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
        refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g bindingG finalG bindingExt extended, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · simpa [evaluate, targetBindingRun, fixClock, targetNext] using targetRun
        · intro key entry found
          exact growth key entry (nextGrowth key entry found)

/-- The direct-call traversal's let case composes its actual binding and body
outputs, conditional on source binding well-formedness. -/
theorem callsFuel_let_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.let trace bindings body) initial = some (out, final))
    (bindingsIH : ∀ target middle, callsListFuel traversalFuel bindings initial = some (target, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed bindings target)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body middle = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [body] [target]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.let trace bindings body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSim_let passFuel relationFuel compiler allowed trace bindings targetBindings body targetBody
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

/-- A handler receives the compiler state, oracle and related exception value
produced by its protected expression. -/
theorem growingExprsSim_handle {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sb sh tb th : ClosLang.Exp)
    (bodyIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sb] [tb])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sb] env state))
    (handlerIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sh] [th]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.handle trace sb sh] [.handle trace tb th] := by
  intro g sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have handleEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .handle trace tb th)] := by simpa using envs
  have bodyEnv := envRelFuel_handle_body trace tb th handleEnv
  have sourceBodyWf := bodyWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at sourceBodyWf
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
      bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
      bodyIH g sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextStates : StateRelFuel relationFuel bodyG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextWf : StateWellFormedFuel relationFuel bodyG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bodyStateWf (min source.clock bodyFinal.clock)
    have nextReady : IncrementalInstallReady bodyG sourceNext targetNext :=
      incrementalInstallReady_fixClock bodyG source bodyFinal target targetBodyFinal bodyReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bodyCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBodyCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bodyOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have eq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bodyG, .val targetValues, targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBodyRun, fixClock, targetNext]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have eq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨bodyG, .err (.abort targetAbort), targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
              nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
            simp [evaluate, targetBodyRun, fixClock, targetNext]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel relationFuel bodyG allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv := envRelFuel_mono handleEnv bodyExt Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have payloadWf : ValueWellFormedFuel relationFuel bodyG allowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 bodyExt Set.Subset.rfl nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf bodyExt Set.Subset.rfl nextGrowth
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              handlerIH bodyG (sourceValue :: sourceEnv) (targetValue :: targetEnv) sourceNext targetNext
                sourceResult sourceFinal handlerRun notType (by simpa using handlerEnv) (.cons payloadWf outerWf)
                nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g bodyG finalG bodyExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetBodyRun, fixClock, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- The direct-call traversal's handler case uses its transformed body and
handler, conditional on source body well-formedness. -/
theorem callsFuel_handle_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.handle trace body handler) initial = some (out, final))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body initial = some (target, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [body] [target])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel traversalFuel handler middle = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [handler] [target]) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.handle trace body handler] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact growingExprsSim_handle passFuel relationFuel compiler allowed trace body handler targetBody targetHandler
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- The direct-call traversal's install case uses its actual transformed
arguments and the smaller-clock installed-program induction hypothesis. -/
theorem callsFuel_install_growing_at {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.op trace .install args) initial = some (out, passFinal))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, passFinal) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed args target)
    (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install args] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? passFuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at passRun
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := passRun
  have argsEnv := envRelFuel_op_args trace .install targetArgs envs
  exact evaluate_install_growing_args passFuel relationFuel g allowed compiler trace args targetArgs
    sourceEnv targetEnv source target result final run notType argsEnv envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle (argsIH targetArgs argsRun) programIH

/-- The actually traversed function creates related closures and leaves the
growing compiler/oracle invariant intact. Static location and coverage
conditions are supplied by the enclosing traversal proof. -/
theorem callsFuel_fn_growing_at {C F : Type} (passFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (name : Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body out : ClosLang.Exp) (initial passFinal g : State)
    (passRun : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, passFinal))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (passGrowth : stateExtends passFinal g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.fn name (some loc) none arity body] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel (traversalFuel + 1) g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (sourceWf : StateWellFormedFuel (traversalFuel + 1) g allowed target.code source)
    (states : StateRelFuel (traversalFuel + 1) g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel (traversalFuel + 1) g allowed targetFinal.code))
        (ValueRelFuel (traversalFuel + 1) g allowed targetFinal.code) result targetResult ∧
      StateRelFuel (traversalFuel + 1) g allowed final targetFinal ∧
      StateWellFormedFuel (traversalFuel + 1) g allowed targetFinal.code final ∧
      IncrementalInstallReady g final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have included := codeIncludes_of_stateExtends passFinal g target.code passGrowth ready.included
  obtain ⟨targetBody, rfl, closure⟩ := callsFuel_fn_relation traversalFuel name loc arity body out
    initial passFinal g allowed target.code passRun initialWf locations annotations distinct fresh passGrowth coverage included
  have valid : arity ≤ source.maxApp ∧ arity ≠ 0 := by
    by_contra invalid
    have bad : result = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst run.symm
    exact notType bad
  have targetValid : arity ≤ target.maxApp ∧ arity ≠ 0 := by simpa [← states.2.2.1] using valid
  have eq : result = .val [.closure (some loc) [] sourceEnv arity body] ∧ final = source := by
    simpa [evaluate, valid] using run.symm
  obtain ⟨rfl, rfl⟩ := eq
  have captured := envRelFuel_fn_body name (some loc) arity targetBody envs
  have valueRel : ValueRelFuel (traversalFuel + 1) g allowed target.code
      (.closure (some loc) [] sourceEnv arity body) (.closure (some loc) [] targetEnv arity targetBody) :=
    .closure closure .nil captured
  exact ⟨.val [.closure (some loc) [] targetEnv arity targetBody], target, by simp [evaluate, targetValid],
    .cons valueRel .nil, states, sourceWf, ready, sourceCompiler, targetCompiler, targetOracle, fun _ _ h => h⟩

/-- Function creation is simulated at arbitrary relation fuel. This is
Flapjack-specific bounded-adapter infrastructure. -/
theorem callsFuel_fn_growing_atFuel {C F : Type} (passFuel traversalFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (name : Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body out : ClosLang.Exp) (initial passFinal g : State)
    (passRun : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, passFinal))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (passGrowth : stateExtends passFinal g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.fn name (some loc) none arity body] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel g allowed targetFinal.code))
        (ValueRelFuel relationFuel g allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel g allowed final targetFinal ∧
      StateWellFormedFuel relationFuel g allowed targetFinal.code final ∧
      IncrementalInstallReady g final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have included := codeIncludes_of_stateExtends passFinal g target.code passGrowth ready.included
  obtain ⟨targetBody, rfl, closure⟩ := callsFuel_fn_relation_atFuel traversalFuel relationFuel name loc arity body out
    initial passFinal g allowed target.code passRun initialWf locations annotations distinct fresh passGrowth coverage included
  have valid : arity ≤ source.maxApp ∧ arity ≠ 0 := by
    by_contra invalid
    have bad : result = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst run.symm
    exact notType bad
  have targetValid : arity ≤ target.maxApp ∧ arity ≠ 0 := by simpa [← states.2.2.1] using valid
  have eq : result = .val [.closure (some loc) [] sourceEnv arity body] ∧ final = source := by
    simpa [evaluate, valid] using run.symm
  obtain ⟨rfl, rfl⟩ := eq
  have captured := envRelFuel_fn_body name (some loc) arity targetBody envs
  have valueRel : ValueRelFuel relationFuel g allowed target.code
      (.closure (some loc) [] sourceEnv arity body) (.closure (some loc) [] targetEnv arity targetBody) :=
    .closure closure .nil captured
  exact ⟨.val [.closure (some loc) [] targetEnv arity targetBody], target, by simp [evaluate, targetValid],
    .cons valueRel .nil, states, sourceWf, ready, sourceCompiler, targetCompiler, targetOracle, fun _ _ h => h⟩

/-- Growing simulation restricted to compiler states extending a particular
pass state. Closure-creation cases need this premise to find the code emitted
by their traversal. This is Lean-side infrastructure for the enclosing proof. -/
def GrowingExprsSimFrom {C F : Type} (passFuel relationFuel : Nat) (compiler : ClosSem.Compiler C)
    (required : State) (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State), stateExtends required g →
    ∀ (sourceEnv targetEnv : List ClosSem.Value)
      (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
      (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
      (final : ClosSem.State (NumSet × C) F),
      evaluate sourceExps sourceEnv source = (result, final) →
      result ≠ .err (.abort .typeError) →
      EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
      ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
      StateWellFormedFuel relationFuel g allowed target.code source →
      StateRelFuel relationFuel g allowed source target → IncrementalInstallReady g source target →
      source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
      target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
      ∃ finalG targetResult targetFinal,
        stateExtends g finalG ∧ evaluate targetExps targetEnv target = (targetResult, targetFinal) ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
          (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
        StateRelFuel relationFuel finalG allowed final targetFinal ∧
        StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
        IncrementalInstallReady finalG final targetFinal ∧
        final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
        targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Clock-bounded pass-state simulation for well-founded induction over
installed programs. This is Flapjack-specific simulation infrastructure.
It demands equal starting clocks and therefore cannot express the general
HOL `calls_correct` result: generated direct-call stubs can require an extra
target tick, as shown by `generated_stub_ne_variable_zero_clock`. -/
def GrowingExprsSimFromBelow {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (required : State) (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State), stateExtends required g →
    ∀ (sourceEnv targetEnv : List ClosSem.Value)
      (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
      (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
      (final : ClosSem.State (NumSet × C) F),
      source.clock < limit →
      evaluate sourceExps sourceEnv source = (result, final) →
      result ≠ .err (.abort .typeError) →
      EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
      ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
      StateWellFormedFuel relationFuel g allowed target.code source →
      StateRelFuel relationFuel g allowed source target → IncrementalInstallReady g source target →
      source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
      target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
      ∃ finalG targetResult targetFinal,
        stateExtends g finalG ∧ evaluate targetExps targetEnv target = (targetResult, targetFinal) ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
          (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
        StateRelFuel relationFuel finalG allowed final targetFinal ∧
        StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
        IncrementalInstallReady finalG final targetFinal ∧
        final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
        targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Clock-bounded expression simulation with an existential target-clock
allowance. This is Flapjack-specific infrastructure motivated by HOL
`calls_correct`, not a port of that theorem: its other invariants and
conclusions have not yet been matched to HOL. -/
def GrowingExprsSimFromBelowWithClock {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (required : State) (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State), stateExtends required g →
    ∀ (sourceEnv targetEnv : List ClosSem.Value)
      (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
      (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
      (final : ClosSem.State (NumSet × C) F),
      source.clock < limit →
      evaluate sourceExps sourceEnv source = (result, final) →
      result ≠ .err (.abort .typeError) →
      EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
      ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
      StateWellFormedFuel relationFuel g allowed target.code source →
      StateRelFuel relationFuel g allowed source target → IncrementalInstallReady g source target →
      source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
      target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
      ∃ extraClock finalG targetResult targetFinal,
        stateExtends g finalG ∧ evaluate targetExps targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
          (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
        StateRelFuel relationFuel finalG allowed final targetFinal ∧
        StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
        IncrementalInstallReady finalG final targetFinal ∧
        final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
        targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Bounded expression simulation with a growing set of open locations. This
Flapjack-specific predicate records the invariants needed to compose dynamic
installation; it is not a port of a HOL correctness theorem. -/
def GrowingExprsSimFromBelowWithOpenClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State), stateExtends required g → ∀ (allowed : Set Nat)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit → evaluate sourceExps sourceEnv source = (result, final) →
    result ≠ .err (.abort .typeError) →
    EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
    ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
    StateWellFormedFuel relationFuel g allowed target.code source →
    StateRelFuel relationFuel g allowed source target → IncrementalInstallReady g source target →
    Disjoint allowed (sptDomain g.1) → OracleLocationsAvoid allowed source →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ extraClock finalG finalAllowed targetResult targetFinal,
      stateExtends g finalG ∧ allowed ⊆ finalAllowed ∧
      Disjoint finalAllowed (sptDomain finalG.1) ∧ OracleLocationsAvoid finalAllowed final ∧
      evaluate targetExps targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG finalAllowed targetFinal.code))
        (ValueRelFuel relationFuel finalG finalAllowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG finalAllowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG finalAllowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Variables preserve the open-location invariant. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_var {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra) (index : Nat) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required
      [.var trace index] [.var trace index] := by
  intro g _ allowed sourceEnv targetEnv source target result final _ run notType envs _ sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  cases lookup : sourceEnv[index]? with
  | none =>
    have failed : result = .err (.abort .typeError) := by
      simpa [evaluate, lookup] using congrArg Prod.fst run.symm
    exact (notType failed).elim
  | some value =>
    have eq : result = .val [value] ∧ final = source := by simpa [evaluate, lookup] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    have related := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .var trace index)]).mp (by simpa using envs)
    have used : ∃ fn ∈ [(0, .var trace index)], ClosProps.freeVar (fn.1 + 0 + index) fn.2 := by
      refine ⟨(0, .var trace index), by simp, ?_⟩
      simp [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp]
    obtain ⟨next, nextLookup, valueRel⟩ := envRel_lookup related used lookup
    refine ⟨0, g, allowed, .val [next], target, stateExtends_refl g ready.well.2, Set.Subset.rfl,
      disjoint, avoids, ?_, .cons valueRel .nil, states, sourceWf, ready, sourceCompiler,
      targetCompiler, oracle, fun _ _ h => h⟩
    simp [evaluate, nextLookup]

/-- Clock-allowing expression simulation restricted to environments with a
required argument prefix. This is Flapjack-specific infrastructure motivated by HOL
`calls_correct`, not a port of that theorem: its other invariants and
conclusions have not yet been matched to HOL. -/
def GrowingExprsSimFromBelowWithClockArity {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (required : State) (allowed : Set Nat) (arity : Nat) (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (g : State), stateExtends required g →
    ∀ (sourceEnv targetEnv : List ClosSem.Value)
      (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
      (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
      (final : ClosSem.State (NumSet × C) F),
      source.clock < limit → arity ≤ sourceEnv.length →
      evaluate sourceExps sourceEnv source = (result, final) →
      result ≠ .err (.abort .typeError) →
      EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
      ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv →
      StateWellFormedFuel relationFuel g allowed target.code source →
      StateRelFuel relationFuel g allowed source target → IncrementalInstallReady g source target →
      source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
      target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
      ∃ extraClock finalG targetResult targetFinal,
        stateExtends g finalG ∧ evaluate targetExps targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
        resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
          (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
        StateRelFuel relationFuel finalG allowed final targetFinal ∧
        StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
        IncrementalInstallReady finalG final targetFinal ∧
        final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
        targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
        (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- A traversed recursive group enters its actual transformed body with
related closures and the growing compiler/oracle invariant. -/
theorem callsFuel_letrec_growing_at {C F : Type} (passFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (names : List Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body out : ClosLang.Exp) (initial passFinal g : State)
    (passRun : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, passFinal))
    (bodyIH : ∀ targetBody middle, callsFuel traversalFuel body middle = some (targetBody, passFinal) →
      GrowingExprsSimFrom (F := F) passFuel traversalFuel compiler passFinal allowed [body] [targetBody])
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (passGrowth : stateExtends passFinal g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.letrec names (some loc) none fns body] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel traversalFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel traversalFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel traversalFuel g allowed target.code source)
    (states : StateRelFuel traversalFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel traversalFuel finalG allowed targetFinal.code))
        (ValueRelFuel traversalFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel traversalFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel traversalFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetFns, targetBody, middle, rfl, bodyPass, closure⟩ :=
    callsFuel_letrec_relation traversalFuel names loc fns body out initial passFinal g allowed target.code passRun
      initialWf locations annotations distinct fresh passGrowth coverage ready.included
  have valid : fns.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
    by_contra invalid
    have bad : result = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst run.symm
    exact notType bad
  have targetValid : targetFns.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
    have arities := recClosureRelFuel_arities traversalFuel g allowed target.code loc fns targetFns closure
    have same := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simp only [List.all_map, Function.comp_def] at same
    rw [← states.2.2.1, same]
    exact valid
  have bodyEnv := envRelFuel_letrec_enter names loc fns targetFns targetBody closure envs
  have bodyRun : evaluate [body]
      ((List.range fns.length).map (fun i => .recclosure (some loc) [] sourceEnv fns i) ++ sourceEnv)
      source = (result, final) := by simpa [evaluate, valid] using run
  have bodyEnvWf : ValuesWellFormedFuel traversalFuel g allowed target.code
      ((List.range fns.length).map (fun i => .recclosure (some loc) [] sourceEnv fns i) ++ sourceEnv) :=
    valuesWellFormedFuel_append (recClosureBundle_wellFormedFuel loc sourceEnv fns targetFns envWf closure) envWf
  obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    bodyIH targetBody middle bodyPass g passGrowth _ _ source target result final bodyRun notType (by simpa using bodyEnv)
      bodyEnvWf sourceWf states ready sourceCompiler targetCompiler targetOracle
  refine ⟨finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩
  simpa [evaluate, targetValid] using targetRun

/-- Induction interface for closure application while carrying the growing
compiler state and oracle. This relates executions of the actual evaluator;
it is not yet a proof of the application case. -/
def GrowingAppSim {C F : Type} (passFuel relationFuel : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (loc : Option Nat) : Prop :=
  ∀ (g : State) (function targetFunction : ClosSem.Value) (args targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    evaluateApp loc function args source = (result, final) → result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code function targetFunction →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) args targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code function →
    ValuesWellFormedFuel relationFuel g allowed target.code args →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp loc targetFunction targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Clock-bounded application simulation for the well-founded evaluator
induction. This Flapjack-specific interface requires equal starting clocks;
the HOL correctness theorem instead permits extra target clock. -/
def GrowingAppSimClockBelow {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (loc : Option Nat) : Prop :=
  ∀ (g : State) (function targetFunction : ClosSem.Value) (args targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit →
    evaluateApp loc function args source = (result, final) → result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code function targetFunction →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) args targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code function →
    ValuesWellFormedFuel relationFuel g allowed target.code args →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp loc targetFunction targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Clock-bounded application simulation with an existential target-clock
allowance. This is Flapjack-specific infrastructure, not a HOL theorem port. -/
def GrowingAppSimClockBelowWithClock {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (loc : Option Nat) : Prop :=
  ∀ (g : State) (function targetFunction : ClosSem.Value) (args targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F),
    source.clock < limit →
    evaluateApp loc function args source = (result, final) → result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code function targetFunction →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) args targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code function →
    ValuesWellFormedFuel relationFuel g allowed target.code args →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp loc targetFunction targetArgs { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- A retained application composes argument, function and closure-application
simulations, carrying compiler-state growth through each stage. The final
application and source value well-formedness remain induction hypotheses. -/
theorem growingExprsSim_app {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Option Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceArgs targetArgs : List ClosLang.Exp)
    (length : sourceArgs.length = targetArgs.length)
    (argsIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (fnIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed loc) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.app trace loc sourceFn sourceArgs] [.app trace loc targetFn targetArgs] := by
  intro g sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have appEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .app trace loc targetFn targetArgs)] := by simpa using envs
  obtain ⟨fnEnv, argsEnv⟩ := envRelFuel_app_parts trace loc targetFn targetArgs appEnv
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp [empty] at length
    have targetNotEmpty : targetArgs.isEmpty = false := by
      cases targetArgs with
      | nil => exact (targetNonempty rfl).elim
      | cons head tail => rfl
    have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases argsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [argsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : sourceResult = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
        argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH g sourceEnv targetEnv source target argsResult argsFinal argsRun argsSafe argsEnv envWf
          sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : sourceResult = .err error ∧ sourceFinal = argsFinal := by simpa [argsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [evaluate]
          simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
          rw [targetArgsRun]
      | val values =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) values targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases fnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [fnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : sourceResult = .err (.abort .typeError) := by
                simpa [argsRun, fnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates,
              fnStateWf, fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH argsG sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal fnRun fnSafe
                (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val vs => simp [resultRel] at fnRel
              | err targetError =>
                have eq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                rw [evaluate]
                simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                rw [targetArgsRun, targetFnRun]
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues fnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) values targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp loc fnValue values fnFinal = (sourceResult, sourceFinal) := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code values :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨finalG, result, final, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                  appIH fnG fnValue targetFnValue values targetValues fnFinal targetFnFinal sourceResult sourceFinal
                    appRun notType functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady
                    fnCompiler targetFnCompiler fnOracle
                refine ⟨finalG, result, final, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
                  finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                  simpa using targetRun
                · intro key entry found
                  exact appGrowth key entry (prefixGrowth key entry found)

/-- A location-free application remains an application after the actual
direct-call traversal and composes its transformed children. -/
theorem callsFuel_app_none_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace none sourceFn sourceArgs) initial = some (out, final))
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed none) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.app trace none sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, next⟩, fnRun, rfl, rfl⟩ := run
  have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
  exact growingExprsSim_app passFuel relationFuel compiler allowed trace none sourceFn targetFn sourceArgs targetArgs
    length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- A location-annotated application remains an application when its location
is absent from the traversal's final known-location set. -/
theorem callsFuel_app_unknown_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace (some loc) sourceFn sourceArgs) initial = some (out, final))
    (unknown : sptLookup loc final.1 = none)
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed (some loc)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.app trace (some loc) sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup loc afterFn.1).isSome
  · simp [found] at rest
    split at rest <;> simp_all
  · simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
    exact growingExprsSim_app passFuel relationFuel compiler allowed trace (some loc) sourceFn targetFn sourceArgs targetArgs
      length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- Installation readiness is independent of either evaluator clock. -/
theorem incrementalInstallReady_setClock {C F : Type} (g : State)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceClock targetClock : Nat) (ready : IncrementalInstallReady g source target) :
    IncrementalInstallReady g { source with clock := sourceClock } { target with clock := targetClock } := by
  obtain ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩ := ready
  exact ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩

/-- Applying no arguments returns the related function and preserves the
compiler-state and oracle invariants. -/
theorem evaluateApp_nil_growing {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat) (g : State)
    (sourceFun targetFun : ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluateApp requested sourceFun [] source = (result, final))
    (functions : ValueRelFuel relationFuel g allowed target.code sourceFun targetFun)
    (stateWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun [] target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have eq : result = .val [sourceFun] ∧ final = source := by simpa [evaluateApp] using run.symm
  obtain ⟨rfl, rfl⟩ := eq
  exact ⟨g, .val [targetFun], target, stateExtends_refl g ready.well.2, by simp [evaluateApp],
    .cons functions .nil, states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩

/-- Partial application, including its timeout branch, preserves the growing
compiler and oracle invariants. -/
theorem evaluateApp_partial_growing {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat) (g : State)
    (sourceFun targetFun sourcePartial : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.partialApp sourcePartial))
    (run : evaluateApp requested sourceFun sourceArgs source = (result, final))
    (functions : ValueRelFuel relationFuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs)
    (stateWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have len := args.length_eq
    simp [empty] at len
    cases sourceArgs with
    | nil => exact nonempty rfl
    | cons head tail => simp at len
  have maxApp := states.2.2.1
  obtain ⟨targetPartial, targetClosure, partialRel⟩ :=
    destClosure_partial_fuel relationFuel g allowed target.code source.maxApp requested sourceFun targetFun sourcePartial
      sourceArgs targetArgs sourceClosure functions args
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs = some (.partialApp targetPartial) := by
    simpa [← maxApp] using targetClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at run
      by_cases timeout : source.clock < (sourceHead :: sourceTail).length
      · have targetTimeout : target.clock < (targetHead :: targetTail).length := by omega
        have sourceTimeout' : source.clock ≤ sourceTail.length := by simpa using timeout
        have targetTimeout' : target.clock ≤ targetTail.length := by simpa using targetTimeout
        have eq : result = .err (.abort .timeoutError) ∧ final = { source with clock := 0 } := by
          simpa [sourceTimeout'] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨g, .err (.abort .timeoutError), { target with clock := 0 }, stateExtends_refl g ready.well.2,
          ?_, rfl, stateRelFuel_zeroClock states, ?_, incrementalInstallReady_setClock g source target 0 0 ready,
          sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        · rw [evaluateApp, targetClosure']
          simp [targetTimeout']
        · exact stateWellFormedFuel_clock stateWf 0
      · have targetEnough : ¬ target.clock < (targetHead :: targetTail).length := by omega
        have sourceEnough' : ¬ source.clock ≤ sourceTail.length := by simpa using timeout
        have targetEnough' : ¬ target.clock ≤ targetTail.length := by simpa using targetEnough
        have eq : result = .val [sourcePartial] ∧ final = decClock (sourceHead :: sourceTail).length source := by
          simpa [sourceEnough'] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨g, .val [targetPartial], decClock (targetHead :: targetTail).length target,
          stateExtends_refl g ready.well.2, ?_, .cons partialRel .nil, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ h => h⟩
        · rw [evaluateApp, targetClosure']
          simp [targetEnough']
        · rw [← lengths]
          exact stateRelFuel_decClock states (sourceHead :: sourceTail).length
        · simpa [decClock] using stateWellFormedFuel_clock stateWf _
        · simpa [decClock] using incrementalInstallReady_setClock g source target
            (source.clock - (sourceHead :: sourceTail).length) (target.clock - (targetHead :: targetTail).length) ready
        · simpa [decClock] using sourceCompiler
        · simpa [decClock] using targetCompiler
        · simpa [decClock] using oracle

/-- The application induction hypothesis for strictly shorter argument
lists. This permits the compiler state to grow between applications. -/
def GrowingAppSimBelow {C F : Type} (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (requested : Option Nat) : Prop :=
  ∀ (g : State) (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value) (final : ClosSem.State (NumSet × C) F),
    sourceArgs.length < limit → evaluateApp requested sourceFun sourceArgs source = (result, final) →
    result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code sourceFun targetFun →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code sourceFun →
    ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Application simulation bounded by both argument count and evaluator
clock, for nested strong inductions. This is Flapjack-specific infrastructure. -/
def GrowingAppSimArgClockBelow {C F : Type} (passFuel relationFuel argLimit clockLimit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (requested : Option Nat) : Prop :=
  ∀ (g : State) (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value) (final : ClosSem.State (NumSet × C) F),
    sourceArgs.length < argLimit → source.clock < clockLimit → evaluateApp requested sourceFun sourceArgs source = (result, final) →
    result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code sourceFun targetFun →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code sourceFun →
    ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- Clock-allowing application simulation bounded by argument count and
evaluator clock, for nested strong inductions. This is Flapjack-specific infrastructure. -/
def GrowingAppSimArgClockBelowWithClock {C F : Type} (passFuel relationFuel argLimit clockLimit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (requested : Option Nat) : Prop :=
  ∀ (g : State) (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value) (final : ClosSem.State (NumSet × C) F),
    sourceArgs.length < argLimit → source.clock < clockLimit → evaluateApp requested sourceFun sourceArgs source = (result, final) →
    result ≠ .err (.abort .typeError) →
    ValueRelFuel relationFuel g allowed target.code sourceFun targetFun →
    List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs →
    ValueWellFormedFuel relationFuel g allowed target.code sourceFun →
    ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs →
    StateWellFormedFuel relationFuel g allowed target.code source → StateRelFuel relationFuel g allowed source target →
    IncrementalInstallReady g source target →
    source.compile = compileIncFuelCallback passFuel compiler → target.compile = compiler →
    target.compileOracle = compileIncFuelOracle passFuel source.compileOracle →
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry)

/-- A full application uses the selected closure body's simulation and, for
remaining arguments, a strictly shorter application induction hypothesis. -/
theorem evaluateApp_full_growing {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat) (g : State)
    (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (run : evaluateApp requested sourceFun sourceArgs source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (functions : ValueRelFuel relationFuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs)
    (functionWf : ValueWellFormedFuel relationFuel g allowed target.code sourceFun)
    (argsWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs)
    (stateWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (bodyIH : ∀ (targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed target.code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceBody] [targetBody])
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (appIH : GrowingAppSimBelow (F := F) passFuel relationFuel sourceArgs.length compiler allowed requested) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have len := args.length_eq
    simp [empty] at len
    cases sourceArgs with
    | nil => exact nonempty rfl
    | cons head tail => simp at len
  have maxApp := states.2.2.1
  obtain ⟨targetBody, targetBodyEnv, targetRest, loc, sourceFns, targetFns, index, arity,
      targetClosure, bodyEnv, restRel, closure, sourceLookup, targetLookup, _⟩ :=
    destClosure_full_fuel relationFuel g allowed target.code source.maxApp requested sourceFun targetFun
      sourceArgs targetArgs sourceBody sourceBodyEnv sourceRest sourceClosure functions args
  have ⟨sourceBodyEnvWf, sourceRestWf⟩ := destClosure_full_wellFormedFuel source.maxApp requested sourceFun
    sourceArgs sourceBodyEnv sourceRest sourceBody functionWf argsWf sourceClosure
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs =
      some (.fullApp targetBody targetBodyEnv targetRest) := by simpa [← maxApp] using targetClosure
  have restShort := destClosure_full_remaining_lt source.maxApp requested sourceFun sourceArgs sourceBodyEnv sourceRest
    sourceBody sourceClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  have restLengths := restRel.length_eq
  let cost := sourceArgs.length - sourceRest.length
  have targetCost : targetArgs.length - targetRest.length = cost := by simp [cost, ← lengths, ← restLengths]
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at run
      have sourceCostEq : sourceTail.length + 1 - sourceRest.length = cost := rfl
      have targetCostEq : targetTail.length + 1 - targetRest.length = cost := targetCost
      simp only [List.length_cons, sourceCostEq] at run
      by_cases timeout : source.clock < cost
      · have sourceEq : result = .err (.abort .timeoutError) ∧ final = { source with clock := 0 } := by
          simpa [timeout] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨g, .err (.abort .timeoutError), { target with clock := 0 }, stateExtends_refl g ready.well.2,
          ?_, rfl, stateRelFuel_zeroClock states, stateWellFormedFuel_clock stateWf 0,
          incrementalInstallReady_setClock g source target 0 0 ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        rw [evaluateApp, targetClosure']
        simp only [List.length_cons, targetCostEq]
        have targetTimeout : target.clock < cost := by omega
        simp [targetTimeout]
      · let sourceStart := decClock cost source
        let targetStart := decClock cost target
        have startStates : StateRelFuel relationFuel g allowed sourceStart targetStart := stateRelFuel_decClock states cost
        have startWf : StateWellFormedFuel relationFuel g allowed targetStart.code sourceStart := by
          simpa [sourceStart, targetStart, decClock] using stateWellFormedFuel_clock stateWf _
        have startReady : IncrementalInstallReady g sourceStart targetStart :=
          incrementalInstallReady_decClock g source target cost ready
        simp only [if_neg timeout, fixClock_evaluate] at run
        cases bodyRun : evaluate [sourceBody] sourceBodyEnv sourceStart with
        | mk bodyResult bodyFinal =>
          have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
            intro bad
            subst bodyResult
            have eq : result = .err (.abort .typeError) := by
              simpa [sourceStart, bodyRun] using congrArg Prod.fst run.symm
            exact notType eq
          have sourceBodyWf := bodyWf target.code sourceBody targetBody loc sourceFns targetFns index arity
            closure sourceLookup targetLookup sourceBodyEnv sourceStart sourceBodyEnvWf startWf startReady.auxEmpty
          rw [bodyRun] at sourceBodyWf
          obtain ⟨bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
            bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
            bodyIH targetBody loc sourceFns targetFns index arity closure sourceLookup targetLookup
              g sourceBodyEnv targetBodyEnv sourceStart targetStart bodyResult bodyFinal bodyRun bodySafe
              (by simpa [targetStart, decClock] using bodyEnv) sourceBodyEnvWf startWf startStates startReady
              (by simpa [sourceStart, decClock] using sourceCompiler)
              (by simpa [targetStart, decClock] using targetCompiler)
              (by simpa [sourceStart, targetStart, decClock] using oracle)
          have targetBodyRun' : evaluate [targetBody] targetBodyEnv (decClock cost target) =
              (targetBodyResult, targetBodyFinal) := by simpa [targetStart] using targetBodyRun
          cases bodyResult with
          | err error =>
            cases targetBodyResult with
            | val vs => simp [resultRel] at bodyRel
            | err targetError =>
              have eq : result = .err error ∧ final = bodyFinal := by simpa [sourceStart, bodyRun] using run.symm
              obtain ⟨rfl, rfl⟩ := eq
              refine ⟨bodyG, .err targetError, targetBodyFinal, bodyExt, ?_, bodyRel, bodyStates, bodyStateWf,
                bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩
              rw [evaluateApp, targetClosure']
              simp only [List.length_cons, targetCostEq]
              have targetEnough : ¬ target.clock < cost := by omega
              rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun']
          | val sourceValues =>
            obtain ⟨sourceValue, rfl⟩ := evaluate_singleton_value sourceBody sourceBodyEnv sourceStart bodyFinal sourceValues bodyRun
            cases targetBodyResult with
            | err error => simp [resultRel] at bodyRel
            | val targetValues =>
              obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetBodyEnv targetStart targetBodyFinal targetValues targetBodyRun
              have valueRel : ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue targetValue := by
                simpa [resultRel] using bodyRel
              have restRel' : List.Forall₂ (ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code) sourceRest targetRest :=
                List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h bodyExt Set.Subset.rfl bodyGrowth) restRel
              have nextRun : evaluateApp requested sourceValue sourceRest bodyFinal = (result, final) := by
                simpa [sourceStart, bodyRun] using run
              have sourceValueWf : ValueWellFormedFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue := by
                have valueWf : ValueWellFormedFuel relationFuel g allowed targetStart.code sourceValue := by
                  cases sourceBodyWf.1 with
                  | cons head tail => exact head
                exact valueWellFormedFuel_mono valueWf bodyExt Set.Subset.rfl bodyGrowth
              have sourceRestWf' := valuesWellFormedFuel_mono sourceRestWf bodyExt Set.Subset.rfl bodyGrowth
              obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                appIH bodyG sourceValue targetValue sourceRest targetRest bodyFinal targetBodyFinal result final
                  restShort nextRun notType valueRel restRel' sourceValueWf sourceRestWf' bodyStateWf bodyStates bodyReady
                  bodyCompiler targetBodyCompiler bodyOracle
              refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g bodyG finalG bodyExt appExt, ?_, related,
                finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
              · rw [evaluateApp, targetClosure']
                simp only [List.length_cons, targetCostEq]
                have targetEnough : ¬ target.clock < cost := by omega
                rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun']
                exact targetRun
              · intro key entry found
                exact appGrowth key entry (bodyGrowth key entry found)

/-- Strong induction over remaining argument counts establishes closure
application simulation from the selected-body simulation and source
well-formedness hypotheses. -/
theorem growingAppSim_of_bodies {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat)
    (bodyIH : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceBody] [targetBody])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state)) :
    GrowingAppSim (F := F) passFuel relationFuel compiler allowed requested := by
  have all : ∀ limit, GrowingAppSimBelow (F := F) passFuel relationFuel limit compiler allowed requested := by
    intro limit
    induction limit using Nat.strongRecOn with
    | ind limit ih =>
      intro g sourceFun targetFun sourceArgs targetArgs source target result final bound run notType functions args
        functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
      cases sourceArgs with
      | nil =>
        have targetEmpty : targetArgs = [] := by
          have len := args.length_eq
          cases targetArgs with
          | nil => rfl
          | cons head tail => simp at len
        subst targetArgs
        exact evaluateApp_nil_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun
          source target result final run functions stateWf states ready sourceCompiler targetCompiler oracle
      | cons first rest =>
        have nonempty : first :: rest ≠ [] := by simp
        cases closureRun : destClosure source.maxApp requested sourceFun (first :: rest) with
        | none =>
          have bad : result = .err (.abort .typeError) := by
            rw [evaluateApp, closureRun] at run
            simpa using congrArg Prod.fst run.symm
          exact (notType bad).elim
        | some closure =>
          cases closure with
          | partialApp value =>
            exact evaluateApp_partial_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun value
              (first :: rest) targetArgs source target result final nonempty closureRun run functions args stateWf states ready
              sourceCompiler targetCompiler oracle
          | fullApp body env remaining =>
            exact evaluateApp_full_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun
              (first :: rest) targetArgs body env remaining source target result final nonempty closureRun run notType
              functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
              (bodyIH g target.code body) (bodyWf g) (ih (first :: rest).length bound)
  intro g sourceFun targetFun sourceArgs targetArgs source target result final run notType functions args functionWf
    argsWf stateWf states ready sourceCompiler targetCompiler oracle
  exact all (sourceArgs.length + 1) g sourceFun targetFun sourceArgs targetArgs source target result final
    (by omega) run notType functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle

/-- A pure transformed function can be evaluated in a related environment to
obtain a related value and an extended compiler state. -/
theorem pure_function_growing_witness {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (sourceValue : ClosSem.Value)
    (sourceRun : evaluate [sourceFn] sourceEnv source = (.val [sourceValue], source))
    (targetPure : ClosLang.pure targetFn = true)
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (fnIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn]) :
    ∃ nextG targetValue,
      stateExtends g nextG ∧ ValueRelFuel relationFuel nextG allowed target.code sourceValue targetValue ∧
      StateRelFuel relationFuel nextG allowed source target ∧ StateWellFormedFuel relationFuel nextG allowed target.code source ∧
      IncrementalInstallReady nextG source target := by
  obtain ⟨targetEnv, _, envs⟩ := envRelFuel_exists_of_wellFormed relationFuel g allowed target.code sourceEnv envWf
  obtain ⟨nextG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady, _, _, _, _⟩ :=
    fnIH g sourceEnv targetEnv source target (.val [sourceValue]) source sourceRun (by simp)
      (by simpa using envs 0 [(0, targetFn)]) envWf sourceWf states ready sourceCompiler targetCompiler oracle
  have targetSafe : targetResult ≠ .err (.abort .typeError) := by
    intro bad
    subst targetResult
    simp [resultRel] at related
  have pureList : ClosLang.pureList [targetFn] = true := by simp [ClosLang.pureList, targetPure]
  obtain ⟨targetValues, rfl, rfl⟩ := ClosProps.evaluate_pure [targetFn] targetEnv target targetFinal
    targetResult pureList targetRun targetSafe
  cases related with
  | cons head tail =>
    cases tail
    exact ⟨nextG, _, extended, head, finalStates, finalWf, finalReady⟩

/-- The pure known-location rewrite simulates its source application while
threading the compiler and oracle invariants through argument evaluation and
closure application. Its expression, well-formedness and application
induction hypotheses remain obligations of the enclosing simulation. -/
theorem callsFuel_app_pure_growing_at {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (pure : ClosLang.pure sourceFn = true)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed (some address))
    (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, targetPure, outEq⟩ :=
    callsFuel_app_pure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known pure
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_call_args trace targetArgs.length (address + 1) targetArgs
    simpa [outEq] using envs
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g sourceEnv targetEnv source target argsResult argsFinal
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq, evaluate, fixClock_evaluate, targetArgsRun]
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            have sourcePure : ClosLang.pureList [sourceFn] = true := by simp [ClosLang.pureList, pure]
            obtain ⟨fnValues, resultEq, finalEq⟩ :=
              ClosProps.evaluate_pure [sourceFn] sourceEnv argsFinal fnFinal fnResult sourcePure sourceFnRun fnSafe
            subst fnResult
            subst fnFinal
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal argsFinal fnValues sourceFnRun
            have envWf' := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
            have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal envWf' argsStateWf argsReady.auxEmpty
            rw [sourceFnRun] at functionWfEval
            obtain ⟨fnG, targetFnValue, fnExt, functionRel, fnStates, fnStateWf, fnReady⟩ :=
              pure_function_growing_witness passFuel relationFuel compiler argsG allowed sourceFn targetFn sourceEnv
                argsFinal targetArgsFinal fnValue sourceFnRun targetPure envWf' argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle (fnIH targetFn middle fnTraversal)
            have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetArgsFinal.code) sourceValues targetValues :=
              List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl (fun _ _ h => h)) valuesRel
            have appRun : evaluateApp (some address) fnValue sourceValues argsFinal = (result, final) := by
              simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
            have nonempty : sourceValues ≠ [] := by
              have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
              intro empty
              simp [empty] at len
            obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
              evaluateApp_known_full address fnValue sourceValues argsFinal final result nonempty appRun notType
            have sourceClosure' : destClosure targetArgsFinal.maxApp (some address) fnValue sourceValues =
                some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
            obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
              destClosure_known_direct relationFuel fnG allowed targetArgsFinal.code targetArgsFinal.maxApp address fnValue targetFnValue
                sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
            have code : targetArgsFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
              unfold findCode at found
              cases h : targetArgsFinal.code.lookup (address + 1) with
              | none => simp [h] at found
              | some entry =>
                rcases entry with ⟨arity, expression⟩
                simp only [h, bind, Option.bind_some] at found
                split at found
                · rename_i same
                  simp only [Option.some.injEq, Prod.mk.injEq] at found
                  obtain ⟨_, rfl⟩ := found
                  rw [same]
                · simp at found
            have targetClosure' : destClosure targetArgsFinal.maxApp (some address) targetFnValue targetValues =
                some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
              simpa [valuesRel'.length_eq] using targetClosure
            have targetEq := evaluate_pure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs
              targetEnv targetValues targetFnValue target targetArgsFinal stubEnv convertedBody targetArgsRun code targetClosure'
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetArgsFinal.code sourceValues :=
              valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl argsGrowth
            have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetArgsFinal.code fnValue := by
              have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                cases functionWfEval.1 with
                | cons head tail => exact head
              exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl (fun _ _ h => h)
            obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              appIH fnG fnValue targetFnValue sourceValues targetValues argsFinal targetArgsFinal result final appRun notType
                functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady argsCompiler targetArgsCompiler argsOracle
            refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [outEq] using targetEq.trans targetRun
            · intro key entry found
              exact growth key entry (argsGrowth key entry found)

/-- The impure known-location rewrite preserves evaluation of the function
expression and threads its compiler-state changes into the direct call. -/
theorem callsFuel_app_impure_growing_at {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (impure : ClosLang.pure sourceFn = false)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed (some address))
    (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, outEq⟩ :=
    callsFuel_app_impure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known impure
  have bindingEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      ((targetArgs ++ [targetFn]).map (0, ·)) := by
    apply envRelFuel_let_bindings (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFn])
      (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
        (ClosCall.variables .none targetArgs.length))
    simpa [outEq] using envs
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.mem_append]
    exact Or.inl member
  have fnEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetFn)] := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member ⊢
    exact Or.inr member
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g sourceEnv targetEnv source target argsResult argsFinal
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq]
          exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFn targetEnv target targetArgsFinal targetError targetArgsRun
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [sourceFnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates, fnStateWf,
              fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH targetFn middle fnTraversal argsG sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal
                sourceFnRun fnSafe (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val values => simp [resultRel] at fnRel
              | err targetError =>
                have eq : result = .err error ∧ final = fnFinal := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                rw [outEq]
                exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFn targetEnv
                  targetValues target targetArgsFinal targetFnFinal targetError targetArgsRun targetFnRun
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues sourceFnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) sourceValues targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp (some address) fnValue sourceValues fnFinal = (result, final) := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
                have nonempty : sourceValues ≠ [] := by
                  have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
                  intro empty
                  simp [empty] at len
                obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
                  evaluateApp_known_full address fnValue sourceValues fnFinal final result nonempty appRun notType
                have sourceClosure' : destClosure targetFnFinal.maxApp (some address) fnValue sourceValues =
                    some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
                obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
                  destClosure_known_direct relationFuel fnG allowed targetFnFinal.code targetFnFinal.maxApp address fnValue targetFnValue
                    sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
                have code : targetFnFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
                  unfold findCode at found
                  cases h : targetFnFinal.code.lookup (address + 1) with
                  | none => simp [h] at found
                  | some entry =>
                    rcases entry with ⟨arity, expression⟩
                    simp only [h, bind, Option.bind_some] at found
                    split at found
                    · rename_i same
                      simp only [Option.some.injEq, Prod.mk.injEq] at found
                      obtain ⟨_, rfl⟩ := found
                      rw [same]
                    · simp at found
                have targetClosure' : destClosure targetFnFinal.maxApp (some address) targetFnValue targetValues =
                    some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
                  simpa [valuesRel'.length_eq] using targetClosure
                have targetEq := callsFuel_app_impure_target_eq traversalFuel trace stubTrace address sourceFn (first :: rest)
                  initial passFinal out targetFn targetArgs middle targetEnv targetValues targetFnValue target targetArgsFinal targetFnFinal
                  stubEnv convertedBody passRun known impure argsTraversal fnTraversal targetArgsRun targetFnRun code targetClosure'
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code sourceValues :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
                  appIH fnG fnValue targetFnValue sourceValues targetValues fnFinal targetFnFinal result final appRun notType
                    functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady fnCompiler targetFnCompiler fnOracle
                exact ⟨finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt,
                  targetEq.trans targetRun, related, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, fun key entry found => growth key entry (prefixGrowth key entry found)⟩

/-- Both known-location rewrite branches simulate under the same growing
compiler-state hypotheses, selected by the source function's purity. -/
theorem callsFuel_app_known_growing_at {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed (some address))
    (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  cases purity : ClosLang.pure sourceFn with
  | false =>
    exact callsFuel_app_impure_growing_at passFuel relationFuel traversalFuel compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g sourceEnv targetEnv
      source target result final run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle
  | true =>
    exact callsFuel_app_pure_growing_at passFuel relationFuel traversalFuel compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g sourceEnv targetEnv
      source target result final run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- A source direct call with a non-type-error result can only propagate an
argument error, since the source state has no installed code. -/
theorem growingExprsSim_call {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.call trace ticks label sourceArgs] [.call trace ticks label targetArgs] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_call_args trace ticks label targetArgs (by simpa using envs)
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g sourceEnv targetEnv source target argsResult argsFinal argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        rw [evaluate, fixClock_evaluate, targetArgsRun]
    | val values =>
      have empty : argsFinal.code = HolFiniteMapExact.empty := argsStates.2.2.2.2.2
      have bad : result = .err (.abort .typeError) := by
        simpa [argsRun, findCode, empty, HolFiniteMapExact.empty] using congrArg Prod.fst run.symm
      exact (notType bad).elim

/-- The direct-call traversal composes the actual transformed arguments with
the growing-state source-call simulation. -/
theorem callsFuel_call_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.call trace ticks label args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed args target) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.call trace ticks label args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSim_call passFuel relationFuel compiler allowed trace ticks label args targetArgs (argsIH targetArgs argsRun)

/-- All application traversal branches compose the growing-state argument,
function and closure-application hypotheses at the given evaluation state. -/
theorem callsFuel_app_growing_at {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, passFinal))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address passFinal.1).isSome = true → address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed location)
    (g : State) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.app trace location sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  cases location with
  | none =>
    have sim := callsFuel_app_none_growing_sim passFuel relationFuel traversalFuel compiler allowed trace
      sourceFn sourceArgs initial passFinal out passRun argsIH fnIH argsWf fnWf appIH
    exact sim g sourceEnv targetEnv source target result final run notType (by simpa using envs) envWf sourceWf
      states ready sourceCompiler targetCompiler oracle
  | some address =>
    cases found : sptLookup address passFinal.1 with
    | none =>
      have sim := callsFuel_app_unknown_growing_sim passFuel relationFuel traversalFuel compiler allowed trace address
        sourceFn sourceArgs initial passFinal out passRun found argsIH fnIH argsWf fnWf appIH
      exact sim g sourceEnv targetEnv source target result final run notType (by simpa using envs) envWf sourceWf
        states ready sourceCompiler targetCompiler oracle
    | some value =>
      have known : (sptLookup address passFinal.1).isSome = true := by simp [found]
      exact callsFuel_app_known_growing_at passFuel relationFuel traversalFuel compiler allowed trace address sourceFn
        sourceArgs initial passFinal out passRun known (notAllowed address rfl known) argsIH fnIH argsWf fnWf appIH
        g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- Updating the reference stores leaves the installation invariant intact. -/
theorem incrementalInstallReady_setRefs {C F : Type} (g : State)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceRefs targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (ready : IncrementalInstallReady g source target) :
    IncrementalInstallReady g { source with refs := sourceRefs } { target with refs := targetRefs } := by
  obtain ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩ := ready
  exact ⟨well, included, known, auxEmpty, distinct, disjoint, fresh⟩

/-- Forcing related thunks simulates the evaluator, including memoization,
while carrying the growing compiler state and oracle invariants. -/
theorem runForced_growing {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (sourceValues targetValues : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : ClosMti.runForced sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (forceIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ ClosMti.runForced targetValues target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have inspected := destThunk_relatedFuel states values
  cases sourceDest : destThunk sourceValues source.refs with
  | badRef =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | notThunk =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | isThunk mode sourceValue =>
    rw [sourceDest] at inspected
    cases targetDest : destThunk targetValues target.refs with
    | badRef => rw [targetDest] at inspected; cases inspected
    | notThunk => rw [targetDest] at inspected; cases inspected
    | isThunk targetMode targetValue =>
      rw [targetDest] at inspected
      cases inspected with
      | isThunk _ _ _ payloadRel =>
        cases mode with
        | evaluated =>
          have eq : result = .val [sourceValue] ∧ final = source := by
            simpa [ClosMti.runForced, sourceDest] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨g, .val [targetValue], target, stateExtends_refl g ready.well.2,
            by simp [ClosMti.runForced, targetDest], .cons payloadRel .nil, states, sourceWf, ready,
            sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        | notEvaluated =>
          have payloadWf := destThunk_wellFormedFuel sourceValues source .notEvaluated sourceValue sourceWf sourceDest
          have forceEnv : EnvRelFuel relationFuel g allowed target.code [sourceValue] [targetValue] 0
              [(0, appUnit (.var .none 0))] := .equalLength rfl (.cons payloadRel .nil)
          have forcedWf := forceWf g target.code sourceValue source payloadWf sourceWf ready.auxEmpty
          cases forceRun : evaluate [appUnit (.var .none 0)] [sourceValue] source with
          | mk forceResult forceFinal =>
            rw [forceRun] at forcedWf
            have forceSafe : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              subst forceResult
              have eq : result = .err (.abort .typeError) := by
                simpa [ClosMti.runForced, sourceDest, forceRun] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨forceG, targetForceResult, targetForceFinal, extended, targetForceRun, forceRel, forceStates,
              forceStateWf, forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩ :=
              forceIH g [sourceValue] [targetValue] source target forceResult forceFinal forceRun forceSafe
                (by simpa using forceEnv) (.cons payloadWf .nil) sourceWf states ready sourceCompiler targetCompiler oracle
            cases forceResult with
            | err error =>
              cases targetForceResult with
              | val values => simp [resultRel] at forceRel
              | err targetError =>
                have eq : result = .err error ∧ final = forceFinal := by
                  simpa [ClosMti.runForced, sourceDest, forceRun] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                exact ⟨forceG, .err targetError, targetForceFinal, extended,
                  by simp [ClosMti.runForced, targetDest, targetForceRun], forceRel, forceStates, forceStateWf,
                  forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩
            | val forced =>
              cases targetForceResult with
              | err error => simp [resultRel] at forceRel
              | val targetForced =>
                have pointers := List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h extended Set.Subset.rfl growth) values
                have update := updateThunk_lists_relatedFuel sourceValues targetValues forced targetForced forceStates pointers forceRel
                cases sourceUpdate : updateThunk sourceValues forceFinal.refs forced with
                | none =>
                  have bad : result = .err (.abort .typeError) := by
                    simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using congrArg Prod.fst run.symm
                  exact (notType bad).elim
                | some sourceRefs =>
                  cases targetUpdate : updateThunk targetValues targetForceFinal.refs targetForced with
                  | none =>
                    have impossible := update.1 targetUpdate
                    rw [sourceUpdate] at impossible
                    contradiction
                  | some targetRefs =>
                    obtain ⟨sourceRefs', sourceUpdate', finalStates⟩ := update.2 targetRefs targetUpdate
                    rw [sourceUpdate] at sourceUpdate'
                    cases sourceUpdate'
                    have eq : result = .val forced ∧ final = { forceFinal with refs := sourceRefs } := by
                      simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using run.symm
                    have valuesWf : ValuesWellFormedFuel relationFuel forceG allowed targetForceFinal.code forced :=
                      valuesWellFormedFuel_mono forcedWf.1 extended Set.Subset.rfl growth
                    have finalWf := updateThunk_wellFormedFuel sourceValues forced forceFinal sourceRefs
                      forceStateWf valuesWf sourceUpdate
                    obtain ⟨rfl, rfl⟩ := eq
                    exact ⟨forceG, .val targetForced, { targetForceFinal with refs := targetRefs }, extended,
                      by simp [ClosMti.runForced, targetDest, targetForceRun, targetUpdate], forceRel, finalStates, finalWf,
                      incrementalInstallReady_setRefs forceG forceFinal targetForceFinal sourceRefs targetRefs forceReady,
                      forceCompiler, targetForceCompiler, forceOracle, growth⟩

/-- Force-thunk expressions compose argument simulation with the generated
force application and memoization simulation. -/
theorem growingExprsSim_force {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceArgs targetArgs)
    (forceIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [.op trace (.thunkOp .forceThunk) sourceArgs] [.op trace (.thunkOp .forceThunk) targetArgs] := by
  intro g sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace (.thunkOp .forceThunk) targetArgs (by simpa using envs)
  rw [ClosMti.evaluate_force_eq] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsWf,
      argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g sourceEnv targetEnv source target argsResult argsFinal argsRun argsSafe argsEnv envWf sourceWf
        states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [ClosMti.evaluate_force_eq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have forceRun : ClosMti.runForced sourceValues argsFinal = (result, final) := by simpa [argsRun] using run
        obtain ⟨finalG, targetResult, targetFinal, forceExt, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runForced_growing passFuel relationFuel compiler argsG allowed sourceValues targetValues argsFinal targetArgsFinal
            result final forceRun notType argsRel argsWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle forceIH forceWf
        refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g argsG finalG argsExt forceExt, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · simpa [ClosMti.evaluate_force_eq, targetArgsRun] using targetRun
        · intro key entry found
          exact growth key entry (argsGrowth key entry found)

/-- The direct-call traversal's force-thunk case uses its actual transformed
argument list and the generated force-application hypotheses. -/
theorem callsFuel_force_growing_sim {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed args target)
    (forceIH : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.op trace (.thunkOp .forceThunk) args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSim_force passFuel relationFuel compiler allowed trace args targetArgs (argsIH targetArgs argsRun) forceIH forceWf

/-- The evaluator-generated force application follows from the growing
closure-application simulation and the unit and variable cases. -/
theorem forceApplication_growing_sim {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed none) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  let unitExp : ClosLang.Exp := .op .none (.blockOp (.cons 0)) []
  have nilSim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [] [] :=
    growingExprsSim_of_forall₂ passFuel relationFuel compiler allowed .nil
  have nilWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_nil_wellFormedFuel env state stateWf
  have unitSim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [unitExp] [unitExp] :=
    growingExprsSim_ordinaryOp passFuel relationFuel compiler allowed .none (.blockOp (.cons 0)) [] []
      (by simp) (by simp) nilSim nilWf
  have unitWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [unitExp] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_ordinaryOp_wellFormedFuel .none (.blockOp (.cons 0)) [] env state (by simp) (by simp)
      (evaluate_nil_wellFormedFuel env state stateWf)
  have fnSim := growingExprsSim_var (F := F) passFuel relationFuel compiler allowed .none 0
  have fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [.var .none 0] env state) := by
    intro g code env state envWf stateWf _
    exact evaluate_var_state_wellFormedFuel .none 0 env state envWf stateWf
  simpa [appUnit, unitExp] using
    growingExprsSim_app passFuel relationFuel compiler allowed .none none (.var .none 0) (.var .none 0)
      [unitExp] [unitExp] rfl unitSim fnSim unitWf fnWf appIH

/-- Well-formedness of the generated force application follows from the
source evaluator's closure-application well-formedness. -/
theorem forceApplication_growing_wf {C F : Type} (relationFuel : Nat) (allowed : Set Nat)
    (appWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code function → ValuesWellFormedFuel relationFuel g allowed code args →
      StateWellFormedFuel relationFuel g allowed code state →
      EvalWellFormedFuel relationFuel g allowed code (evaluateApp none function args state))
    (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F)
    (valueWf : ValueWellFormedFuel relationFuel g allowed code value)
    (stateWf : StateWellFormedFuel relationFuel g allowed code state)
    (_oracleEmpty : OracleAuxEmpty state.compileOracle) :
    EvalWellFormedFuel relationFuel g allowed code (evaluate [appUnit (.var .none 0)] [value] state) := by
  let unitExp : ClosLang.Exp := .op .none (.blockOp (.cons 0)) []
  have unitWf : EvalWellFormedFuel relationFuel g allowed code (evaluate [unitExp] [value] state) := by
    exact evaluate_ordinaryOp_wellFormedFuel .none (.blockOp (.cons 0)) [] [value] state (by simp) (by simp)
      (evaluate_nil_wellFormedFuel [value] state stateWf)
  have evalWf := evaluate_app_wellFormedFuel .none none (.var .none 0) [unitExp] [value] state stateWf unitWf
    (fun start _ startWf => evaluate_var_state_wellFormedFuel .none 0 [value] start (.cons valueWf .nil) startWf)
    (fun function args start _ functionWf argsWf startWf => appWf g code function args start functionWf argsWf startWf)
  simpa [appUnit, unitExp] using evalWf

/-- The force traversal follows from its argument simulation and the growing
closure-application simulation and source well-formedness. -/
theorem callsFuel_force_growing_of_app {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSim (F := F) passFuel relationFuel compiler allowed args target)
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed none)
    (appWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code function → ValuesWellFormedFuel relationFuel g allowed code args →
      StateWellFormedFuel relationFuel g allowed code state →
      EvalWellFormedFuel relationFuel g allowed code (evaluateApp none function args state)) :
    GrowingExprsSim (F := F) passFuel relationFuel compiler allowed [.op trace (.thunkOp .forceThunk) args] [out] := by
  exact callsFuel_force_growing_sim passFuel relationFuel traversalFuel compiler allowed trace args initial final out
    run argsIH (forceApplication_growing_sim passFuel relationFuel compiler allowed appIH)
    (forceApplication_growing_wf relationFuel allowed appWf)

/-- An unrestricted growing simulation is valid above every pass state. -/
theorem growingExprsSim_from {C F : Type} (passFuel relationFuel : Nat) (compiler : ClosSem.Compiler C)
    (required : State) (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp)
    (sim : GrowingExprsSim (F := F) passFuel relationFuel compiler allowed sourceExps targetExps) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed sourceExps targetExps := by
  intro g _
  exact sim g

/-- A simulation valid above one pass state is valid above any extension of
that state. -/
theorem growingExprsSimFrom_mono {C F : Type} (passFuel relationFuel : Nat) (compiler : ClosSem.Compiler C)
    (smaller larger : State) (allowed : Set Nat) (sourceExps targetExps : List ClosLang.Exp)
    (growth : stateExtends smaller larger)
    (sim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler smaller allowed sourceExps targetExps) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler larger allowed sourceExps targetExps := by
  intro g extended
  exact sim g (stateExtends_trans smaller larger g growth extended)

/-- A pass-state-restricted list simulation supplies the installed-program
simulation at that same state. This is Flapjack-specific infrastructure; the
smaller-clock bound is retained for the enclosing induction. -/
theorem growingExprsSimFrom_installedBelow {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp)
    (sim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler g allowed program targetProgram) :
    InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel limit compiler g allowed program targetProgram := by
  intro source target result final _ run notType sourceWf states ready sourceCompiler targetCompiler oracle
  have envs : EnvRelFuel relationFuel g allowed target.code [] [] 0 (targetProgram.map (0, ·)) := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel]
  exact sim g (stateExtends_refl g ready.well.2) [] [] source target result final run notType envs .nil sourceWf
    states ready sourceCompiler targetCompiler oracle

/-- An unbounded pass-state simulation is valid at every clock bound. This
is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_below {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp)
    (sim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed sourceExps targetExps) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceExps targetExps := by
  intro g growth sourceEnv targetEnv source target result final _
  exact sim g growth sourceEnv targetEnv source target result final

/-- A same-clock simulation is a special case of the clock-allowing
interface. This is Flapjack-specific infrastructure. -/
theorem growingExprsSimFromBelow_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp)
    (sim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceExps targetExps) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceExps targetExps := by
  intro g growth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩ :=
    sim g growth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
      sourceCompiler targetCompiler oracle
  refine ⟨0, finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩
  simpa using targetRun

/-- A same-clock application simulation is a special case of the
clock-allowing interface. This is Flapjack-specific infrastructure. -/
theorem growingAppSimClockBelow_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (loc : Option Nat)
    (sim : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed loc) :
    GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed loc := by
  intro g function targetFunction args targetArgs source target result final clock run notType functions arguments
    functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
  obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩ :=
    sim g function targetFunction args targetArgs source target result final clock run notType functions arguments
      functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
  refine ⟨0, finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩
  simpa using targetRun

/-- A clock-bounded simulation can be used at a smaller clock bound. This
is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_mono_clock {C F : Type} (passFuel relationFuel smaller larger : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp) (bound : smaller ≤ larger)
    (sim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel larger compiler required allowed sourceExps targetExps) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel smaller compiler required allowed sourceExps targetExps := by
  intro g growth sourceEnv targetEnv source target result final clock
  exact sim g growth sourceEnv targetEnv source target result final (Nat.lt_of_lt_of_le clock bound)

/-- A clock-bounded simulation remains valid above an extension of its
required pass state. This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_mono_state {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (smaller larger : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp) (growth : stateExtends smaller larger)
    (sim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler smaller allowed sourceExps targetExps) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler larger allowed sourceExps targetExps := by
  intro g extended
  exact sim g (stateExtends_trans smaller larger g growth extended)

/-- A clock-allowing simulation remains valid above an extension of its
required pass state. This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_mono_state {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (smaller larger : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp) (growth : stateExtends smaller larger)
    (sim : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler smaller allowed sourceExps targetExps) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler larger allowed sourceExps targetExps := by
  intro g extended
  exact sim g (stateExtends_trans smaller larger g growth extended)

/-- The open recursive-closure case follows from the actual expression
traversal induction. Closed groups are returned as the outstanding stub
case. This is Flapjack-specific simulation infrastructure. -/
theorem recClosureRelFuel_target_body_sim_or_stub {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (index arity : Nat) (body targetBody : ClosLang.Exp)
    (related : recClosureRelFuel relationFuel g allowed code loc fns1 fns2)
    (sourceLookup : fns1[index]? = some (arity, body))
    (targetLookup : fns2[index]? = some (arity, targetBody))
    (exprIH : ∀ depth before after,
      depth < max relationFuel (listBudget (fns1.map Prod.snd) + 1) →
      callsFuel depth body before = some (targetBody, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before → wellFormed before →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler after allowed [body] [targetBody]) :
    (∃ trace stubIndex, fns2 = callsListSource trace stubIndex loc fns1) ∨
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler g allowed [body] [targetBody] := by
  rcases recClosureRelFuel_target_body relationFuel g allowed code loc fns1 fns2 index arity body targetBody
      related sourceLookup targetLookup with stubs | ⟨depth, before, after, depthLt, selected,
        bodyDistinct, bodyFresh, beforeWf, extended⟩
  · exact Or.inl stubs
  · exact Or.inr (growingExprsSimFromBelow_mono_state passFuel relationFuel limit compiler after g allowed
      [body] [targetBody] extended (exprIH depth before after depthLt selected bodyDistinct bodyFresh beforeWf))

/-- A known generated stub simulates its source body when the actual probe
traversal supplies a simulation of its converted body. The argument bound is
provided by closure application; the probe-state expression induction remains
an explicit assumption because reserved locations need not be fully well
formed. This is Flapjack-specific infrastructure, not a HOL theorem port. -/
theorem recClosureRelFuel_known_body_sim_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (body targetBody : ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (clock : source.clock < limit)
    (run : evaluate [body] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (related : recClosureRelFuel relationFuel g allowed target.code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, body))
    (targetLookup : targetFns[index]? = some (arity, targetBody))
    (notAllowed : 2 * index + loc ∉ allowed)
    (sourceBound : arity ≤ sourceEnv.length)
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (bodyIH : ∀ converted depth before after,
      depth < max relationFuel (listBudget (sourceFns.map Prod.snd) + 1) →
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before →
      (before.2.map Prod.fst).Nodup →
      (∀ n, ClosProps.freeVarExp n converted → n < arity) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler g allowed [body] [converted]) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧
      evaluate [targetBody] targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨trace, converted, depth, before, after, _, _, targetStub, codeLookup,
    depthBound, selectedRun, distinct, fresh, beforeDistinct, _, _, _, _, _, _, _, closed, _⟩ :=
    recClosureRelFuel_known_probe_body relationFuel g allowed target.code loc sourceFns targetFns
      index arity body related sourceLookup notAllowed
  have bodyEq : targetBody = .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity) := by
    rw [targetLookup] at targetStub
    exact (Prod.mk.inj (Option.some.inj targetStub)).2
  have stubEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity))] := by
    simpa [bodyEq] using envs
  obtain ⟨targetBound, bodyEnv⟩ :=
    envRelFuel_stub_body_prefix relationFuel g allowed target.code trace (loc + 2 * index + 1)
      arity converted sourceEnv targetEnv stubEnv sourceBound closed
  obtain ⟨extraClock, finalG, targetResult, targetFinal, extended, targetRun, resultRelated,
    finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    bodyIH converted depth before after depthBound selectedRun distinct fresh beforeDistinct closed
      g (stateExtends_refl g ready.well.2) sourceEnv (targetEnv.take arity) source target result final
      clock run notType (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
  refine ⟨extraClock + 1, finalG, targetResult, targetFinal, extended, ?_, resultRelated, finalStates,
    finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
  rw [bodyEq, evaluate_generated_stub_with_allowance trace (loc + 2 * index + 1) arity extraClock
    converted targetEnv target targetBound codeLookup]
  exact targetRun

/-- Known generated closure bodies satisfy the arity-restricted simulation
interface used by application induction, provided the actual probe-body
traversals simulate at each growing compiler state. This is Flapjack-specific
infrastructure; the probe traversal induction remains an explicit premise. -/
theorem recClosureRelFuel_known_body_arity_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (body targetBody : ClosLang.Exp)
    (related : recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, body))
    (targetLookup : targetFns[index]? = some (arity, targetBody))
    (notAllowed : 2 * index + loc ∉ allowed)
    (bodyIH : ∀ larger, stateExtends g larger → ∀ converted depth before after,
      depth < max relationFuel (listBudget (sourceFns.map Prod.snd) + 1) →
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before →
      (before.2.map Prod.fst).Nodup →
      (∀ n, ClosProps.freeVarExp n converted → n < arity) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler larger allowed [body] [converted]) :
    GrowingExprsSimFromBelowWithClockArity (F := F) passFuel relationFuel limit compiler g allowed arity [body] [targetBody] := by
  intro larger growth sourceEnv targetEnv source target result final clock sourceBound run notType envs envWf sourceWf
    states ready sourceCompiler targetCompiler oracle
  have related' := recClosureRelFuel_retarget relationFuel g larger allowed code target.code loc sourceFns targetFns
    related growth ready.included
  exact recClosureRelFuel_known_body_sim_withClock passFuel relationFuel limit compiler larger allowed loc
    sourceFns targetFns index arity body targetBody sourceEnv targetEnv source target result final clock run notType
    related' sourceLookup targetLookup notAllowed sourceBound (by simpa using envs) envWf sourceWf states ready
    sourceCompiler targetCompiler oracle (bodyIH larger growth)

/-- If a probe state can be completed with an auxiliary-code suffix that is
fresh for the body and whose final state extends into the installed compiler
state, the ordinary well-formed traversal induction applies to that probe.
Constructing such a suffix for every probe remains an obligation. This is
Flapjack-specific simulation infrastructure, not a HOL theorem port. -/
theorem probeBody_sim_of_completed_state {C F : Type} (passFuel relationFuel limit depth : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (body converted : ClosLang.Exp) (before after : State) (suffix : List (Nat × Nat × ClosLang.Exp))
    (run : callsFuel depth body before = some (converted, after))
    (distinct : (codeLocationsExp body).Nodup)
    (fresh : LabelsFresh (codeLocationsExp body) (appendAux before suffix))
    (completedWf : wellFormed (appendAux before suffix))
    (completedGrowth : stateExtends (appendAux after suffix) g)
    (exprIH : ∀ initial final,
      callsFuel depth body initial = some (converted, final) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) initial →
      wellFormed initial →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [body] [converted]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler g allowed [body] [converted] := by
  have completedRun : callsFuel depth body (appendAux before suffix) =
      some (converted, appendAux after suffix) := by
    simpa [run] using (callsFuel_appendAux_pair depth).1 body before suffix
  exact growingExprsSimFromBelowWithClock_mono_state passFuel relationFuel limit compiler
    (appendAux after suffix) g allowed [body] [converted] completedGrowth
    (exprIH (appendAux before suffix) (appendAux after suffix) completedRun distinct fresh completedWf)

/-- Related closure bodies satisfy the arity-restricted application
interface in both extracted and open groups, assuming the ordinary
well-formed body-traversal induction. Extracted probe states are completed
with fresh installed code before invoking that induction. This is
Flapjack-specific infrastructure, not a HOL theorem port. -/
theorem recClosureRelFuel_body_arity_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (body targetBody : ClosLang.Exp)
    (related : recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, body))
    (targetLookup : targetFns[index]? = some (arity, targetBody))
    (exprIH : ∀ converted depth before after,
      depth < max relationFuel (listBudget (sourceFns.map Prod.snd) + 1) →
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before →
      wellFormed before →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler after allowed [body] [converted]) :
    GrowingExprsSimFromBelowWithClockArity (F := F) passFuel relationFuel limit compiler g allowed arity [body] [targetBody] := by
  intro larger growth sourceEnv targetEnv source target result final clock sourceBound run notType envs envWf sourceWf
    states ready sourceCompiler targetCompiler oracle
  have related' := recClosureRelFuel_retarget relationFuel g larger allowed code target.code loc sourceFns targetFns
    related growth ready.included
  rcases recClosureRelFuel_body_traversal_cases relationFuel larger allowed target.code loc sourceFns targetFns
      index arity body targetBody related' sourceLookup targetLookup with
    ⟨trace, converted, depth, before, after, _, _, bodyEq, codeLookup, depthBound, selectedRun,
      distinct, fresh, beforeDistinct, beforeWeak, knownCovered, _, beforeGrowth, _, afterGrowth, _, closed, _⟩ |
    ⟨depth, before, after, depthBound, selectedRun, distinct, fresh, beforeWf, extended⟩
  · have stubEnv : EnvRelFuel relationFuel larger allowed target.code sourceEnv targetEnv 0
        [(0, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity))] := by
      simpa [bodyEq] using envs
    obtain ⟨targetBound, bodyEnv⟩ :=
      envRelFuel_stub_body_prefix relationFuel larger allowed target.code trace (loc + 2 * index + 1)
        arity converted sourceEnv targetEnv stubEnv sourceBound closed
    obtain ⟨suffix, completedWf, completedFresh, completedGrowth⟩ :=
      weaklyWellFormed_complete_aux_fresh before after larger (codeLocationsExp body) beforeWeak beforeDistinct
        ready.well beforeGrowth afterGrowth fresh knownCovered
    have bodySim := probeBody_sim_of_completed_state passFuel relationFuel limit depth compiler larger allowed
      body converted before after suffix selectedRun distinct completedFresh completedWf completedGrowth
      (fun initial final traversal bodyDistinct bodyFresh initialWf =>
        exprIH converted depth initial final depthBound traversal bodyDistinct bodyFresh initialWf)
    obtain ⟨extraClock, finalG, targetResult, targetFinal, finalExt, targetRun, resultRelated,
      finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩ :=
      bodySim
        larger (stateExtends_refl larger ready.well.2) sourceEnv (targetEnv.take arity) source target result final
        clock run notType (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    refine ⟨extraClock + 1, finalG, targetResult, targetFinal, finalExt, ?_, resultRelated, finalStates,
      finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, codeGrowth⟩
    rw [bodyEq, evaluate_generated_stub_with_allowance trace (loc + 2 * index + 1) arity extraClock
      converted targetEnv target targetBound codeLookup]
    exact targetRun
  · have bodySim := growingExprsSimFromBelowWithClock_mono_state passFuel relationFuel limit compiler after larger
      allowed [body] [targetBody] extended (exprIH targetBody depth before after depthBound selectedRun distinct fresh beforeWf)
    exact bodySim larger (stateExtends_refl larger ready.well.2) sourceEnv targetEnv source target result final clock run
      notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- A clock-bounded pass-state simulation supplies the corresponding
installed-program simulation. This is Flapjack-specific infrastructure. -/
theorem growingExprsSimFromBelow_installedBelow {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp)
    (sim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler g allowed program targetProgram) :
    InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel limit compiler g allowed program targetProgram := by
  intro source target result final clock run notType sourceWf states ready sourceCompiler targetCompiler oracle
  have envs : EnvRelFuel relationFuel g allowed target.code [] [] 0 (targetProgram.map (0, ·)) := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel]
  exact sim g (stateExtends_refl g ready.well.2) [] [] source target result final clock run notType envs .nil
    sourceWf states ready sourceCompiler targetCompiler oracle

/-- A clock-allowing pass-state simulation supplies the corresponding
installed-program simulation. This is Flapjack-specific infrastructure. -/
theorem growingExprsSimFromBelowWithClock_installedBelow {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (g : State) (allowed : Set Nat)
    (program targetProgram : List ClosLang.Exp)
    (sim : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler g allowed program targetProgram) :
    InstalledProgramSimBelowWithClock (C := C) (F := F) passFuel relationFuel limit compiler g allowed program targetProgram := by
  intro source target result final clock run notType sourceWf states ready sourceCompiler targetCompiler oracle
  have envs : EnvRelFuel relationFuel g allowed target.code [] [] 0 (targetProgram.map (0, ·)) := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel]
  exact sim g (stateExtends_refl g ready.well.2) [] [] source target result final clock run notType envs .nil
    sourceWf states ready sourceCompiler targetCompiler oracle

/-- Matching ticks preserve a simulation above the required pass state. This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_tick {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed
      [.tick trace sourceBody] [.tick trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have eq : result = .err (.abort .timeoutError) ∧ final = source := by simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .err (.abort .timeoutError), target, stateExtends_refl g ready.well.2,
      by simp [evaluate, targetZero], rfl, states, sourceWf, ready, sourceCompiler, targetCompiler, oracle,
      fun _ _ h => h⟩
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp (by simpa using envs)
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv (decClock 1 source) (decClock 1 target) result final bodyRun notType
        (by simpa [decClock] using bodyEnv) envWf (stateWellFormedFuel_clock sourceWf _)
        (stateRelFuel_decClock states 1) (incrementalInstallReady_decClock g source target 1 ready)
        (by simpa [decClock] using sourceCompiler) (by simpa [decClock] using targetCompiler)
        (by simpa [decClock] using oracle)
    refine ⟨finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    simpa [evaluate, targetNonzero] using targetRun

/-- Matching raises preserve a simulation above the required pass state. This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_raise {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed
      [.raise trace sourceBody] [.raise trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp (by simpa using envs)
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodySafe (by simpa using bodyEnv)
        envWf sourceWf states ready sourceCompiler targetCompiler oracle
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err targetError =>
        have eq : result = .err error ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        exact ⟨finalG, .err targetError, targetFinal, extended, by simp [evaluate, targetRun], related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv target targetFinal targetValues targetRun
        have eq : result = .err (.raise value) ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        have valueRel : ValueRelFuel relationFuel finalG allowed targetFinal.code value targetValue := by
          simpa [resultRel] using related
        exact ⟨finalG, .err (.raise targetValue), targetFinal, extended, by simp [evaluate, targetRun], valueRel,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Condition and branch simulations compose above a required pass state.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_if {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sc sy sn tc ty tn : ClosLang.Exp)
    (conditionIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sc] [tc])
    (yesIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sy] [ty])
    (noIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sn] [tn]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed
      [.ifThenElse trace sc sy sn] [.ifThenElse trace tc ty tn] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have ifEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .ifThenElse trace tc ty tn)] := by simpa using envs
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) ifEnv
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condSafe : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨condG, targetCondResult, targetCondFinal, condExt, targetCondRun, condRel, condStates,
      condWf, condReady, condCompiler, targetCondCompiler, condOracle, condGrowth⟩ :=
      conditionIH g requiredGrowth sourceEnv targetEnv source target condResult condFinal condRun condSafe
        (by simpa using conditionEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), condFinal)).2
    let targetNext := (fixClock target ((), targetCondFinal)).2
    have nextStates : StateRelFuel relationFuel condG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 condStates
    have nextWf : StateWellFormedFuel relationFuel condG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock condWf (min source.clock condFinal.clock)
    have nextReady : IncrementalInstallReady condG sourceNext targetNext :=
      incrementalInstallReady_fixClock condG source condFinal target targetCondFinal condReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using condCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by
      simpa [targetNext, fixClock] using targetCondCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using condOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := condGrowth
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have eq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, condRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨condG, .err targetError, targetNext, condExt, ?_, condRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetCondRun, fixClock, targetNext]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv target targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel relationFuel condG allowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have eq : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact (notType eq).elim
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          have branchEnvWf := valuesWellFormedFuel_mono envWf condExt Set.Subset.rfl nextGrowth
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              noIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              yesIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Pass-state-restricted simulation composition for let.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_let {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBindings targetBindings : List ClosLang.Exp) (sourceBody targetBody : ClosLang.Exp)
    (bindingsIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed sourceBindings targetBindings)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed
      [.let trace sourceBindings sourceBody] [.let trace targetBindings targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have letEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .let trace targetBindings targetBody)] := by simpa using envs
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody letEnv
  have bindingWf := bindingsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingSafe : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bindingG, targetBindingResult, targetBindingFinal, bindingExt, targetBindingRun, bindingRel,
      bindingStates, bindingStateWf, bindingReady, bindingCompiler, targetBindingCompiler, bindingOracle, bindingGrowth⟩ :=
      bindingsIH g requiredGrowth sourceEnv targetEnv source target bindingResult bindingFinal bindingRun bindingSafe
        bindingsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextStates : StateRelFuel relationFuel bindingG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextWf : StateWellFormedFuel relationFuel bindingG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bindingStateWf (min source.clock bindingFinal.clock)
    have nextReady : IncrementalInstallReady bindingG sourceNext targetNext :=
      incrementalInstallReady_fixClock bindingG source bindingFinal target targetBindingFinal bindingReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bindingCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBindingCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bindingOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have eq : result = .err error ∧ final = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bindingG, .err targetError, targetNext, bindingExt, ?_, bindingRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBindingRun, fixClock, targetNext]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel bindingG allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv target
            targetBindingFinal targetValues targetBindingRun
          exact valuesRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody letEnv
        have outerEnv' := envRelFuel_mono outerEnv bindingExt Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valuesRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf) bindingExt Set.Subset.rfl nextGrowth
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (result, final) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          bodyIH bindingG (stateExtends_trans required g bindingG requiredGrowth bindingExt) (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) sourceNext targetNext result final
            bodyRun notType (by simpa using bodyEnv) bodyEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
        refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g bindingG finalG bindingExt extended, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · simpa [evaluate, targetBindingRun, fixClock, targetNext] using targetRun
        · intro key entry found
          exact growth key entry (nextGrowth key entry found)

/-- Pass-state-restricted simulation composition for handle.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_handle {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sb sh tb th : ClosLang.Exp)
    (bodyIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sb] [tb])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sb] env state))
    (handlerIH : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [sh] [th]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [.handle trace sb sh] [.handle trace tb th] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have handleEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .handle trace tb th)] := by simpa using envs
  have bodyEnv := envRelFuel_handle_body trace tb th handleEnv
  have sourceBodyWf := bodyWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at sourceBodyWf
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
      bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
      bodyIH g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextStates : StateRelFuel relationFuel bodyG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextWf : StateWellFormedFuel relationFuel bodyG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bodyStateWf (min source.clock bodyFinal.clock)
    have nextReady : IncrementalInstallReady bodyG sourceNext targetNext :=
      incrementalInstallReady_fixClock bodyG source bodyFinal target targetBodyFinal bodyReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bodyCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBodyCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bodyOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have eq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bodyG, .val targetValues, targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBodyRun, fixClock, targetNext]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have eq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨bodyG, .err (.abort targetAbort), targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
              nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
            simp [evaluate, targetBodyRun, fixClock, targetNext]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel relationFuel bodyG allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv := envRelFuel_mono handleEnv bodyExt Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have payloadWf : ValueWellFormedFuel relationFuel bodyG allowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 bodyExt Set.Subset.rfl nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf bodyExt Set.Subset.rfl nextGrowth
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              handlerIH bodyG (stateExtends_trans required g bodyG requiredGrowth bodyExt) (sourceValue :: sourceEnv) (targetValue :: targetEnv) sourceNext targetNext
                sourceResult sourceFinal handlerRun notType (by simpa using handlerEnv) (.cons payloadWf outerWf)
                nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g bodyG finalG bodyExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetBodyRun, fixClock, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Ordinary operations preserve simulation above a required pass state.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFrom_ordinaryOp {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (sourceArgs targetArgs : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsSim : GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed sourceArgs targetArgs)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state)) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed
      [.op trace op sourceArgs] [.op trace op targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace op targetArgs (by simpa using envs)
  have sourceArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  rw [evaluate_ordinaryOp_eq trace op sourceArgs sourceEnv source notInstall notForce] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    rw [argsRun] at sourceArgsWf
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsSim g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRel
        have valuesWf : ValuesWellFormedFuel relationFuel argsG allowed targetArgsFinal.code sourceValues := by
          apply valuesWellFormedFuel_mono _ argsExt Set.Subset.rfl argsGrowth
          exact sourceArgsWf.1
        have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp
          (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
          (fun (s : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F) =>
            t.code = targetArgsFinal.code ∧ StateRelFuel relationFuel argsG allowed s t)
          argsFinal targetArgsFinal sourceValues.reverse targetValues.reverse op
          ⟨valueRelFuel_simple relationFuel argsG allowed targetArgsFinal.code,
            stateRelFuel_simple relationFuel argsG allowed targetArgsFinal.code⟩ ⟨⟨rfl, argsStates⟩, valuesRel⟩
        have primWf := doApp_result_wellFormedFuel op sourceValues.reverse argsFinal argsStateWf
          (valuesWellFormedFuel_reverse valuesWf)
        cases primRun : doApp op sourceValues.reverse argsFinal with
        | err error =>
          simp only [primRun] at sim
          obtain ⟨targetError, targetPrim, errors⟩ := sim
          have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, errors, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
        | val pair =>
          obtain ⟨value, sourceFinal⟩ := pair
          simp only [primRun] at sim primWf
          obtain ⟨targetValue, targetFinal, valueRel, ⟨codeEq, finalStates⟩, targetPrim⟩ := sim
          have eq : result = .val [value] ∧ final = sourceFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          have finalReady := incrementalInstallReady_doApp argsG argsFinal targetArgsFinal final targetFinal
            sourceValues.reverse targetValues.reverse value targetValue op argsReady primRun targetPrim
          have srcFields := ClosInterp.doApp_compilerFields op sourceValues.reverse argsFinal final value primRun
          have tgtFields := ClosInterp.doApp_compilerFields op targetValues.reverse targetArgsFinal targetFinal targetValue targetPrim
          refine ⟨argsG, .val [targetValue], targetFinal, argsExt, ?_, ?_, ?_, ?_, finalReady, ?_, ?_, ?_, ?_⟩
          · simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
          · change List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetFinal.code) [value] [targetValue]
            rw [codeEq]
            exact .cons valueRel .nil
          · simpa [codeEq] using finalStates
          · simpa [codeEq, PrimitiveResultWellFormedFuel] using primWf.2
          · exact srcFields.1.trans argsCompiler
          · exact tgtFields.1.trans targetArgsCompiler
          · rw [tgtFields.2.1, srcFields.2.1]
            exact argsOracle
          · intro key entry found
            rw [codeEq]
            exact argsGrowth key entry found

/-- Install arguments may use the pass-state-restricted simulation.
This is Flapjack-specific simulation infrastructure. -/
theorem evaluate_install_growing_args_from {C F : Type} (fuel relationFuel : Nat) (required g : State) (requiredGrowth : stateExtends required g)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)))
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (argsSim : GrowingExprsSimFrom (F := F) fuel relationFuel compiler required allowed sourceArgs targetArgs)
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  apply evaluate_install_incremental_sim fuel relationFuel g allowed compiler trace sourceArgs targetArgs
    sourceEnv targetEnv source target result final run notType ?_ programIH
  intro sourceResult sourceMiddle argsRun argsSafe
  obtain ⟨middleG, targetResult, targetMiddle, extended, targetRun, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩ :=
    argsSim g requiredGrowth sourceEnv targetEnv source target sourceResult sourceMiddle argsRun argsSafe envs envWf sourceWf
      states ready sourceCompiler targetCompiler targetOracle
  exact ⟨middleG, targetResult, targetMiddle, targetRun, extended, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩

/-- Clock-bounded argument simulation for the install case. This is
Flapjack-specific simulation infrastructure. -/
theorem evaluate_install_growing_args_below {C F : Type} (fuel relationFuel limit : Nat) (required g : State) (requiredGrowth : stateExtends required g)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (clock : source.clock < limit)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)))
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (argsSim : GrowingExprsSimFromBelow (F := F) fuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  apply evaluate_install_incremental_sim fuel relationFuel g allowed compiler trace sourceArgs targetArgs
    sourceEnv targetEnv source target result final run notType ?_ programIH
  intro sourceResult sourceMiddle argsRun argsSafe
  obtain ⟨middleG, targetResult, targetMiddle, extended, targetRun, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩ :=
    argsSim g requiredGrowth sourceEnv targetEnv source target sourceResult sourceMiddle clock argsRun argsSafe envs envWf sourceWf
      states ready sourceCompiler targetCompiler targetOracle
  exact ⟨middleG, targetResult, targetMiddle, targetRun, extended, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩

/-- Clock-allowing argument simulation for the install case. This is
Flapjack-specific simulation infrastructure. -/
theorem evaluate_install_growing_args_below_withClock {C F : Type} (fuel relationFuel limit : Nat) (required g : State) (requiredGrowth : stateExtends required g)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (clock : source.clock < limit)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : evaluate [.op trace .install sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)))
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (argsSim : GrowingExprsSimFromBelowWithClock (F := F) fuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (programIH : ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? fuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelowWithClock (C := C) (F := F) fuel relationFuel source.clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    ∃ extraClock nextG targetResult targetFinal,
      stateExtends g nextG ∧
      evaluate [.op trace .install targetArgs] targetEnv { target with clock := target.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel nextG allowed targetFinal.code))
        (ValueRelFuel relationFuel nextG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel nextG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel nextG allowed targetFinal.code final ∧
      IncrementalInstallReady nextG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  apply evaluate_install_incremental_sim_withClock fuel relationFuel g allowed compiler trace sourceArgs targetArgs
    sourceEnv targetEnv source target result final run notType ?_ programIH
  intro sourceResult sourceMiddle argsRun argsSafe
  obtain ⟨extraClock, middleG, targetResult, targetMiddle, extended, targetRun, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩ :=
    argsSim g requiredGrowth sourceEnv targetEnv source target sourceResult sourceMiddle clock argsRun argsSafe envs envWf sourceWf
      states ready sourceCompiler targetCompiler targetOracle
  exact ⟨extraClock, middleG, targetResult, targetMiddle, targetRun, extended, related, middleStates, middleWf,
    middleReady, finalCompiler, finalTargetCompiler, finalOracle, growth⟩

/-- The fuel-bounded variable traversal needs no expression induction
hypothesis. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_var_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (index : Nat)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.var trace index) initial = some (out, final)) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.var trace index] [out] := by
  exact growingExprsSim_from passFuel relationFuel compiler final allowed _ _
    (callsFuel_var_growing_sim passFuel relationFuel traversalFuel compiler allowed trace index initial final out run)

/-- The fuel-bounded tick traversal carries the pass-state requirement into
its body. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_tick_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [body] [target]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.tick trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_tick passFuel relationFuel compiler next allowed trace body target (bodyIH target bodyRun)

/-- The fuel-bounded raise traversal carries the pass-state requirement into
its body. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_raise_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [body] [target]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.raise trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_raise passFuel relationFuel compiler next allowed trace body target (bodyIH target bodyRun)

/-- The fuel-bounded conditional traversal composes child simulations above
its final pass state. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_if_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (conditionIH : ∀ target middle, callsFuel traversalFuel condition initial = some (target, middle) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [condition] [target])
    (yesIH : ∀ target before after, callsFuel traversalFuel yes before = some (target, after) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [yes] [target])
    (noIH : ∀ target middle, callsFuel traversalFuel no middle = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [no] [target]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed
      [.ifThenElse trace condition yes no] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_if passFuel relationFuel compiler next allowed trace condition yes no
    targetCondition targetYes targetNo (conditionIH targetCondition middle1 conditionRun)
    (yesIH targetYes middle1 middle2 yesRun) (noIH targetNo middle2 noRun)

/-- Fuel-bounded let traversal with simulations above the final pass state.
This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_let_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.let trace bindings body) initial = some (out, final))
    (bindingsIH : ∀ target middle, callsListFuel traversalFuel bindings initial = some (target, middle) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed bindings target)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body middle = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [body] [target]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.let trace bindings body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_let passFuel relationFuel compiler next allowed trace bindings targetBindings body targetBody
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

/-- Fuel-bounded handle traversal with simulations above the final pass state.
This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_handle_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.handle trace body handler) initial = some (out, final))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body initial = some (target, middle) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [body] [target])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel traversalFuel handler middle = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [handler] [target]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.handle trace body handler] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_handle passFuel relationFuel compiler next allowed trace body handler targetBody targetHandler
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- Fuel-bounded ordinary-operation traversal above the final pass state.
This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_ordinaryOp_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace op args) initial = some (out, final))
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed args target)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate args env state)) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed [.op trace op args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFrom_ordinaryOp passFuel relationFuel compiler next allowed trace op args targetArgs
    notInstall notForce (argsIH targetArgs argsRun) argsWf

/-- The fuel-bounded install traversal composes its arguments above the pass
state with a smaller-clock installed-program hypothesis. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_install_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.op trace .install args) initial = some (out, passFinal))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, passFinal) →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler passFinal allowed args target)
    (programIH : ∀ clock (middleG : State) program nextKnown converted,
      compileIncFuel? passFuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler passFinal allowed
      [.op trace .install args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at passRun
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := passRun
  intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle
  have argsEnv := envRelFuel_op_args trace .install targetArgs (by simpa using envs)
  exact evaluate_install_growing_args_from passFuel relationFuel next g requiredGrowth allowed compiler trace args targetArgs
    sourceEnv targetEnv source target result final run notType argsEnv envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle (argsIH targetArgs argsRun) (programIH source.clock)

/-- The install case uses a smaller-clock induction hypothesis and
clock-bounded argument simulation. This is Flapjack-specific infrastructure. -/
theorem callsFuel_install_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.op trace .install args) initial = some (out, passFinal))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed args target)
    (programIH : ∀ clock, clock < limit → ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? passFuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.op trace .install args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at passRun
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := passRun
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle
  have argsEnv := envRelFuel_op_args trace .install targetArgs (by simpa using envs)
  exact evaluate_install_growing_args_below passFuel relationFuel limit next g requiredGrowth allowed compiler trace args targetArgs
    sourceEnv targetEnv source target clock result final run notType argsEnv envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle (argsIH targetArgs argsRun) (programIH source.clock clock)

/-- The install case uses a smaller-clock induction hypothesis and
clock-allowing argument simulation. This is Flapjack-specific infrastructure. -/
theorem callsFuel_install_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.op trace .install args) initial = some (out, passFinal))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, passFinal) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed args target)
    (programIH : ∀ clock, clock < limit → ∀ (middleG : State) program nextKnown converted,
      compileIncFuel? passFuel middleG.1 (program, []) = some (nextKnown, converted) →
      InstalledProgramSimBelowWithClock (C := C) (F := F) passFuel relationFuel clock compiler
        (nextKnown, converted.2 ++ middleG.2) allowed program converted.1) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.op trace .install args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at passRun
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := passRun
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle
  have argsEnv := envRelFuel_op_args trace .install targetArgs (by simpa using envs)
  exact evaluate_install_growing_args_below_withClock passFuel relationFuel limit next g requiredGrowth allowed compiler trace args targetArgs
    sourceEnv targetEnv source target clock result final run notType argsEnv envWf sourceWf states ready
    sourceCompiler targetCompiler targetOracle (argsIH targetArgs argsRun) (programIH source.clock clock)

/-- Clock-bounded tick simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_tick {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.tick trace sourceBody] [.tick trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have eq : result = .err (.abort .timeoutError) ∧ final = source := by simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .err (.abort .timeoutError), target, stateExtends_refl g ready.well.2,
      by simp [evaluate, targetZero], rfl, states, sourceWf, ready, sourceCompiler, targetCompiler, oracle,
      fun _ _ h => h⟩
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp (by simpa using envs)
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv (decClock 1 source) (decClock 1 target) result final (by simp [decClock]; omega) bodyRun notType
        (by simpa [decClock] using bodyEnv) envWf (stateWellFormedFuel_clock sourceWf _)
        (stateRelFuel_decClock states 1) (incrementalInstallReady_decClock g source target 1 ready)
        (by simpa [decClock] using sourceCompiler) (by simpa [decClock] using targetCompiler)
        (by simpa [decClock] using oracle)
    refine ⟨finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    simpa [evaluate, targetNonzero] using targetRun

/-- Clock-allowing tick simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_tick {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.tick trace sourceBody] [.tick trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have eq : result = .err (.abort .timeoutError) ∧ final = source := by simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    have targetRun : evaluate [.tick trace targetBody] targetEnv target =
        (.err (.abort .timeoutError), target) := by simp [evaluate, targetZero]
    exact ⟨0, g, .err (.abort .timeoutError), target, stateExtends_refl g ready.well.2,
      by simpa using targetRun, rfl, states, sourceWf, ready, sourceCompiler, targetCompiler, oracle,
      fun _ _ h => h⟩
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp (by simpa using envs)
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨extraClock, finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv (decClock 1 source) (decClock 1 target) result final (by simp [decClock]; omega) bodyRun notType
        (by simpa [decClock] using bodyEnv) envWf (stateWellFormedFuel_clock sourceWf _)
        (stateRelFuel_decClock states 1) (incrementalInstallReady_decClock g source target 1 ready)
        (by simpa [decClock] using sourceCompiler) (by simpa [decClock] using targetCompiler)
        (by simpa [decClock] using oracle)
    refine ⟨extraClock, finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    have shiftedNonzero : target.clock + extraClock ≠ 0 := by omega
    have clocksEqual : target.clock + extraClock - 1 = target.clock - 1 + extraClock := by omega
    simpa [evaluate, decClock, targetNonzero, shiftedNonzero, clocksEqual] using targetRun

/-- Ticks preserve the open-location simulation, including timeout and an
additional target clock allowance. This is Flapjack-specific infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_tick {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required
      [.tick trace sourceBody] [.tick trace targetBody] := by
  intro g requiredGrowth allowed sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have eq : result = .err (.abort .timeoutError) ∧ final = source := by simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    have targetRun : evaluate [.tick trace targetBody] targetEnv target =
        (.err (.abort .timeoutError), target) := by simp [evaluate, targetZero]
    exact ⟨0, g, allowed, .err (.abort .timeoutError), target, stateExtends_refl g ready.well.2,
      Set.Subset.rfl, disjoint, avoids, by simpa using targetRun, rfl, states, sourceWf, ready,
      sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp (by simpa using envs)
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨extraClock, finalG, finalAllowed, targetResult, targetFinal, extended, allowedGrowth,
      finalDisjoint, finalAvoids, targetRun, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth allowed sourceEnv targetEnv (decClock 1 source) (decClock 1 target) result final
        (by simp [decClock]; omega) bodyRun notType (by simpa [decClock] using bodyEnv) envWf
        (stateWellFormedFuel_clock sourceWf _) (stateRelFuel_decClock states 1)
        (incrementalInstallReady_decClock g source target 1 ready) disjoint
        (by simpa [OracleLocationsAvoid, decClock] using avoids)
        (by simpa [decClock] using sourceCompiler) (by simpa [decClock] using targetCompiler)
        (by simpa [decClock] using oracle)
    refine ⟨extraClock, finalG, finalAllowed, targetResult, targetFinal, extended, allowedGrowth,
      finalDisjoint, finalAvoids, ?_, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    have shiftedNonzero : target.clock + extraClock ≠ 0 := by omega
    have clocksEqual : target.clock + extraClock - 1 = target.clock - 1 + extraClock := by omega
    simpa [evaluate, decClock, targetNonzero, shiftedNonzero, clocksEqual] using targetRun

/-- Clock-bounded raise simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_raise {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.raise trace sourceBody] [.raise trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp (by simpa using envs)
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe (by simpa using bodyEnv)
        envWf sourceWf states ready sourceCompiler targetCompiler oracle
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err targetError =>
        have eq : result = .err error ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        exact ⟨finalG, .err targetError, targetFinal, extended, by simp [evaluate, targetRun], related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv target targetFinal targetValues targetRun
        have eq : result = .err (.raise value) ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        have valueRel : ValueRelFuel relationFuel finalG allowed targetFinal.code value targetValue := by
          simpa [resultRel] using related
        exact ⟨finalG, .err (.raise targetValue), targetFinal, extended, by simp [evaluate, targetRun], valueRel,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Clock-allowing raise simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_raise {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.raise trace sourceBody] [.raise trace targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp (by simpa using envs)
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨extraClock, finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
      finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe (by simpa using bodyEnv)
        envWf sourceWf states ready sourceCompiler targetCompiler oracle
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err targetError =>
        have eq : result = .err error ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        exact ⟨extraClock, finalG, .err targetError, targetFinal, extended, by simp [evaluate, targetRun], related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv { target with clock := target.clock + extraClock } targetFinal targetValues targetRun
        have eq : result = .err (.raise value) ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        have valueRel : ValueRelFuel relationFuel finalG allowed targetFinal.code value targetValue := by
          simpa [resultRel] using related
        exact ⟨extraClock, finalG, .err (.raise targetValue), targetFinal, extended, by simp [evaluate, targetRun], valueRel,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Raising a related value preserves the growing open-location simulation.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_raise {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra)
    (sourceBody targetBody : ClosLang.Exp)
    (bodySim : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required
      [.raise trace sourceBody] [.raise trace targetBody] := by
  intro g requiredGrowth allowed sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  have bodyEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp (by simpa using envs)
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨extraClock, finalG, finalAllowed, targetResult, targetFinal, extended, allowedGrowth,
      finalDisjoint, finalAvoids, targetRun, related, finalStates, finalWf, finalReady,
      finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
      bodySim g requiredGrowth allowed sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready disjoint avoids sourceCompiler targetCompiler oracle
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err targetError =>
        have eq : result = .err error ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        exact ⟨extraClock, finalG, finalAllowed, .err targetError, targetFinal, extended, allowedGrowth,
          finalDisjoint, finalAvoids, by simp [evaluate, targetRun], related, finalStates, finalWf,
          finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv
          { target with clock := target.clock + extraClock } targetFinal targetValues targetRun
        have eq : result = .err (.raise value) ∧ final = bodyFinal := by simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        have valueRel : ValueRelFuel relationFuel finalG finalAllowed targetFinal.code value targetValue := by
          simpa [resultRel] using related
        exact ⟨extraClock, finalG, finalAllowed, .err (.raise targetValue), targetFinal, extended, allowedGrowth,
          finalDisjoint, finalAvoids, by simp [evaluate, targetRun], valueRel, finalStates, finalWf,
          finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- The actual variable traversal preserves the open-location simulation. -/
theorem callsFuel_var_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra) (index : Nat)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.var trace index) initial = some (out, final)) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [.var trace index] [out] := by
  simp [callsFuel] at run
  obtain ⟨rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_var passFuel relationFuel limit compiler initial trace index

/-- The actual tick traversal uses its body's open-location simulation. -/
theorem callsFuel_tick_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [body] [target]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [.tick trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_tick passFuel relationFuel limit compiler next trace body target (bodyIH target bodyRun)

/-- The actual raise traversal uses its body's open-location simulation. -/
theorem callsFuel_raise_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [body] [target]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [.raise trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_raise passFuel relationFuel limit compiler next trace body target (bodyIH target bodyRun)

/-- Clock-bounded tick traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_tick_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.tick trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_tick passFuel relationFuel limit compiler next allowed trace body target (bodyIH target bodyRun)

/-- Clock-allowing tick traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_tick_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.tick trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_tick passFuel relationFuel limit compiler next allowed trace body target (bodyIH target bodyRun)

/-- Clock-bounded raise traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_raise_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.raise trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_raise passFuel relationFuel limit compiler next allowed trace body target (bodyIH target bodyRun)

/-- Clock-allowing raise traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_raise_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel traversalFuel body initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.raise trace body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_raise passFuel relationFuel limit compiler next allowed trace body target (bodyIH target bodyRun)

/-- Clock-bounded conditional simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_if {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sc sy sn tc ty tn : ClosLang.Exp)
    (conditionIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sc] [tc])
    (yesIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sy] [ty])
    (noIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sn] [tn]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.ifThenElse trace sc sy sn] [.ifThenElse trace tc ty tn] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have ifEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .ifThenElse trace tc ty tn)] := by simpa using envs
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) ifEnv
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condSafe : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨condG, targetCondResult, targetCondFinal, condExt, targetCondRun, condRel, condStates,
      condWf, condReady, condCompiler, targetCondCompiler, condOracle, condGrowth⟩ :=
      conditionIH g requiredGrowth sourceEnv targetEnv source target condResult condFinal clock condRun condSafe
        (by simpa using conditionEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), condFinal)).2
    let targetNext := (fixClock target ((), targetCondFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel condG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 condStates
    have nextWf : StateWellFormedFuel relationFuel condG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock condWf (min source.clock condFinal.clock)
    have nextReady : IncrementalInstallReady condG sourceNext targetNext :=
      incrementalInstallReady_fixClock condG source condFinal target targetCondFinal condReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using condCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by
      simpa [targetNext, fixClock] using targetCondCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using condOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := condGrowth
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have eq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, condRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨condG, .err targetError, targetNext, condExt, ?_, condRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetCondRun, fixClock, targetNext]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv target targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel relationFuel condG allowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have eq : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact (notType eq).elim
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          have branchEnvWf := valuesWellFormedFuel_mono envWf condExt Set.Subset.rfl nextGrowth
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              noIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              yesIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Clock-allowing conditional simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_if {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sc sy sn tc ty tn : ClosLang.Exp)
    (conditionIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sc] [tc])
    (yesIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sy] [ty])
    (noIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sn] [tn]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.ifThenElse trace sc sy sn] [.ifThenElse trace tc ty tn] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have ifEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .ifThenElse trace tc ty tn)] := by simpa using envs
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) ifEnv
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condSafe : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨condExtra, condG, targetCondResult, targetCondFinal, condExt, targetCondRun, condRel, condStates,
      condWf, condReady, condCompiler, targetCondCompiler, condOracle, condGrowth⟩ :=
      conditionIH g requiredGrowth sourceEnv targetEnv source target condResult condFinal clock condRun condSafe
        (by simpa using conditionEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    have condClockBound : targetCondFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le [sc] sourceEnv source
      rw [condRun] at sourceBound
      change condFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := condStates.2.1
      change condFinal.clock = targetCondFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), condFinal)).2
    let targetNext := (fixClock target ((), targetCondFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel condG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 condStates
    have nextWf : StateWellFormedFuel relationFuel condG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock condWf (min source.clock condFinal.clock)
    have nextReady : IncrementalInstallReady condG sourceNext targetNext :=
      incrementalInstallReady_fixClock condG source condFinal target targetCondFinal condReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using condCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by
      simpa [targetNext, fixClock] using targetCondCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using condOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := condGrowth
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have eq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, condRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨condExtra, condG, .err targetError, targetNext, condExt, ?_, condRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetCondFinal.clock ≤ target.clock + condExtra := by omega
        simp [evaluate, targetCondRun, fixClock, targetNext,
          Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv { target with clock := target.clock + condExtra } targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel relationFuel condG allowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have eq : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact (notType eq).elim
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          have branchEnvWf := valuesWellFormedFuel_mono envWf condExt Set.Subset.rfl nextGrowth
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨branchExtra, finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              noIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨condExtra + branchExtra, finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedCondition := (evaluate_addClock (C := C) (F := F)).1 [tc] targetEnv
                { target with clock := target.clock + condExtra } targetCondFinal (.val [targetValue]) branchExtra
                targetCondRun (by simp)
              have shiftedCondition' : evaluate [tc] targetEnv
                  { target with clock := target.clock + (condExtra + branchExtra) } =
                  (.val [targetValue], { targetCondFinal with clock := targetCondFinal.clock + branchExtra }) := by
                simpa [Nat.add_assoc] using shiftedCondition
              have shiftedBound : targetCondFinal.clock + branchExtra ≤
                  target.clock + (condExtra + branchExtra) := by omega
              simpa [evaluate, shiftedCondition', fixClock, targetBool, targetNext,
                Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨branchExtra, finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              yesIH condG (stateExtends_trans required g condG requiredGrowth condExt) sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨condExtra + branchExtra, finalG, result, final, stateExtends_trans g condG finalG condExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedCondition := (evaluate_addClock (C := C) (F := F)).1 [tc] targetEnv
                { target with clock := target.clock + condExtra } targetCondFinal (.val [targetValue]) branchExtra
                targetCondRun (by simp)
              have shiftedCondition' : evaluate [tc] targetEnv
                  { target with clock := target.clock + (condExtra + branchExtra) } =
                  (.val [targetValue], { targetCondFinal with clock := targetCondFinal.clock + branchExtra }) := by
                simpa [Nat.add_assoc] using shiftedCondition
              have shiftedBound : targetCondFinal.clock + branchExtra ≤
                  target.clock + (condExtra + branchExtra) := by omega
              simpa [evaluate, shiftedCondition', fixClock, targetBool, targetNext,
                Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Conditional simulation with growing open locations. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_if {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra)
    (sc sy sn tc ty tn : ClosLang.Exp)
    (conditionIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sc] [tc])
    (yesIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sy] [ty])
    (noIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sn] [tn]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required
      [.ifThenElse trace sc sy sn] [.ifThenElse trace tc ty tn] := by
  intro g requiredGrowth allowed sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  have ifEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .ifThenElse trace tc ty tn)] := by simpa using envs
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) ifEnv
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condSafe : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨condExtra, condG, condAllowed, targetCondResult, targetCondFinal, condExt, condAllowedGrowth,
      condDisjoint, condAvoids, targetCondRun, condRel, condStates,
      condWf, condReady, condCompiler, targetCondCompiler, condOracle, condGrowth⟩ :=
      conditionIH g requiredGrowth allowed sourceEnv targetEnv source target condResult condFinal clock condRun condSafe
        (by simpa using conditionEnv) envWf sourceWf states ready disjoint avoids sourceCompiler targetCompiler oracle
    have condClockBound : targetCondFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le [sc] sourceEnv source
      rw [condRun] at sourceBound
      change condFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := condStates.2.1
      change condFinal.clock = targetCondFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), condFinal)).2
    let targetNext := (fixClock target ((), targetCondFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel condG condAllowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 condStates
    have nextWf : StateWellFormedFuel relationFuel condG condAllowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock condWf (min source.clock condFinal.clock)
    have nextReady : IncrementalInstallReady condG sourceNext targetNext :=
      incrementalInstallReady_fixClock condG source condFinal target targetCondFinal condReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using condCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by
      simpa [targetNext, fixClock] using targetCondCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using condOracle
    have nextAvoids : OracleLocationsAvoid condAllowed sourceNext := by
      simpa [sourceNext, fixClock, OracleLocationsAvoid] using condAvoids
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := condGrowth
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have eq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, condRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨condExtra, condG, condAllowed, .err targetError, targetNext, condExt, condAllowedGrowth,
          condDisjoint, nextAvoids, ?_, condRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetCondFinal.clock ≤ target.clock + condExtra := by omega
        simp [evaluate, targetCondRun, fixClock, targetNext,
          Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv { target with clock := target.clock + condExtra } targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel relationFuel condG condAllowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have eq : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact (notType eq).elim
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          have branchEnvWf := valuesWellFormedFuel_mono envWf condExt condAllowedGrowth nextGrowth
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt condAllowedGrowth nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨branchExtra, finalG, finalAllowed, result, final, extended, branchAllowedGrowth, finalDisjoint, finalAvoids,
              targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              noIH condG (stateExtends_trans required g condG requiredGrowth condExt) condAllowed sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady condDisjoint nextAvoids nextCompiler nextTargetCompiler nextOracle
            refine ⟨condExtra + branchExtra, finalG, finalAllowed, result, final, stateExtends_trans g condG finalG condExt extended,
              Set.Subset.trans condAllowedGrowth branchAllowedGrowth, finalDisjoint, finalAvoids, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedCondition := (evaluate_addClock (C := C) (F := F)).1 [tc] targetEnv
                { target with clock := target.clock + condExtra } targetCondFinal (.val [targetValue]) branchExtra
                targetCondRun (by simp)
              have shiftedCondition' : evaluate [tc] targetEnv
                  { target with clock := target.clock + (condExtra + branchExtra) } =
                  (.val [targetValue], { targetCondFinal with clock := targetCondFinal.clock + branchExtra }) := by
                simpa [Nat.add_assoc] using shiftedCondition
              have shiftedBound : targetCondFinal.clock + branchExtra ≤
                  target.clock + (condExtra + branchExtra) := by omega
              simpa [evaluate, shiftedCondition', fixClock, targetBool, targetNext,
                Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) ifEnv
            have branchEnv' := envRelFuel_mono branchEnv condExt condAllowedGrowth nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨branchExtra, finalG, finalAllowed, result, final, extended, branchAllowedGrowth, finalDisjoint, finalAvoids,
              targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              yesIH condG (stateExtends_trans required g condG requiredGrowth condExt) condAllowed sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal nextClock branchRun notType
                (by simpa using branchEnv') branchEnvWf nextWf nextStates nextReady condDisjoint nextAvoids nextCompiler nextTargetCompiler nextOracle
            refine ⟨condExtra + branchExtra, finalG, finalAllowed, result, final, stateExtends_trans g condG finalG condExt extended,
              Set.Subset.trans condAllowedGrowth branchAllowedGrowth, finalDisjoint, finalAvoids, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedCondition := (evaluate_addClock (C := C) (F := F)).1 [tc] targetEnv
                { target with clock := target.clock + condExtra } targetCondFinal (.val [targetValue]) branchExtra
                targetCondRun (by simp)
              have shiftedCondition' : evaluate [tc] targetEnv
                  { target with clock := target.clock + (condExtra + branchExtra) } =
                  (.val [targetValue], { targetCondFinal with clock := targetCondFinal.clock + branchExtra }) := by
                simpa [Nat.add_assoc] using shiftedCondition
              have shiftedBound : targetCondFinal.clock + branchExtra ≤
                  target.clock + (condExtra + branchExtra) := by omega
              simpa [evaluate, shiftedCondition', fixClock, targetBool, targetNext,
                Nat.min_eq_right condClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Clock-bounded conditional traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_if_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (conditionIH : ∀ target middle, callsFuel traversalFuel condition initial = some (target, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [condition] [target])
    (yesIH : ∀ target before after, callsFuel traversalFuel yes before = some (target, after) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [yes] [target])
    (noIH : ∀ target middle, callsFuel traversalFuel no middle = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [no] [target]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed
      [.ifThenElse trace condition yes no] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_if passFuel relationFuel limit compiler next allowed trace condition yes no
    targetCondition targetYes targetNo (conditionIH targetCondition middle1 conditionRun)
    (yesIH targetYes middle1 middle2 yesRun) (noIH targetNo middle2 noRun)

/-- Clock-allowing conditional traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_if_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (conditionIH : ∀ target middle, callsFuel traversalFuel condition initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [condition] [target])
    (yesIH : ∀ target before after, callsFuel traversalFuel yes before = some (target, after) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [yes] [target])
    (noIH : ∀ target middle, callsFuel traversalFuel no middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [no] [target]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [.ifThenElse trace condition yes no] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_if passFuel relationFuel limit compiler next allowed trace condition yes no
    targetCondition targetYes targetNo (conditionIH targetCondition middle1 conditionRun)
    (yesIH targetYes middle1 middle2 yesRun) (noIH targetNo middle2 noRun)

/-- The conditional traversal composes its three open-location simulations.
This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_if_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (conditionIH : ∀ target middle, callsFuel traversalFuel condition initial = some (target, middle) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [condition] [target])
    (yesIH : ∀ target before after, callsFuel traversalFuel yes before = some (target, after) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [yes] [target])
    (noIH : ∀ target middle, callsFuel traversalFuel no middle = some (target, final) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [no] [target]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final
      [.ifThenElse trace condition yes no] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_if passFuel relationFuel limit compiler next trace condition yes no
    targetCondition targetYes targetNo (conditionIH targetCondition middle1 conditionRun)
    (yesIH targetYes middle1 middle2 yesRun) (noIH targetNo middle2 noRun)

/-- Adding a target allowance before and after an intermediate computation
commutes with restoring its clock, when that computation did not increase the
original clock. This is Flapjack-specific simulation infrastructure. -/
theorem fixClock_allowance {C F : Type} (start last : ClosSem.State C F)
    (before after : Nat) (bound : last.clock ≤ start.clock) :
    (fixClock { start with clock := start.clock + (before + after) }
      ((), { last with clock := last.clock + after })).2 =
      { (fixClock start ((), last)).2 with
        clock := (fixClock start ((), last)).2.clock + after } := by
  have shiftedBound : last.clock + after ≤ start.clock + (before + after) := by omega
  simp [fixClock, Nat.min_eq_right bound, Nat.min_eq_right shiftedBound]

/-- Clock-bounded let simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_let {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBindings targetBindings : List ClosLang.Exp) (sourceBody targetBody : ClosLang.Exp)
    (bindingsIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceBindings targetBindings)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.let trace sourceBindings sourceBody] [.let trace targetBindings targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have letEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .let trace targetBindings targetBody)] := by simpa using envs
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody letEnv
  have bindingWf := bindingsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingSafe : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bindingG, targetBindingResult, targetBindingFinal, bindingExt, targetBindingRun, bindingRel,
      bindingStates, bindingStateWf, bindingReady, bindingCompiler, targetBindingCompiler, bindingOracle, bindingGrowth⟩ :=
      bindingsIH g requiredGrowth sourceEnv targetEnv source target bindingResult bindingFinal clock bindingRun bindingSafe
        bindingsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bindingG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextWf : StateWellFormedFuel relationFuel bindingG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bindingStateWf (min source.clock bindingFinal.clock)
    have nextReady : IncrementalInstallReady bindingG sourceNext targetNext :=
      incrementalInstallReady_fixClock bindingG source bindingFinal target targetBindingFinal bindingReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bindingCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBindingCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bindingOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have eq : result = .err error ∧ final = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bindingG, .err targetError, targetNext, bindingExt, ?_, bindingRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBindingRun, fixClock, targetNext]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel bindingG allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv target
            targetBindingFinal targetValues targetBindingRun
          exact valuesRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody letEnv
        have outerEnv' := envRelFuel_mono outerEnv bindingExt Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valuesRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf) bindingExt Set.Subset.rfl nextGrowth
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (result, final) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          bodyIH bindingG (stateExtends_trans required g bindingG requiredGrowth bindingExt) (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) sourceNext targetNext result final nextClock
            bodyRun notType (by simpa using bodyEnv) bodyEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
        refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g bindingG finalG bindingExt extended, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · simpa [evaluate, targetBindingRun, fixClock, targetNext] using targetRun
        · intro key entry found
          exact growth key entry (nextGrowth key entry found)

/-- Clock-allowing let simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_let {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceBindings targetBindings : List ClosLang.Exp) (sourceBody targetBody : ClosLang.Exp)
    (bindingsIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceBindings targetBindings)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.let trace sourceBindings sourceBody] [.let trace targetBindings targetBody] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have letEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .let trace targetBindings targetBody)] := by simpa using envs
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody letEnv
  have bindingWf := bindingsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingSafe : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bindingExtra, bindingG, targetBindingResult, targetBindingFinal, bindingExt, targetBindingRun, bindingRel,
      bindingStates, bindingStateWf, bindingReady, bindingCompiler, targetBindingCompiler, bindingOracle, bindingGrowth⟩ :=
      bindingsIH g requiredGrowth sourceEnv targetEnv source target bindingResult bindingFinal clock bindingRun bindingSafe
        bindingsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
    have bindingClockBound : targetBindingFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le sourceBindings sourceEnv source
      rw [bindingRun] at sourceBound
      change bindingFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := bindingStates.2.1
      change bindingFinal.clock = targetBindingFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bindingG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextWf : StateWellFormedFuel relationFuel bindingG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bindingStateWf (min source.clock bindingFinal.clock)
    have nextReady : IncrementalInstallReady bindingG sourceNext targetNext :=
      incrementalInstallReady_fixClock bindingG source bindingFinal target targetBindingFinal bindingReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bindingCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBindingCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bindingOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have eq : result = .err error ∧ final = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bindingExtra, bindingG, .err targetError, targetNext, bindingExt, ?_, bindingRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetBindingFinal.clock ≤ target.clock + bindingExtra := by omega
        simp [evaluate, targetBindingRun, fixClock, targetNext,
          Nat.min_eq_right bindingClockBound, Nat.min_eq_right shiftedBound]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel bindingG allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv { target with clock := target.clock + bindingExtra }
            targetBindingFinal targetValues targetBindingRun
          exact valuesRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody letEnv
        have outerEnv' := envRelFuel_mono outerEnv bindingExt Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valuesRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel relationFuel bindingG allowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf) bindingExt Set.Subset.rfl nextGrowth
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (result, final) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨bodyExtra, finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          bodyIH bindingG (stateExtends_trans required g bindingG requiredGrowth bindingExt) (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) sourceNext targetNext result final nextClock
            bodyRun notType (by simpa using bodyEnv) bodyEnvWf nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
        refine ⟨bindingExtra + bodyExtra, finalG, targetResult, targetFinal, stateExtends_trans g bindingG finalG bindingExt extended, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · have shiftedBindings := (evaluate_addClock (C := C) (F := F)).1 targetBindings targetEnv
            { target with clock := target.clock + bindingExtra } targetBindingFinal (.val targetValues) bodyExtra
            targetBindingRun (by simp)
          have shiftedBindings' : evaluate targetBindings targetEnv
              { target with clock := target.clock + (bindingExtra + bodyExtra) } =
              (.val targetValues, { targetBindingFinal with clock := targetBindingFinal.clock + bodyExtra }) := by
            simpa [Nat.add_assoc] using shiftedBindings
          have shiftedBound : targetBindingFinal.clock + bodyExtra ≤
              target.clock + (bindingExtra + bodyExtra) := by omega
          simpa [evaluate, shiftedBindings', targetNext, fixClock,
            Nat.min_eq_right bindingClockBound, Nat.min_eq_right shiftedBound] using targetRun
        · intro key entry found
          exact growth key entry (nextGrowth key entry found)

/-- Let simulation with growing open locations. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_let {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra)
    (sourceBindings targetBindings : List ClosLang.Exp) (sourceBody targetBody : ClosLang.Exp)
    (bindingsIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required sourceBindings targetBindings)
    (bindingsWf : ∀ (allowed : Set Nat) (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sourceBody] [targetBody]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required
      [.let trace sourceBindings sourceBody] [.let trace targetBindings targetBody] := by
  intro g requiredGrowth allowed sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  have letEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .let trace targetBindings targetBody)] := by simpa using envs
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody letEnv
  have bindingWf := bindingsWf allowed g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingSafe : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have eq : result = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bindingExtra, bindingG, bindingAllowed, targetBindingResult, targetBindingFinal, bindingExt, bindingAllowedGrowth,
      bindingDisjoint, bindingAvoids, targetBindingRun, bindingRel,
      bindingStates, bindingStateWf, bindingReady, bindingCompiler, targetBindingCompiler, bindingOracle, bindingGrowth⟩ :=
      bindingsIH g requiredGrowth allowed sourceEnv targetEnv source target bindingResult bindingFinal clock bindingRun bindingSafe
        bindingsEnv envWf sourceWf states ready disjoint avoids sourceCompiler targetCompiler oracle
    have bindingClockBound : targetBindingFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le sourceBindings sourceEnv source
      rw [bindingRun] at sourceBound
      change bindingFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := bindingStates.2.1
      change bindingFinal.clock = targetBindingFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bindingG bindingAllowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextWf : StateWellFormedFuel relationFuel bindingG bindingAllowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bindingStateWf (min source.clock bindingFinal.clock)
    have nextReady : IncrementalInstallReady bindingG sourceNext targetNext :=
      incrementalInstallReady_fixClock bindingG source bindingFinal target targetBindingFinal bindingReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bindingCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBindingCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bindingOracle
    have nextAvoids : OracleLocationsAvoid bindingAllowed sourceNext := by
      simpa [sourceNext, fixClock, OracleLocationsAvoid] using bindingAvoids
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have eq : result = .err error ∧ final = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bindingExtra, bindingG, bindingAllowed, .err targetError, targetNext, bindingExt, bindingAllowedGrowth,
          bindingDisjoint, nextAvoids, ?_, bindingRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetBindingFinal.clock ≤ target.clock + bindingExtra := by omega
        simp [evaluate, targetBindingRun, fixClock, targetNext,
          Nat.min_eq_right bindingClockBound, Nat.min_eq_right shiftedBound]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel bindingG bindingAllowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv { target with clock := target.clock + bindingExtra }
            targetBindingFinal targetValues targetBindingRun
          exact valuesRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody letEnv
        have outerEnv' := envRelFuel_mono outerEnv bindingExt bindingAllowedGrowth nextGrowth
        have bodyEnv : EnvRelFuel relationFuel bindingG bindingAllowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valuesRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel relationFuel bindingG bindingAllowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf) bindingExt bindingAllowedGrowth nextGrowth
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (result, final) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨bodyExtra, finalG, finalAllowed, targetResult, targetFinal, extended, bodyAllowedGrowth, finalDisjoint, finalAvoids,
          targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          bodyIH bindingG (stateExtends_trans required g bindingG requiredGrowth bindingExt) bindingAllowed (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) sourceNext targetNext result final nextClock
            bodyRun notType (by simpa using bodyEnv) bodyEnvWf nextWf nextStates nextReady bindingDisjoint nextAvoids nextCompiler nextTargetCompiler nextOracle
        refine ⟨bindingExtra + bodyExtra, finalG, finalAllowed, targetResult, targetFinal, stateExtends_trans g bindingG finalG bindingExt extended,
          Set.Subset.trans bindingAllowedGrowth bodyAllowedGrowth, finalDisjoint, finalAvoids, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · have shiftedBindings := (evaluate_addClock (C := C) (F := F)).1 targetBindings targetEnv
            { target with clock := target.clock + bindingExtra } targetBindingFinal (.val targetValues) bodyExtra
            targetBindingRun (by simp)
          have shiftedBindings' : evaluate targetBindings targetEnv
              { target with clock := target.clock + (bindingExtra + bodyExtra) } =
              (.val targetValues, { targetBindingFinal with clock := targetBindingFinal.clock + bodyExtra }) := by
            simpa [Nat.add_assoc] using shiftedBindings
          have shiftedBound : targetBindingFinal.clock + bodyExtra ≤
              target.clock + (bindingExtra + bodyExtra) := by omega
          simpa [evaluate, shiftedBindings', targetNext, fixClock,
            Nat.min_eq_right bindingClockBound, Nat.min_eq_right shiftedBound] using targetRun
        · intro key entry found
          exact growth key entry (nextGrowth key entry found)

/-- Clock-bounded handle simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_handle {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sb sh tb th : ClosLang.Exp)
    (bodyIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sb] [tb])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sb] env state))
    (handlerIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sh] [th]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [.handle trace sb sh] [.handle trace tb th] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have handleEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .handle trace tb th)] := by simpa using envs
  have bodyEnv := envRelFuel_handle_body trace tb th handleEnv
  have sourceBodyWf := bodyWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at sourceBodyWf
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
      bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
      bodyIH g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bodyG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextWf : StateWellFormedFuel relationFuel bodyG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bodyStateWf (min source.clock bodyFinal.clock)
    have nextReady : IncrementalInstallReady bodyG sourceNext targetNext :=
      incrementalInstallReady_fixClock bodyG source bodyFinal target targetBodyFinal bodyReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bodyCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBodyCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bodyOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have eq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bodyG, .val targetValues, targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        simp [evaluate, targetBodyRun, fixClock, targetNext]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have eq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨bodyG, .err (.abort targetAbort), targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
              nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
            simp [evaluate, targetBodyRun, fixClock, targetNext]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel relationFuel bodyG allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv := envRelFuel_mono handleEnv bodyExt Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have payloadWf : ValueWellFormedFuel relationFuel bodyG allowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 bodyExt Set.Subset.rfl nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf bodyExt Set.Subset.rfl nextGrowth
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              handlerIH bodyG (stateExtends_trans required g bodyG requiredGrowth bodyExt) (sourceValue :: sourceEnv) (targetValue :: targetEnv) sourceNext targetNext
                sourceResult sourceFinal nextClock handlerRun notType (by simpa using handlerEnv) (.cons payloadWf outerWf)
                nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨finalG, result, final, stateExtends_trans g bodyG finalG bodyExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [evaluate, targetBodyRun, fixClock, targetNext] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Clock-allowing handle simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_handle {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sb sh tb th : ClosLang.Exp)
    (bodyIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sb] [tb])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sb] env state))
    (handlerIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sh] [th]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [.handle trace sb sh] [.handle trace tb th] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have handleEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .handle trace tb th)] := by simpa using envs
  have bodyEnv := envRelFuel_handle_body trace tb th handleEnv
  have sourceBodyWf := bodyWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at sourceBodyWf
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bodyExtra, bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
      bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
      bodyIH g requiredGrowth sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready sourceCompiler targetCompiler oracle
    have bodyClockBound : targetBodyFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le [sb] sourceEnv source
      rw [bodyRun] at sourceBound
      change bodyFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := bodyStates.2.1
      change bodyFinal.clock = targetBodyFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bodyG allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextWf : StateWellFormedFuel relationFuel bodyG allowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bodyStateWf (min source.clock bodyFinal.clock)
    have nextReady : IncrementalInstallReady bodyG sourceNext targetNext :=
      incrementalInstallReady_fixClock bodyG source bodyFinal target targetBodyFinal bodyReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bodyCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBodyCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bodyOracle
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have eq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bodyExtra, bodyG, .val targetValues, targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetBodyFinal.clock ≤ target.clock + bodyExtra := by omega
        simp [evaluate, targetBodyRun, fixClock, targetNext,
          Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have eq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨bodyExtra, bodyG, .err (.abort targetAbort), targetNext, bodyExt, ?_, bodyRel, nextStates, nextWf, nextReady,
              nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
            have shiftedBound : targetBodyFinal.clock ≤ target.clock + bodyExtra := by omega
            simp [evaluate, targetBodyRun, fixClock, targetNext,
              Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel relationFuel bodyG allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv := envRelFuel_mono handleEnv bodyExt Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have payloadWf : ValueWellFormedFuel relationFuel bodyG allowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 bodyExt Set.Subset.rfl nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf bodyExt Set.Subset.rfl nextGrowth
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨handlerExtra, finalG, result, final, extended, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              handlerIH bodyG (stateExtends_trans required g bodyG requiredGrowth bodyExt) (sourceValue :: sourceEnv) (targetValue :: targetEnv) sourceNext targetNext
                sourceResult sourceFinal nextClock handlerRun notType (by simpa using handlerEnv) (.cons payloadWf outerWf)
                nextWf nextStates nextReady nextCompiler nextTargetCompiler nextOracle
            refine ⟨bodyExtra + handlerExtra, finalG, result, final, stateExtends_trans g bodyG finalG bodyExt extended, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedBody := (evaluate_addClock (C := C) (F := F)).1 [tb] targetEnv
                { target with clock := target.clock + bodyExtra } targetBodyFinal (.err (.raise targetValue)) handlerExtra
                targetBodyRun (by simp)
              have shiftedBody' : evaluate [tb] targetEnv
                  { target with clock := target.clock + (bodyExtra + handlerExtra) } =
                  (.err (.raise targetValue), { targetBodyFinal with clock := targetBodyFinal.clock + handlerExtra }) := by
                simpa [Nat.add_assoc] using shiftedBody
              have shiftedBound : targetBodyFinal.clock + handlerExtra ≤
                  target.clock + (bodyExtra + handlerExtra) := by omega
              simpa [evaluate, shiftedBody', fixClock, targetNext,
                Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Exception-handler simulation with growing open locations. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithOpenClock_handle {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (trace : BackendCommon.Tra)
    (sb sh tb th : ClosLang.Exp)
    (bodyIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sb] [tb])
    (bodyWf : ∀ (allowed : Set Nat) (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sb] env state))
    (handlerIH : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [sh] [th]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [.handle trace sb sh] [.handle trace tb th] := by
  intro g requiredGrowth allowed sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    disjoint avoids sourceCompiler targetCompiler oracle
  have handleEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .handle trace tb th)] := by simpa using envs
  have bodyEnv := envRelFuel_handle_body trace tb th handleEnv
  have sourceBodyWf := bodyWf allowed g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at sourceBodyWf
    have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have eq : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨bodyExtra, bodyG, bodyAllowed, targetBodyResult, targetBodyFinal, bodyExt, bodyAllowedGrowth,
      bodyDisjoint, bodyAvoids, targetBodyRun, bodyRel, bodyStates,
      bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
      bodyIH g requiredGrowth allowed sourceEnv targetEnv source target bodyResult bodyFinal clock bodyRun bodySafe
        (by simpa using bodyEnv) envWf sourceWf states ready disjoint avoids sourceCompiler targetCompiler oracle
    have bodyClockBound : targetBodyFinal.clock ≤ target.clock := by
      have sourceBound := evaluate_clock_le [sb] sourceEnv source
      rw [bodyRun] at sourceBound
      change bodyFinal.clock ≤ source.clock at sourceBound
      have originalClocks := states.2.1
      have finalClocks := bodyStates.2.1
      change bodyFinal.clock = targetBodyFinal.clock at finalClocks
      change source.clock = target.clock at originalClocks
      omega
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextClock : sourceNext.clock < limit := by
      simp only [sourceNext, fixClock]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) clock
    have nextStates : StateRelFuel relationFuel bodyG bodyAllowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextWf : StateWellFormedFuel relationFuel bodyG bodyAllowed targetNext.code sourceNext := by
      simpa [sourceNext, targetNext, fixClock] using
        stateWellFormedFuel_clock bodyStateWf (min source.clock bodyFinal.clock)
    have nextReady : IncrementalInstallReady bodyG sourceNext targetNext :=
      incrementalInstallReady_fixClock bodyG source bodyFinal target targetBodyFinal bodyReady
    have nextCompiler : sourceNext.compile = compileIncFuelCallback passFuel compiler := by
      simpa [sourceNext, fixClock] using bodyCompiler
    have nextTargetCompiler : targetNext.compile = compiler := by simpa [targetNext, fixClock] using targetBodyCompiler
    have nextOracle : targetNext.compileOracle = compileIncFuelOracle passFuel sourceNext.compileOracle := by
      simpa [sourceNext, targetNext, fixClock] using bodyOracle
    have nextAvoids : OracleLocationsAvoid bodyAllowed sourceNext := by
      simpa [sourceNext, fixClock, OracleLocationsAvoid] using bodyAvoids
    have nextGrowth : ∀ key entry, target.code.lookup key = some entry → targetNext.code.lookup key = some entry := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have eq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨bodyExtra, bodyG, bodyAllowed, .val targetValues, targetNext, bodyExt, bodyAllowedGrowth,
          bodyDisjoint, nextAvoids, ?_, bodyRel, nextStates, nextWf, nextReady,
          nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
        have shiftedBound : targetBodyFinal.clock ≤ target.clock + bodyExtra := by omega
        simp [evaluate, targetBodyRun, fixClock, targetNext,
          Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have eq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := eq
            refine ⟨bodyExtra, bodyG, bodyAllowed, .err (.abort targetAbort), targetNext, bodyExt, bodyAllowedGrowth,
              bodyDisjoint, nextAvoids, ?_, bodyRel, nextStates, nextWf, nextReady,
              nextCompiler, nextTargetCompiler, nextOracle, nextGrowth⟩
            have shiftedBound : targetBodyFinal.clock ≤ target.clock + bodyExtra := by omega
            simp [evaluate, targetBodyRun, fixClock, targetNext,
              Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel relationFuel bodyG bodyAllowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv := envRelFuel_mono handleEnv bodyExt bodyAllowedGrowth nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have payloadWf : ValueWellFormedFuel relationFuel bodyG bodyAllowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 bodyExt bodyAllowedGrowth nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf bodyExt bodyAllowedGrowth nextGrowth
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨handlerExtra, finalG, finalAllowed, result, final, extended, handlerAllowedGrowth, finalDisjoint, finalAvoids,
              targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              handlerIH bodyG (stateExtends_trans required g bodyG requiredGrowth bodyExt) bodyAllowed (sourceValue :: sourceEnv) (targetValue :: targetEnv) sourceNext targetNext
                sourceResult sourceFinal nextClock handlerRun notType (by simpa using handlerEnv) (.cons payloadWf outerWf)
                nextWf nextStates nextReady bodyDisjoint nextAvoids nextCompiler nextTargetCompiler nextOracle
            refine ⟨bodyExtra + handlerExtra, finalG, finalAllowed, result, final, stateExtends_trans g bodyG finalG bodyExt extended,
              Set.Subset.trans bodyAllowedGrowth handlerAllowedGrowth, finalDisjoint, finalAvoids, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · have shiftedBody := (evaluate_addClock (C := C) (F := F)).1 [tb] targetEnv
                { target with clock := target.clock + bodyExtra } targetBodyFinal (.err (.raise targetValue)) handlerExtra
                targetBodyRun (by simp)
              have shiftedBody' : evaluate [tb] targetEnv
                  { target with clock := target.clock + (bodyExtra + handlerExtra) } =
                  (.err (.raise targetValue), { targetBodyFinal with clock := targetBodyFinal.clock + handlerExtra }) := by
                simpa [Nat.add_assoc] using shiftedBody
              have shiftedBound : targetBodyFinal.clock + handlerExtra ≤
                  target.clock + (bodyExtra + handlerExtra) := by omega
              simpa [evaluate, shiftedBody', fixClock, targetNext,
                Nat.min_eq_right bodyClockBound, Nat.min_eq_right shiftedBound] using targetRun
            · intro key entry found
              exact growth key entry (nextGrowth key entry found)

/-- Clock-bounded ordinary-operation simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_ordinaryOp {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (sourceArgs targetArgs : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsSim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.op trace op sourceArgs] [.op trace op targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace op targetArgs (by simpa using envs)
  have sourceArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  rw [evaluate_ordinaryOp_eq trace op sourceArgs sourceEnv source notInstall notForce] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    rw [argsRun] at sourceArgsWf
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsSim g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRel
        have valuesWf : ValuesWellFormedFuel relationFuel argsG allowed targetArgsFinal.code sourceValues := by
          apply valuesWellFormedFuel_mono _ argsExt Set.Subset.rfl argsGrowth
          exact sourceArgsWf.1
        have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp
          (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
          (fun (s : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F) =>
            t.code = targetArgsFinal.code ∧ StateRelFuel relationFuel argsG allowed s t)
          argsFinal targetArgsFinal sourceValues.reverse targetValues.reverse op
          ⟨valueRelFuel_simple relationFuel argsG allowed targetArgsFinal.code,
            stateRelFuel_simple relationFuel argsG allowed targetArgsFinal.code⟩ ⟨⟨rfl, argsStates⟩, valuesRel⟩
        have primWf := doApp_result_wellFormedFuel op sourceValues.reverse argsFinal argsStateWf
          (valuesWellFormedFuel_reverse valuesWf)
        cases primRun : doApp op sourceValues.reverse argsFinal with
        | err error =>
          simp only [primRun] at sim
          obtain ⟨targetError, targetPrim, errors⟩ := sim
          have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, errors, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
        | val pair =>
          obtain ⟨value, sourceFinal⟩ := pair
          simp only [primRun] at sim primWf
          obtain ⟨targetValue, targetFinal, valueRel, ⟨codeEq, finalStates⟩, targetPrim⟩ := sim
          have eq : result = .val [value] ∧ final = sourceFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          have finalReady := incrementalInstallReady_doApp argsG argsFinal targetArgsFinal final targetFinal
            sourceValues.reverse targetValues.reverse value targetValue op argsReady primRun targetPrim
          have srcFields := ClosInterp.doApp_compilerFields op sourceValues.reverse argsFinal final value primRun
          have tgtFields := ClosInterp.doApp_compilerFields op targetValues.reverse targetArgsFinal targetFinal targetValue targetPrim
          refine ⟨argsG, .val [targetValue], targetFinal, argsExt, ?_, ?_, ?_, ?_, finalReady, ?_, ?_, ?_, ?_⟩
          · simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
          · change List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetFinal.code) [value] [targetValue]
            rw [codeEq]
            exact .cons valueRel .nil
          · simpa [codeEq] using finalStates
          · simpa [codeEq, PrimitiveResultWellFormedFuel] using primWf.2
          · exact srcFields.1.trans argsCompiler
          · exact tgtFields.1.trans targetArgsCompiler
          · rw [tgtFields.2.1, srcFields.2.1]
            exact argsOracle
          · intro key entry found
            rw [codeEq]
            exact argsGrowth key entry found

/-- Clock-allowing ordinary-operation simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_ordinaryOp {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (sourceArgs targetArgs : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsSim : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.op trace op sourceArgs] [.op trace op targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace op targetArgs (by simpa using envs)
  have sourceArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  rw [evaluate_ordinaryOp_eq trace op sourceArgs sourceEnv source notInstall notForce] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    rw [argsRun] at sourceArgsWf
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨extraClock, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsSim g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨extraClock, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv { target with clock := target.clock + extraClock } notInstall notForce, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRel
        have valuesWf : ValuesWellFormedFuel relationFuel argsG allowed targetArgsFinal.code sourceValues := by
          apply valuesWellFormedFuel_mono _ argsExt Set.Subset.rfl argsGrowth
          exact sourceArgsWf.1
        have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp
          (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code)
          (fun (s : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F) =>
            t.code = targetArgsFinal.code ∧ StateRelFuel relationFuel argsG allowed s t)
          argsFinal targetArgsFinal sourceValues.reverse targetValues.reverse op
          ⟨valueRelFuel_simple relationFuel argsG allowed targetArgsFinal.code,
            stateRelFuel_simple relationFuel argsG allowed targetArgsFinal.code⟩ ⟨⟨rfl, argsStates⟩, valuesRel⟩
        have primWf := doApp_result_wellFormedFuel op sourceValues.reverse argsFinal argsStateWf
          (valuesWellFormedFuel_reverse valuesWf)
        cases primRun : doApp op sourceValues.reverse argsFinal with
        | err error =>
          simp only [primRun] at sim
          obtain ⟨targetError, targetPrim, errors⟩ := sim
          have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨extraClock, argsG, .err targetError, targetArgsFinal, argsExt, ?_, errors, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv { target with clock := target.clock + extraClock } notInstall notForce, targetArgsRun, targetPrim]
        | val pair =>
          obtain ⟨value, sourceFinal⟩ := pair
          simp only [primRun] at sim primWf
          obtain ⟨targetValue, targetFinal, valueRel, ⟨codeEq, finalStates⟩, targetPrim⟩ := sim
          have eq : result = .val [value] ∧ final = sourceFinal := by simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          have finalReady := incrementalInstallReady_doApp argsG argsFinal targetArgsFinal final targetFinal
            sourceValues.reverse targetValues.reverse value targetValue op argsReady primRun targetPrim
          have srcFields := ClosInterp.doApp_compilerFields op sourceValues.reverse argsFinal final value primRun
          have tgtFields := ClosInterp.doApp_compilerFields op targetValues.reverse targetArgsFinal targetFinal targetValue targetPrim
          refine ⟨extraClock, argsG, .val [targetValue], targetFinal, argsExt, ?_, ?_, ?_, ?_, finalReady, ?_, ?_, ?_, ?_⟩
          · simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv { target with clock := target.clock + extraClock } notInstall notForce, targetArgsRun, targetPrim]
          · change List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetFinal.code) [value] [targetValue]
            rw [codeEq]
            exact .cons valueRel .nil
          · simpa [codeEq] using finalStates
          · simpa [codeEq, PrimitiveResultWellFormedFuel] using primWf.2
          · exact srcFields.1.trans argsCompiler
          · exact tgtFields.1.trans targetArgsCompiler
          · rw [tgtFields.2.1, srcFields.2.1]
            exact argsOracle
          · intro key entry found
            rw [codeEq]
            exact argsGrowth key entry found

/-- Clock-bounded let traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_let_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.let trace bindings body) initial = some (out, final))
    (bindingsIH : ∀ target middle, callsListFuel traversalFuel bindings initial = some (target, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed bindings target)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body middle = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.let trace bindings body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_let passFuel relationFuel limit compiler next allowed trace bindings targetBindings body targetBody
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

/-- Clock-allowing let traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_let_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.let trace bindings body) initial = some (out, final))
    (bindingsIH : ∀ target middle, callsListFuel traversalFuel bindings initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed bindings target)
    (bindingsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [body] [target]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.let trace bindings body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_let passFuel relationFuel limit compiler next allowed trace bindings targetBindings body targetBody
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

/-- The let traversal composes its binding and body simulations with a growing
open set. The binding well-formedness premise remains explicit. -/
theorem callsFuel_let_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.let trace bindings body) initial = some (out, final))
    (bindingsIH : ∀ target middle, callsListFuel traversalFuel bindings initial = some (target, middle) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final bindings target)
    (bindingsWf : ∀ (allowed : Set Nat) (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body middle = some (target, final) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [body] [target]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [.let trace bindings body] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_let passFuel relationFuel limit compiler next trace bindings targetBindings body targetBody
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

/-- Clock-bounded handle traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_handle_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.handle trace body handler) initial = some (out, final))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body initial = some (target, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [body] [target])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel traversalFuel handler middle = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [handler] [target]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.handle trace body handler] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_handle passFuel relationFuel limit compiler next allowed trace body handler targetBody targetHandler
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- Clock-allowing handle traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_handle_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.handle trace body handler) initial = some (out, final))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [body] [target])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel traversalFuel handler middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [handler] [target]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.handle trace body handler] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_handle passFuel relationFuel limit compiler next allowed trace body handler targetBody targetHandler
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- The handler traversal composes its body and handler with growing open
locations. The body well-formedness premise remains explicit. -/
theorem callsFuel_handle_growing_below_withOpenClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.handle trace body handler) initial = some (out, final))
    (bodyIH : ∀ target middle, callsFuel traversalFuel body initial = some (target, middle) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [body] [target])
    (bodyWf : ∀ (allowed : Set Nat) (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel traversalFuel handler middle = some (target, final) →
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [handler] [target]) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler final [.handle trace body handler] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithOpenClock_handle passFuel relationFuel limit compiler next trace body handler targetBody targetHandler
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- Clock-bounded ordinaryOp traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_ordinaryOp_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace op args) initial = some (out, final))
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed args target)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate args env state)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.op trace op args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_ordinaryOp passFuel relationFuel limit compiler next allowed trace op args targetArgs
    notInstall notForce (argsIH targetArgs argsRun) argsWf

/-- Clock-allowing ordinaryOp traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_ordinaryOp_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace op args) initial = some (out, final))
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed args target)
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env →
      StateWellFormedFuel relationFuel g allowed code state → OracleAuxEmpty state.compileOracle →
      EvalWellFormedFuel relationFuel g allowed code (evaluate args env state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.op trace op args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_ordinaryOp passFuel relationFuel limit compiler next allowed trace op args targetArgs
    notInstall notForce (argsIH targetArgs argsRun) argsWf

/-- Clock-bounded thunk forcing preserves the pass-state requirement.
This is Flapjack-specific simulation infrastructure. -/
theorem runForced_growing_below {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required g : State) (requiredGrowth : stateExtends required g) (allowed : Set Nat)
    (sourceValues targetValues : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (clock : source.clock < limit) (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : ClosMti.runForced sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (forceIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ ClosMti.runForced targetValues target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have inspected := destThunk_relatedFuel states values
  cases sourceDest : destThunk sourceValues source.refs with
  | badRef =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | notThunk =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | isThunk mode sourceValue =>
    rw [sourceDest] at inspected
    cases targetDest : destThunk targetValues target.refs with
    | badRef => rw [targetDest] at inspected; cases inspected
    | notThunk => rw [targetDest] at inspected; cases inspected
    | isThunk targetMode targetValue =>
      rw [targetDest] at inspected
      cases inspected with
      | isThunk _ _ _ payloadRel =>
        cases mode with
        | evaluated =>
          have eq : result = .val [sourceValue] ∧ final = source := by
            simpa [ClosMti.runForced, sourceDest] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨g, .val [targetValue], target, stateExtends_refl g ready.well.2,
            by simp [ClosMti.runForced, targetDest], .cons payloadRel .nil, states, sourceWf, ready,
            sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        | notEvaluated =>
          have payloadWf := destThunk_wellFormedFuel sourceValues source .notEvaluated sourceValue sourceWf sourceDest
          have forceEnv : EnvRelFuel relationFuel g allowed target.code [sourceValue] [targetValue] 0
              [(0, appUnit (.var .none 0))] := .equalLength rfl (.cons payloadRel .nil)
          have forcedWf := forceWf g target.code sourceValue source payloadWf sourceWf ready.auxEmpty
          cases forceRun : evaluate [appUnit (.var .none 0)] [sourceValue] source with
          | mk forceResult forceFinal =>
            rw [forceRun] at forcedWf
            have forceSafe : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              subst forceResult
              have eq : result = .err (.abort .typeError) := by
                simpa [ClosMti.runForced, sourceDest, forceRun] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨forceG, targetForceResult, targetForceFinal, extended, targetForceRun, forceRel, forceStates,
              forceStateWf, forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩ :=
              forceIH g requiredGrowth [sourceValue] [targetValue] source target forceResult forceFinal clock forceRun forceSafe
                (by simpa using forceEnv) (.cons payloadWf .nil) sourceWf states ready sourceCompiler targetCompiler oracle
            cases forceResult with
            | err error =>
              cases targetForceResult with
              | val values => simp [resultRel] at forceRel
              | err targetError =>
                have eq : result = .err error ∧ final = forceFinal := by
                  simpa [ClosMti.runForced, sourceDest, forceRun] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                exact ⟨forceG, .err targetError, targetForceFinal, extended,
                  by simp [ClosMti.runForced, targetDest, targetForceRun], forceRel, forceStates, forceStateWf,
                  forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩
            | val forced =>
              cases targetForceResult with
              | err error => simp [resultRel] at forceRel
              | val targetForced =>
                have pointers := List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h extended Set.Subset.rfl growth) values
                have update := updateThunk_lists_relatedFuel sourceValues targetValues forced targetForced forceStates pointers forceRel
                cases sourceUpdate : updateThunk sourceValues forceFinal.refs forced with
                | none =>
                  have bad : result = .err (.abort .typeError) := by
                    simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using congrArg Prod.fst run.symm
                  exact (notType bad).elim
                | some sourceRefs =>
                  cases targetUpdate : updateThunk targetValues targetForceFinal.refs targetForced with
                  | none =>
                    have impossible := update.1 targetUpdate
                    rw [sourceUpdate] at impossible
                    contradiction
                  | some targetRefs =>
                    obtain ⟨sourceRefs', sourceUpdate', finalStates⟩ := update.2 targetRefs targetUpdate
                    rw [sourceUpdate] at sourceUpdate'
                    cases sourceUpdate'
                    have eq : result = .val forced ∧ final = { forceFinal with refs := sourceRefs } := by
                      simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using run.symm
                    have valuesWf : ValuesWellFormedFuel relationFuel forceG allowed targetForceFinal.code forced :=
                      valuesWellFormedFuel_mono forcedWf.1 extended Set.Subset.rfl growth
                    have finalWf := updateThunk_wellFormedFuel sourceValues forced forceFinal sourceRefs
                      forceStateWf valuesWf sourceUpdate
                    obtain ⟨rfl, rfl⟩ := eq
                    exact ⟨forceG, .val targetForced, { targetForceFinal with refs := targetRefs }, extended,
                      by simp [ClosMti.runForced, targetDest, targetForceRun, targetUpdate], forceRel, finalStates, finalWf,
                      incrementalInstallReady_setRefs forceG forceFinal targetForceFinal sourceRefs targetRefs forceReady,
                      forceCompiler, targetForceCompiler, forceOracle, growth⟩

/-- Clock-allowing thunk forcing preserves the pass-state requirement.
This is Flapjack-specific simulation infrastructure. -/
theorem runForced_growing_below_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required g : State) (requiredGrowth : stateExtends required g) (allowed : Set Nat)
    (sourceValues targetValues : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (clock : source.clock < limit) (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (run : ClosMti.runForced sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (forceIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ ClosMti.runForced targetValues { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have inspected := destThunk_relatedFuel states values
  cases sourceDest : destThunk sourceValues source.refs with
  | badRef =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | notThunk =>
    have bad : result = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | isThunk mode sourceValue =>
    rw [sourceDest] at inspected
    cases targetDest : destThunk targetValues target.refs with
    | badRef => rw [targetDest] at inspected; cases inspected
    | notThunk => rw [targetDest] at inspected; cases inspected
    | isThunk targetMode targetValue =>
      rw [targetDest] at inspected
      cases inspected with
      | isThunk _ _ _ payloadRel =>
        cases mode with
        | evaluated =>
          have eq : result = .val [sourceValue] ∧ final = source := by
            simpa [ClosMti.runForced, sourceDest] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨0, g, .val [targetValue], target, stateExtends_refl g ready.well.2,
            by simp [ClosMti.runForced, targetDest], .cons payloadRel .nil, states, sourceWf, ready,
            sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        | notEvaluated =>
          have payloadWf := destThunk_wellFormedFuel sourceValues source .notEvaluated sourceValue sourceWf sourceDest
          have forceEnv : EnvRelFuel relationFuel g allowed target.code [sourceValue] [targetValue] 0
              [(0, appUnit (.var .none 0))] := .equalLength rfl (.cons payloadRel .nil)
          have forcedWf := forceWf g target.code sourceValue source payloadWf sourceWf ready.auxEmpty
          cases forceRun : evaluate [appUnit (.var .none 0)] [sourceValue] source with
          | mk forceResult forceFinal =>
            rw [forceRun] at forcedWf
            have forceSafe : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              subst forceResult
              have eq : result = .err (.abort .typeError) := by
                simpa [ClosMti.runForced, sourceDest, forceRun] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨forceExtra, forceG, targetForceResult, targetForceFinal, extended, targetForceRun, forceRel, forceStates,
              forceStateWf, forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩ :=
              forceIH g requiredGrowth [sourceValue] [targetValue] source target forceResult forceFinal clock forceRun forceSafe
                (by simpa using forceEnv) (.cons payloadWf .nil) sourceWf states ready sourceCompiler targetCompiler oracle
            cases forceResult with
            | err error =>
              cases targetForceResult with
              | val values => simp [resultRel] at forceRel
              | err targetError =>
                have eq : result = .err error ∧ final = forceFinal := by
                  simpa [ClosMti.runForced, sourceDest, forceRun] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                exact ⟨forceExtra, forceG, .err targetError, targetForceFinal, extended,
                  by simp [ClosMti.runForced, targetDest, targetForceRun], forceRel, forceStates, forceStateWf,
                  forceReady, forceCompiler, targetForceCompiler, forceOracle, growth⟩
            | val forced =>
              cases targetForceResult with
              | err error => simp [resultRel] at forceRel
              | val targetForced =>
                have pointers := List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h extended Set.Subset.rfl growth) values
                have update := updateThunk_lists_relatedFuel sourceValues targetValues forced targetForced forceStates pointers forceRel
                cases sourceUpdate : updateThunk sourceValues forceFinal.refs forced with
                | none =>
                  have bad : result = .err (.abort .typeError) := by
                    simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using congrArg Prod.fst run.symm
                  exact (notType bad).elim
                | some sourceRefs =>
                  cases targetUpdate : updateThunk targetValues targetForceFinal.refs targetForced with
                  | none =>
                    have impossible := update.1 targetUpdate
                    rw [sourceUpdate] at impossible
                    contradiction
                  | some targetRefs =>
                    obtain ⟨sourceRefs', sourceUpdate', finalStates⟩ := update.2 targetRefs targetUpdate
                    rw [sourceUpdate] at sourceUpdate'
                    cases sourceUpdate'
                    have eq : result = .val forced ∧ final = { forceFinal with refs := sourceRefs } := by
                      simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using run.symm
                    have valuesWf : ValuesWellFormedFuel relationFuel forceG allowed targetForceFinal.code forced :=
                      valuesWellFormedFuel_mono forcedWf.1 extended Set.Subset.rfl growth
                    have finalWf := updateThunk_wellFormedFuel sourceValues forced forceFinal sourceRefs
                      forceStateWf valuesWf sourceUpdate
                    obtain ⟨rfl, rfl⟩ := eq
                    exact ⟨forceExtra, forceG, .val targetForced, { targetForceFinal with refs := targetRefs }, extended,
                      by simp [ClosMti.runForced, targetDest, targetForceRun, targetUpdate], forceRel, finalStates, finalWf,
                      incrementalInstallReady_setRefs forceG forceFinal targetForceFinal sourceRefs targetRefs forceReady,
                      forceCompiler, targetForceCompiler, forceOracle, growth⟩

/-- Clock-bounded force-thunk simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_force {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (forceIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.op trace (.thunkOp .forceThunk) sourceArgs] [.op trace (.thunkOp .forceThunk) targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace (.thunkOp .forceThunk) targetArgs (by simpa using envs)
  rw [ClosMti.evaluate_force_eq] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsWf,
      argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf sourceWf
        states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [ClosMti.evaluate_force_eq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have argsClock : argsFinal.clock < limit := by
          have bound := evaluate_clock_le sourceArgs sourceEnv source
          rw [argsRun] at bound
          exact Nat.lt_of_le_of_lt bound clock
        have requiredArgs := stateExtends_trans required g argsG requiredGrowth argsExt
        have forceRun : ClosMti.runForced sourceValues argsFinal = (result, final) := by simpa [argsRun] using run
        obtain ⟨finalG, targetResult, targetFinal, forceExt, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runForced_growing_below passFuel relationFuel limit compiler required argsG requiredArgs allowed sourceValues targetValues argsFinal targetArgsFinal argsClock
            result final forceRun notType argsRel argsWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle forceIH forceWf
        refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g argsG finalG argsExt forceExt, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · simpa [ClosMti.evaluate_force_eq, targetArgsRun] using targetRun
        · intro key entry found
          exact growth key entry (argsGrowth key entry found)

/-- Clock-allowing force-thunk simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_force {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (forceIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.op trace (.thunkOp .forceThunk) sourceArgs] [.op trace (.thunkOp .forceThunk) targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_op_args trace (.thunkOp .forceThunk) targetArgs (by simpa using envs)
  rw [ClosMti.evaluate_force_eq] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsExtra, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsWf,
      argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf sourceWf
        states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsExtra, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        simp [ClosMti.evaluate_force_eq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have argsClock : argsFinal.clock < limit := by
          have bound := evaluate_clock_le sourceArgs sourceEnv source
          rw [argsRun] at bound
          exact Nat.lt_of_le_of_lt bound clock
        have requiredArgs := stateExtends_trans required g argsG requiredGrowth argsExt
        have forceRun : ClosMti.runForced sourceValues argsFinal = (result, final) := by simpa [argsRun] using run
        obtain ⟨forceExtra, finalG, targetResult, targetFinal, forceExt, targetRun, related, finalStates, finalWf, finalReady,
          finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          runForced_growing_below_withClock passFuel relationFuel limit compiler required argsG requiredArgs allowed sourceValues targetValues argsFinal targetArgsFinal argsClock
            result final forceRun notType argsRel argsWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle forceIH forceWf
        refine ⟨argsExtra + forceExtra, finalG, targetResult, targetFinal, stateExtends_trans g argsG finalG argsExt forceExt, ?_, related,
          finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
        · have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
            { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) forceExtra
            targetArgsRun (by simp)
          have shiftedArgs' : evaluate targetArgs targetEnv
              { target with clock := target.clock + (argsExtra + forceExtra) } =
              (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + forceExtra }) := by
            simpa [Nat.add_assoc] using shiftedArgs
          simpa [ClosMti.evaluate_force_eq, shiftedArgs'] using targetRun
        · intro key entry found
          exact growth key entry (argsGrowth key entry found)

/-- Clock-bounded source direct-call simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_call {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.call trace ticks label sourceArgs] [.call trace ticks label targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_call_args trace ticks label targetArgs (by simpa using envs)
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        rw [evaluate, fixClock_evaluate, targetArgsRun]
    | val values =>
      have empty : argsFinal.code = HolFiniteMapExact.empty := argsStates.2.2.2.2.2
      have bad : result = .err (.abort .typeError) := by
        simpa [argsRun, findCode, empty, HolFiniteMapExact.empty] using congrArg Prod.fst run.symm
      exact (notType bad).elim

/-- Clock-allowing source direct-call simulation. This is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_call {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.call trace ticks label sourceArgs] [.call trace ticks label targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have argsEnv := envRelFuel_call_args trace ticks label targetArgs (by simpa using envs)
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have eq : result = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType eq
    obtain ⟨argsExtra, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
      argsWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
      argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
        sourceWf states ready sourceCompiler targetCompiler oracle
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have eq : result = .err error ∧ final = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := eq
        refine ⟨argsExtra, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsWf,
          argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
        rw [evaluate, fixClock_evaluate, targetArgsRun]
    | val values =>
      have empty : argsFinal.code = HolFiniteMapExact.empty := argsStates.2.2.2.2.2
      have bad : result = .err (.abort .typeError) := by
        simpa [argsRun, findCode, empty, HolFiniteMapExact.empty] using congrArg Prod.fst run.symm
      exact (notType bad).elim

/-- Clock-bounded call traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_call_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.call trace ticks label args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed args target) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.call trace ticks label args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_call passFuel relationFuel limit compiler next allowed trace ticks label args targetArgs (argsIH targetArgs argsRun)

/-- Clock-allowing call traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_call_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (ticks label : Nat)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.call trace ticks label args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed args target) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.call trace ticks label args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_call passFuel relationFuel limit compiler next allowed trace ticks label args targetArgs (argsIH targetArgs argsRun)

/-- Clock-bounded force traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_force_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed args target)
    (forceIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.op trace (.thunkOp .forceThunk) args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelow_force passFuel relationFuel limit compiler next allowed trace args targetArgs (argsIH targetArgs argsRun) forceIH forceWf

/-- Clock-allowing force traversal. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_force_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed args target)
    (forceIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)])
    (forceWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code value → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code
        (evaluate [appUnit (.var .none 0)] [value] state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.op trace (.thunkOp .forceThunk) args] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact growingExprsSimFromBelowWithClock_force passFuel relationFuel limit compiler next allowed trace args targetArgs (argsIH targetArgs argsRun) forceIH forceWf

/-- The generated force application can use a full application simulation
at any clock bound and pass state. The application simulation remains an
assumption. This is Flapjack-specific simulation infrastructure. -/
theorem forceApplication_growing_below {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (appIH : GrowingAppSim (F := F) passFuel relationFuel compiler allowed none) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  apply growingExprsSimFrom_below
  exact growingExprsSim_from passFuel relationFuel compiler required allowed _ _
    (forceApplication_growing_sim passFuel relationFuel compiler allowed appIH)

/-- Clock-bounded retained application simulation. The application and
source well-formedness hypotheses remain assumptions; this is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_app {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Option Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceArgs targetArgs : List ClosLang.Exp)
    (length : sourceArgs.length = targetArgs.length)
    (argsIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (fnIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed loc) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [.app trace loc sourceFn sourceArgs] [.app trace loc targetFn targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have appEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .app trace loc targetFn targetArgs)] := by simpa using envs
  obtain ⟨fnEnv, argsEnv⟩ := envRelFuel_app_parts trace loc targetFn targetArgs appEnv
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp [empty] at length
    have targetNotEmpty : targetArgs.isEmpty = false := by
      cases targetArgs with
      | nil => exact (targetNonempty rfl).elim
      | cons head tail => rfl
    have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases argsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [argsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : sourceResult = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
        argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
          sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : sourceResult = .err error ∧ sourceFinal = argsFinal := by simpa [argsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [evaluate]
          simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
          rw [targetArgsRun]
      | val values =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [argsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans required g argsG requiredGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) values targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases fnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [fnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : sourceResult = .err (.abort .typeError) := by
                simpa [argsRun, fnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates,
              fnStateWf, fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH argsG requiredArgs sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal argsClock fnRun fnSafe
                (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val vs => simp [resultRel] at fnRel
              | err targetError =>
                have eq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                rw [evaluate]
                simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                rw [targetArgsRun, targetFnRun]
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues fnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) values targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have fnClock : fnFinal.clock < limit := by
                  have bound := evaluate_clock_le [sourceFn] sourceEnv argsFinal
                  rw [fnRun] at bound
                  exact Nat.lt_of_le_of_lt bound argsClock
                have appRun : evaluateApp loc fnValue values fnFinal = (sourceResult, sourceFinal) := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code values :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨finalG, result, final, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                  appIH fnG fnValue targetFnValue values targetValues fnFinal targetFnFinal sourceResult sourceFinal
                    fnClock appRun notType functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady
                    fnCompiler targetFnCompiler fnOracle
                refine ⟨finalG, result, final, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
                  finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                  simpa using targetRun
                · intro key entry found
                  exact appGrowth key entry (prefixGrowth key entry found)

/-- Clock-allowing retained application simulation. The application and
source well-formedness hypotheses remain assumptions; this is
Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelowWithClock_app {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Option Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceArgs targetArgs : List ClosLang.Exp)
    (length : sourceArgs.length = targetArgs.length)
    (argsIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceArgs targetArgs)
    (fnIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed loc) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [.app trace loc sourceFn sourceArgs] [.app trace loc targetFn targetArgs] := by
  intro g requiredGrowth sourceEnv targetEnv source target sourceResult sourceFinal clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  have appEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      [(0, .app trace loc targetFn targetArgs)] := by simpa using envs
  obtain ⟨fnEnv, argsEnv⟩ := envRelFuel_app_parts trace loc targetFn targetArgs appEnv
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp [empty] at length
    have targetNotEmpty : targetArgs.isEmpty = false := by
      cases targetArgs with
      | nil => exact (targetNonempty rfl).elim
      | cons head tail => rfl
    have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases argsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [argsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : sourceResult = .err (.abort .typeError) := by simpa [argsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsExtra, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates,
        argsStateWf, argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH g requiredGrowth sourceEnv targetEnv source target argsResult argsFinal clock argsRun argsSafe argsEnv envWf
          sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : sourceResult = .err error ∧ sourceFinal = argsFinal := by simpa [argsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsExtra, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [evaluate]
          simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
          rw [targetArgsRun]
      | val values =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [argsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans required g argsG requiredGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) values targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases fnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [fnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : sourceResult = .err (.abort .typeError) := by
                simpa [argsRun, fnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnExtra, fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates,
              fnStateWf, fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH argsG requiredArgs sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal argsClock fnRun fnSafe
                (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val vs => simp [resultRel] at fnRel
              | err targetError =>
                have eq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨argsExtra + fnExtra, fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
                  { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) fnExtra
                  targetArgsRun (by simp)
                have shiftedArgs' : evaluate targetArgs targetEnv
                    { target with clock := target.clock + (argsExtra + fnExtra) } =
                    (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra }) := by
                  simpa [Nat.add_assoc] using shiftedArgs
                rw [evaluate]
                simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                rw [shiftedArgs', targetFnRun]
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues fnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra } targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) values targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have fnClock : fnFinal.clock < limit := by
                  have bound := evaluate_clock_le [sourceFn] sourceEnv argsFinal
                  rw [fnRun] at bound
                  exact Nat.lt_of_le_of_lt bound argsClock
                have appRun : evaluateApp loc fnValue values fnFinal = (sourceResult, sourceFinal) := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code values :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨appExtra, finalG, result, final, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                  appIH fnG fnValue targetFnValue values targetValues fnFinal targetFnFinal sourceResult sourceFinal
                    fnClock appRun notType functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady
                    fnCompiler targetFnCompiler fnOracle
                refine ⟨argsExtra + (fnExtra + appExtra), finalG, result, final, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
                  finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
                · have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
                    { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) (fnExtra + appExtra)
                    targetArgsRun (by simp)
                  have shiftedArgs' : evaluate targetArgs targetEnv
                      { target with clock := target.clock + (argsExtra + (fnExtra + appExtra)) } =
                      (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + (fnExtra + appExtra) }) := by
                    simpa [Nat.add_assoc] using shiftedArgs
                  have shiftedFn := (evaluate_addClock (C := C) (F := F)).1 [targetFn] targetEnv
                    { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra } targetFnFinal
                    (.val [targetFnValue]) appExtra targetFnRun (by simp)
                  have shiftedFn' : evaluate [targetFn] targetEnv
                      { targetArgsFinal with clock := targetArgsFinal.clock + (fnExtra + appExtra) } =
                      (.val [targetFnValue], { targetFnFinal with clock := targetFnFinal.clock + appExtra }) := by
                    simpa [Nat.add_assoc] using shiftedFn
                  rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [shiftedArgs', shiftedFn']
                  simpa using targetRun
                · intro key entry found
                  exact appGrowth key entry (prefixGrowth key entry found)

/-- Clock-bounded traversal of a location-free application. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_none_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace none sourceFn sourceArgs) initial = some (out, final))
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed none) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.app trace none sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, next⟩, fnRun, rfl, rfl⟩ := run
  have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
  exact growingExprsSimFromBelow_app passFuel relationFuel limit compiler next allowed trace none sourceFn targetFn sourceArgs targetArgs
    length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- Clock-allowing traversal of a location-free application. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_none_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace none sourceFn sourceArgs) initial = some (out, final))
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed none) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.app trace none sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, next⟩, fnRun, rfl, rfl⟩ := run
  have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
  exact growingExprsSimFromBelowWithClock_app passFuel relationFuel limit compiler next allowed trace none sourceFn targetFn sourceArgs targetArgs
    length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- The generated force application follows from a clock-bounded
application simulation. This is Flapjack-specific infrastructure. -/
theorem forceApplication_growing_from_bounded_app {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed none) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  let unitExp : ClosLang.Exp := .op .none (.blockOp (.cons 0)) []
  have nilSim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [] [] :=
    growingExprsSimFrom_below passFuel relationFuel limit compiler required allowed [] []
      (growingExprsSim_from passFuel relationFuel compiler required allowed [] []
        (growingExprsSim_of_forall₂ passFuel relationFuel compiler allowed .nil))
  have nilWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_nil_wellFormedFuel env state stateWf
  have unitSim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [unitExp] [unitExp] :=
    growingExprsSimFromBelow_ordinaryOp passFuel relationFuel limit compiler required allowed .none (.blockOp (.cons 0)) [] []
      (by simp) (by simp) nilSim nilWf
  have unitWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [unitExp] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_ordinaryOp_wellFormedFuel .none (.blockOp (.cons 0)) [] env state (by simp) (by simp)
      (evaluate_nil_wellFormedFuel env state stateWf)
  have fnSim := growingExprsSimFrom_below (F := F) passFuel relationFuel limit compiler required allowed _ _
    (growingExprsSim_from passFuel relationFuel compiler required allowed _ _
      (growingExprsSim_var passFuel relationFuel compiler allowed .none 0))
  have fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [.var .none 0] env state) := by
    intro g code env state envWf stateWf _
    exact evaluate_var_state_wellFormedFuel .none 0 env state envWf stateWf
  simpa [appUnit, unitExp] using
    growingExprsSimFromBelow_app passFuel relationFuel limit compiler required allowed .none none (.var .none 0) (.var .none 0)
      [unitExp] [unitExp] rfl unitSim fnSim unitWf fnWf appIH

/-- The generated force application follows from a clock-allowing
application simulation. This is Flapjack-specific infrastructure. -/
theorem forceApplication_growing_from_clock_app {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed none) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed
      [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  let unitExp : ClosLang.Exp := .op .none (.blockOp (.cons 0)) []
  have nilSim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [] [] :=
    growingExprsSimFrom_below passFuel relationFuel limit compiler required allowed [] []
      (growingExprsSim_from passFuel relationFuel compiler required allowed [] []
        (growingExprsSim_of_forall₂ passFuel relationFuel compiler allowed .nil))
  have nilWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_nil_wellFormedFuel env state stateWf
  have unitSim : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [unitExp] [unitExp] :=
    growingExprsSimFromBelow_ordinaryOp passFuel relationFuel limit compiler required allowed .none (.blockOp (.cons 0)) [] []
      (by simp) (by simp) nilSim nilWf
  have unitWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [unitExp] env state) := by
    intro g code env state _ stateWf _
    exact evaluate_ordinaryOp_wellFormedFuel .none (.blockOp (.cons 0)) [] env state (by simp) (by simp)
      (evaluate_nil_wellFormedFuel env state stateWf)
  have fnSim := growingExprsSimFrom_below (F := F) passFuel relationFuel limit compiler required allowed _ _
    (growingExprsSim_from passFuel relationFuel compiler required allowed _ _
      (growingExprsSim_var passFuel relationFuel compiler allowed .none 0))
  have fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [.var .none 0] env state) := by
    intro g code env state envWf stateWf _
    exact evaluate_var_state_wellFormedFuel .none 0 env state envWf stateWf
  simpa [appUnit, unitExp] using
    growingExprsSimFromBelowWithClock_app passFuel relationFuel limit compiler required allowed .none none (.var .none 0) (.var .none 0)
      [unitExp] [unitExp] rfl
      (growingExprsSimFromBelow_withClock passFuel relationFuel limit compiler required allowed _ _ unitSim)
      (growingExprsSimFromBelow_withClock passFuel relationFuel limit compiler required allowed _ _ fnSim)
      unitWf fnWf appIH

/-- The bounded force-thunk traversal uses the clock-bounded application
induction for its generated application. Source application well-formedness
is still an assumption. This is Flapjack-specific infrastructure. -/
theorem callsFuel_force_growing_below_of_app {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed args target)
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed none)
    (appWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code function → ValuesWellFormedFuel relationFuel g allowed code args →
      StateWellFormedFuel relationFuel g allowed code state →
      EvalWellFormedFuel relationFuel g allowed code (evaluateApp none function args state)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed
      [.op trace (.thunkOp .forceThunk) args] [out] := by
  exact callsFuel_force_growing_below passFuel relationFuel traversalFuel limit compiler allowed trace args initial final out
    run argsIH (forceApplication_growing_from_bounded_app passFuel relationFuel limit compiler final allowed appIH)
    (forceApplication_growing_wf relationFuel allowed appWf)

/-- The clock-allowing force-thunk traversal uses the clock-allowing application
induction for its generated application. Source application well-formedness
is still an assumption. This is Flapjack-specific infrastructure. -/
theorem callsFuel_force_growing_below_withClock_of_app {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel traversalFuel args initial = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed args target)
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed none)
    (appWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValueWellFormedFuel relationFuel g allowed code function → ValuesWellFormedFuel relationFuel g allowed code args →
      StateWellFormedFuel relationFuel g allowed code state →
      EvalWellFormedFuel relationFuel g allowed code (evaluateApp none function args state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [.op trace (.thunkOp .forceThunk) args] [out] := by
  exact callsFuel_force_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace args initial final out
    run argsIH (forceApplication_growing_from_clock_app passFuel relationFuel limit compiler final allowed appIH)
    (forceApplication_growing_wf relationFuel allowed appWf)

/-- Clock-bounded traversal of an application whose location is not
known to the pass. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_unknown_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace (some loc) sourceFn sourceArgs) initial = some (out, final))
    (unknown : sptLookup loc final.1 = none)
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed (some loc)) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed [.app trace (some loc) sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup loc afterFn.1).isSome
  · simp [found] at rest
    split at rest <;> simp_all
  · simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
    exact growingExprsSimFromBelow_app passFuel relationFuel limit compiler afterFn allowed trace (some loc) sourceFn targetFn sourceArgs targetArgs
      length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- Clock-allowing traversal of an application whose location is not
known to the pass. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_unknown_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (loc : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace (some loc) sourceFn sourceArgs) initial = some (out, final))
    (unknown : sptLookup loc final.1 = none)
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed (some loc)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [.app trace (some loc) sourceFn sourceArgs] [out] := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup loc afterFn.1).isSome
  · simp [found] at rest
    split at rest <;> simp_all
  · simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    have length := callsListFuel_length traversalFuel sourceArgs initial middle targetArgs argsRun
    exact growingExprsSimFromBelowWithClock_app passFuel relationFuel limit compiler afterFn allowed trace (some loc) sourceFn targetFn sourceArgs targetArgs
      length.symm (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) argsWf fnWf appIH

/-- A full application uses clock-bounded body simulation and a
shorter, clock-bounded application hypothesis. This is Flapjack-specific
simulation infrastructure. -/
theorem evaluateApp_full_growing_clockBelow {C F : Type} (passFuel relationFuel clockLimit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat) (g : State)
    (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < clockLimit) (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (run : evaluateApp requested sourceFun sourceArgs source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (functions : ValueRelFuel relationFuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs)
    (functionWf : ValueWellFormedFuel relationFuel g allowed target.code sourceFun)
    (argsWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs)
    (stateWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (bodyIH : ∀ (targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed target.code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel source.clock compiler g allowed [sourceBody] [targetBody])
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (appIH : GrowingAppSimArgClockBelow (F := F) passFuel relationFuel sourceArgs.length clockLimit compiler allowed requested) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have len := args.length_eq
    simp [empty] at len
    cases sourceArgs with
    | nil => exact nonempty rfl
    | cons head tail => simp at len
  have maxApp := states.2.2.1
  obtain ⟨targetBody, targetBodyEnv, targetRest, loc, sourceFns, targetFns, index, arity,
      targetClosure, bodyEnv, restRel, closure, sourceLookup, targetLookup, _⟩ :=
    destClosure_full_fuel relationFuel g allowed target.code source.maxApp requested sourceFun targetFun
      sourceArgs targetArgs sourceBody sourceBodyEnv sourceRest sourceClosure functions args
  have ⟨sourceBodyEnvWf, sourceRestWf⟩ := destClosure_full_wellFormedFuel source.maxApp requested sourceFun
    sourceArgs sourceBodyEnv sourceRest sourceBody functionWf argsWf sourceClosure
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs =
      some (.fullApp targetBody targetBodyEnv targetRest) := by simpa [← maxApp] using targetClosure
  have restShort := destClosure_full_remaining_lt source.maxApp requested sourceFun sourceArgs sourceBodyEnv sourceRest
    sourceBody sourceClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  have restLengths := restRel.length_eq
  let cost := sourceArgs.length - sourceRest.length
  have targetCost : targetArgs.length - targetRest.length = cost := by simp [cost, ← lengths, ← restLengths]
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at run
      have sourceCostEq : sourceTail.length + 1 - sourceRest.length = cost := rfl
      have targetCostEq : targetTail.length + 1 - targetRest.length = cost := targetCost
      simp only [List.length_cons, sourceCostEq] at run
      by_cases timeout : source.clock < cost
      · have sourceEq : result = .err (.abort .timeoutError) ∧ final = { source with clock := 0 } := by
          simpa [timeout] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨g, .err (.abort .timeoutError), { target with clock := 0 }, stateExtends_refl g ready.well.2,
          ?_, rfl, stateRelFuel_zeroClock states, stateWellFormedFuel_clock stateWf 0,
          incrementalInstallReady_setClock g source target 0 0 ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        rw [evaluateApp, targetClosure']
        simp only [List.length_cons, targetCostEq]
        have targetTimeout : target.clock < cost := by omega
        simp [targetTimeout]
      · let sourceStart := decClock cost source
        let targetStart := decClock cost target
        have startClock : sourceStart.clock < source.clock := by
          simp only [sourceStart, decClock]
          dsimp [cost]
          omega
        have startStates : StateRelFuel relationFuel g allowed sourceStart targetStart := stateRelFuel_decClock states cost
        have startWf : StateWellFormedFuel relationFuel g allowed targetStart.code sourceStart := by
          simpa [sourceStart, targetStart, decClock] using stateWellFormedFuel_clock stateWf _
        have startReady : IncrementalInstallReady g sourceStart targetStart :=
          incrementalInstallReady_decClock g source target cost ready
        simp only [if_neg timeout, fixClock_evaluate] at run
        cases bodyRun : evaluate [sourceBody] sourceBodyEnv sourceStart with
        | mk bodyResult bodyFinal =>
          have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
            intro bad
            subst bodyResult
            have eq : result = .err (.abort .typeError) := by
              simpa [sourceStart, bodyRun] using congrArg Prod.fst run.symm
            exact notType eq
          have sourceBodyWf := bodyWf target.code sourceBody targetBody loc sourceFns targetFns index arity
            closure sourceLookup targetLookup sourceBodyEnv sourceStart sourceBodyEnvWf startWf startReady.auxEmpty
          rw [bodyRun] at sourceBodyWf
          obtain ⟨bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
            bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
            bodyIH targetBody loc sourceFns targetFns index arity closure sourceLookup targetLookup
              g (stateExtends_refl g ready.well.2) sourceBodyEnv targetBodyEnv sourceStart targetStart bodyResult bodyFinal startClock bodyRun bodySafe
              (by simpa [targetStart, decClock] using bodyEnv) sourceBodyEnvWf startWf startStates startReady
              (by simpa [sourceStart, decClock] using sourceCompiler)
              (by simpa [targetStart, decClock] using targetCompiler)
              (by simpa [sourceStart, targetStart, decClock] using oracle)
          have targetBodyRun' : evaluate [targetBody] targetBodyEnv (decClock cost target) =
              (targetBodyResult, targetBodyFinal) := by simpa [targetStart] using targetBodyRun
          cases bodyResult with
          | err error =>
            cases targetBodyResult with
            | val vs => simp [resultRel] at bodyRel
            | err targetError =>
              have eq : result = .err error ∧ final = bodyFinal := by simpa [sourceStart, bodyRun] using run.symm
              obtain ⟨rfl, rfl⟩ := eq
              refine ⟨bodyG, .err targetError, targetBodyFinal, bodyExt, ?_, bodyRel, bodyStates, bodyStateWf,
                bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩
              rw [evaluateApp, targetClosure']
              simp only [List.length_cons, targetCostEq]
              have targetEnough : ¬ target.clock < cost := by omega
              rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun']
          | val sourceValues =>
            obtain ⟨sourceValue, rfl⟩ := evaluate_singleton_value sourceBody sourceBodyEnv sourceStart bodyFinal sourceValues bodyRun
            cases targetBodyResult with
            | err error => simp [resultRel] at bodyRel
            | val targetValues =>
              obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetBodyEnv targetStart targetBodyFinal targetValues targetBodyRun
              have valueRel : ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue targetValue := by
                simpa [resultRel] using bodyRel
              have restRel' : List.Forall₂ (ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code) sourceRest targetRest :=
                List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h bodyExt Set.Subset.rfl bodyGrowth) restRel
              have bodyClock : bodyFinal.clock < clockLimit := by
                have bound := evaluate_clock_le [sourceBody] sourceBodyEnv sourceStart
                rw [bodyRun] at bound
                exact Nat.lt_trans (Nat.lt_of_le_of_lt bound startClock) clock
              have nextRun : evaluateApp requested sourceValue sourceRest bodyFinal = (result, final) := by
                simpa [sourceStart, bodyRun] using run
              have sourceValueWf : ValueWellFormedFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue := by
                have valueWf : ValueWellFormedFuel relationFuel g allowed targetStart.code sourceValue := by
                  cases sourceBodyWf.1 with
                  | cons head tail => exact head
                exact valueWellFormedFuel_mono valueWf bodyExt Set.Subset.rfl bodyGrowth
              have sourceRestWf' := valuesWellFormedFuel_mono sourceRestWf bodyExt Set.Subset.rfl bodyGrowth
              obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                appIH bodyG sourceValue targetValue sourceRest targetRest bodyFinal targetBodyFinal result final
                  restShort bodyClock nextRun notType valueRel restRel' sourceValueWf sourceRestWf' bodyStateWf bodyStates bodyReady
                  bodyCompiler targetBodyCompiler bodyOracle
              refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g bodyG finalG bodyExt appExt, ?_, related,
                finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
              · rw [evaluateApp, targetClosure']
                simp only [List.length_cons, targetCostEq]
                have targetEnough : ¬ target.clock < cost := by omega
                rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun']
                exact targetRun
              · intro key entry found
                exact appGrowth key entry (bodyGrowth key entry found)

/-- A full application uses clock-allowing body simulation and a
shorter, clock-allowing application hypothesis. This is Flapjack-specific
simulation infrastructure. -/
theorem evaluateApp_full_growing_clockBelow_withClock {C F : Type} (passFuel relationFuel clockLimit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat) (g : State)
    (sourceFun targetFun : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < clockLimit) (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (run : evaluateApp requested sourceFun sourceArgs source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (functions : ValueRelFuel relationFuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceArgs targetArgs)
    (functionWf : ValueWellFormedFuel relationFuel g allowed target.code sourceFun)
    (argsWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceArgs)
    (stateWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (bodyIH : ∀ (targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed target.code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSimFromBelowWithClockArity (F := F) passFuel relationFuel source.clock compiler g allowed arity [sourceBody] [targetBody])
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state))
    (appIH : GrowingAppSimArgClockBelowWithClock (F := F) passFuel relationFuel sourceArgs.length clockLimit compiler allowed requested) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluateApp requested targetFun targetArgs { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have len := args.length_eq
    simp [empty] at len
    cases sourceArgs with
    | nil => exact nonempty rfl
    | cons head tail => simp at len
  have maxApp := states.2.2.1
  obtain ⟨targetBody, targetBodyEnv, targetRest, loc, sourceFns, targetFns, index, arity,
      targetClosure, bodyEnv, restRel, closure, sourceLookup, targetLookup, _, sourceBodyBound⟩ :=
    destClosure_full_fuel relationFuel g allowed target.code source.maxApp requested sourceFun targetFun
      sourceArgs targetArgs sourceBody sourceBodyEnv sourceRest sourceClosure functions args
  have ⟨sourceBodyEnvWf, sourceRestWf⟩ := destClosure_full_wellFormedFuel source.maxApp requested sourceFun
    sourceArgs sourceBodyEnv sourceRest sourceBody functionWf argsWf sourceClosure
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs =
      some (.fullApp targetBody targetBodyEnv targetRest) := by simpa [← maxApp] using targetClosure
  have restShort := destClosure_full_remaining_lt source.maxApp requested sourceFun sourceArgs sourceBodyEnv sourceRest
    sourceBody sourceClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  have restLengths := restRel.length_eq
  let cost := sourceArgs.length - sourceRest.length
  have targetCost : targetArgs.length - targetRest.length = cost := by simp [cost, ← lengths, ← restLengths]
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at run
      have sourceCostEq : sourceTail.length + 1 - sourceRest.length = cost := rfl
      have targetCostEq : targetTail.length + 1 - targetRest.length = cost := targetCost
      simp only [List.length_cons, sourceCostEq] at run
      by_cases timeout : source.clock < cost
      · have sourceEq : result = .err (.abort .timeoutError) ∧ final = { source with clock := 0 } := by
          simpa [timeout] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨0, g, .err (.abort .timeoutError), { target with clock := 0 }, stateExtends_refl g ready.well.2,
          ?_, rfl, stateRelFuel_zeroClock states, stateWellFormedFuel_clock stateWf 0,
          incrementalInstallReady_setClock g source target 0 0 ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
        rw [evaluateApp, targetClosure']
        simp only [List.length_cons, targetCostEq]
        have targetTimeout : target.clock < cost := by omega
        simp [targetTimeout]
      · let sourceStart := decClock cost source
        let targetStart := decClock cost target
        have startClock : sourceStart.clock < source.clock := by
          simp only [sourceStart, decClock]
          dsimp [cost]
          omega
        have startStates : StateRelFuel relationFuel g allowed sourceStart targetStart := stateRelFuel_decClock states cost
        have startWf : StateWellFormedFuel relationFuel g allowed targetStart.code sourceStart := by
          simpa [sourceStart, targetStart, decClock] using stateWellFormedFuel_clock stateWf _
        have startReady : IncrementalInstallReady g sourceStart targetStart :=
          incrementalInstallReady_decClock g source target cost ready
        simp only [if_neg timeout, fixClock_evaluate] at run
        cases bodyRun : evaluate [sourceBody] sourceBodyEnv sourceStart with
        | mk bodyResult bodyFinal =>
          have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
            intro bad
            subst bodyResult
            have eq : result = .err (.abort .typeError) := by
              simpa [sourceStart, bodyRun] using congrArg Prod.fst run.symm
            exact notType eq
          have sourceBodyWf := bodyWf target.code sourceBody targetBody loc sourceFns targetFns index arity
            closure sourceLookup targetLookup sourceBodyEnv sourceStart sourceBodyEnvWf startWf startReady.auxEmpty
          rw [bodyRun] at sourceBodyWf
          obtain ⟨bodyExtra, bodyG, targetBodyResult, targetBodyFinal, bodyExt, targetBodyRun, bodyRel, bodyStates,
            bodyStateWf, bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩ :=
            bodyIH targetBody loc sourceFns targetFns index arity closure sourceLookup targetLookup
              g (stateExtends_refl g ready.well.2) sourceBodyEnv targetBodyEnv sourceStart targetStart bodyResult bodyFinal startClock sourceBodyBound bodyRun bodySafe
              (by simpa [targetStart, decClock] using bodyEnv) sourceBodyEnvWf startWf startStates startReady
              (by simpa [sourceStart, decClock] using sourceCompiler)
              (by simpa [targetStart, decClock] using targetCompiler)
              (by simpa [sourceStart, targetStart, decClock] using oracle)
          have targetBodyRun' : evaluate [targetBody] targetBodyEnv
              (decClock cost { target with clock := target.clock + bodyExtra }) =
              (targetBodyResult, targetBodyFinal) := by
            have enough : cost ≤ target.clock := by omega
            have shift : target.clock + bodyExtra - cost = target.clock - cost + bodyExtra := by omega
            simpa [targetStart, decClock, shift] using targetBodyRun
          cases bodyResult with
          | err error =>
            cases targetBodyResult with
            | val vs => simp [resultRel] at bodyRel
            | err targetError =>
              have eq : result = .err error ∧ final = bodyFinal := by simpa [sourceStart, bodyRun] using run.symm
              obtain ⟨rfl, rfl⟩ := eq
              refine ⟨bodyExtra, bodyG, .err targetError, targetBodyFinal, bodyExt, ?_, bodyRel, bodyStates, bodyStateWf,
                bodyReady, bodyCompiler, targetBodyCompiler, bodyOracle, bodyGrowth⟩
              rw [evaluateApp, targetClosure']
              simp only [List.length_cons, targetCostEq]
              have targetEnough : ¬ target.clock + bodyExtra < cost := by omega
              rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun']
          | val sourceValues =>
            obtain ⟨sourceValue, rfl⟩ := evaluate_singleton_value sourceBody sourceBodyEnv sourceStart bodyFinal sourceValues bodyRun
            cases targetBodyResult with
            | err error => simp [resultRel] at bodyRel
            | val targetValues =>
              obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetBodyEnv { targetStart with clock := targetStart.clock + bodyExtra } targetBodyFinal targetValues targetBodyRun
              have valueRel : ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue targetValue := by
                simpa [resultRel] using bodyRel
              have restRel' : List.Forall₂ (ValueRelFuel relationFuel bodyG allowed targetBodyFinal.code) sourceRest targetRest :=
                List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h bodyExt Set.Subset.rfl bodyGrowth) restRel
              have bodyClock : bodyFinal.clock < clockLimit := by
                have bound := evaluate_clock_le [sourceBody] sourceBodyEnv sourceStart
                rw [bodyRun] at bound
                exact Nat.lt_trans (Nat.lt_of_le_of_lt bound startClock) clock
              have nextRun : evaluateApp requested sourceValue sourceRest bodyFinal = (result, final) := by
                simpa [sourceStart, bodyRun] using run
              have sourceValueWf : ValueWellFormedFuel relationFuel bodyG allowed targetBodyFinal.code sourceValue := by
                have valueWf : ValueWellFormedFuel relationFuel g allowed targetStart.code sourceValue := by
                  cases sourceBodyWf.1 with
                  | cons head tail => exact head
                exact valueWellFormedFuel_mono valueWf bodyExt Set.Subset.rfl bodyGrowth
              have sourceRestWf' := valuesWellFormedFuel_mono sourceRestWf bodyExt Set.Subset.rfl bodyGrowth
              obtain ⟨appExtra, finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                finalCompiler, targetFinalCompiler, finalOracle, appGrowth⟩ :=
                appIH bodyG sourceValue targetValue sourceRest targetRest bodyFinal targetBodyFinal result final
                  restShort bodyClock nextRun notType valueRel restRel' sourceValueWf sourceRestWf' bodyStateWf bodyStates bodyReady
                  bodyCompiler targetBodyCompiler bodyOracle
              refine ⟨bodyExtra + appExtra, finalG, targetResult, targetFinal, stateExtends_trans g bodyG finalG bodyExt appExt, ?_, related,
                finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
              · have shiftedBody := (evaluate_addClock (C := C) (F := F)).1 [targetBody] targetBodyEnv
                  { targetStart with clock := targetStart.clock + bodyExtra } targetBodyFinal (.val [targetValue]) appExtra
                  targetBodyRun (by simp)
                have enough : cost ≤ target.clock := by omega
                have shiftedBody' : evaluate [targetBody] targetBodyEnv
                    (decClock cost { target with clock := target.clock + (bodyExtra + appExtra) }) =
                    (.val [targetValue], { targetBodyFinal with clock := targetBodyFinal.clock + appExtra }) := by
                  have shift : target.clock + (bodyExtra + appExtra) - cost =
                      target.clock - cost + (bodyExtra + appExtra) := by omega
                  simpa [targetStart, decClock, shift, Nat.add_assoc] using shiftedBody
                rw [evaluateApp, targetClosure']
                simp only [List.length_cons, targetCostEq]
                have targetEnough : ¬ target.clock + (bodyExtra + appExtra) < cost := by omega
                rw [if_neg targetEnough, fixClock_evaluate, shiftedBody']
                exact targetRun
              · intro key entry found
                exact appGrowth key entry (bodyGrowth key entry found)

/-- Strong induction on argument count establishes clock-bounded
application simulation from bounded closure bodies and source
well-formedness. This is Flapjack-specific infrastructure. -/
theorem growingAppSimClockBelow_of_bodies {C F : Type} (passFuel relationFuel clockLimit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat)
    (bodyIH : ∀ callerClock, callerClock < clockLimit → ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel callerClock compiler g allowed [sourceBody] [targetBody])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state)) :
    GrowingAppSimClockBelow (F := F) passFuel relationFuel clockLimit compiler allowed requested := by
  have all : ∀ limit, GrowingAppSimArgClockBelow (F := F) passFuel relationFuel limit clockLimit compiler allowed requested := by
    intro limit
    induction limit using Nat.strongRecOn with
    | ind limit ih =>
      intro g sourceFun targetFun sourceArgs targetArgs source target result final bound clock run notType functions args
        functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
      cases sourceArgs with
      | nil =>
        have targetEmpty : targetArgs = [] := by
          have len := args.length_eq
          cases targetArgs with
          | nil => rfl
          | cons head tail => simp at len
        subst targetArgs
        exact evaluateApp_nil_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun
          source target result final run functions stateWf states ready sourceCompiler targetCompiler oracle
      | cons first rest =>
        have nonempty : first :: rest ≠ [] := by simp
        cases closureRun : destClosure source.maxApp requested sourceFun (first :: rest) with
        | none =>
          have bad : result = .err (.abort .typeError) := by
            rw [evaluateApp, closureRun] at run
            simpa using congrArg Prod.fst run.symm
          exact (notType bad).elim
        | some closure =>
          cases closure with
          | partialApp value =>
            exact evaluateApp_partial_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun value
              (first :: rest) targetArgs source target result final nonempty closureRun run functions args stateWf states ready
              sourceCompiler targetCompiler oracle
          | fullApp body env remaining =>
            exact evaluateApp_full_growing_clockBelow passFuel relationFuel clockLimit compiler allowed requested g sourceFun targetFun
              (first :: rest) targetArgs body env remaining source target result final clock nonempty closureRun run notType
              functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
              (bodyIH source.clock clock g target.code body) (bodyWf g) (ih (first :: rest).length bound)
  intro g sourceFun targetFun sourceArgs targetArgs source target result final clock run notType functions args functionWf
    argsWf stateWf states ready sourceCompiler targetCompiler oracle
  exact all (sourceArgs.length + 1) g sourceFun targetFun sourceArgs targetArgs source target result final
    (by omega) clock run notType functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle

/-- Strong induction on argument count establishes clock-allowing
application simulation from bounded closure bodies and source
well-formedness. This is Flapjack-specific infrastructure. -/
theorem growingAppSimClockBelowWithClock_of_bodies {C F : Type} (passFuel relationFuel clockLimit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (requested : Option Nat)
    (bodyIH : ∀ callerClock, callerClock < clockLimit → ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      GrowingExprsSimFromBelowWithClockArity (F := F) passFuel relationFuel callerClock compiler g allowed arity [sourceBody] [targetBody])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state)) :
    GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel clockLimit compiler allowed requested := by
  have all : ∀ limit, GrowingAppSimArgClockBelowWithClock (F := F) passFuel relationFuel limit clockLimit compiler allowed requested := by
    intro limit
    induction limit using Nat.strongRecOn with
    | ind limit ih =>
      intro g sourceFun targetFun sourceArgs targetArgs source target result final bound clock run notType functions args
        functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
      cases sourceArgs with
      | nil =>
        have targetEmpty : targetArgs = [] := by
          have len := args.length_eq
          cases targetArgs with
          | nil => rfl
          | cons head tail => simp at len
        subst targetArgs
        obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
          finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
          evaluateApp_nil_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun
            source target result final run functions stateWf states ready sourceCompiler targetCompiler oracle
        exact ⟨0, finalG, targetResult, targetFinal, extended, by simpa using targetRun, related, finalStates,
          finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
      | cons first rest =>
        have nonempty : first :: rest ≠ [] := by simp
        cases closureRun : destClosure source.maxApp requested sourceFun (first :: rest) with
        | none =>
          have bad : result = .err (.abort .typeError) := by
            rw [evaluateApp, closureRun] at run
            simpa using congrArg Prod.fst run.symm
          exact (notType bad).elim
        | some closure =>
          cases closure with
          | partialApp value =>
            obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf,
              finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              evaluateApp_partial_growing passFuel relationFuel compiler allowed requested g sourceFun targetFun value
                (first :: rest) targetArgs source target result final nonempty closureRun run functions args stateWf states ready
                sourceCompiler targetCompiler oracle
            exact ⟨0, finalG, targetResult, targetFinal, extended, by simpa using targetRun, related, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩
          | fullApp body env remaining =>
            exact evaluateApp_full_growing_clockBelow_withClock passFuel relationFuel clockLimit compiler allowed requested g sourceFun targetFun
              (first :: rest) targetArgs body env remaining source target result final clock nonempty closureRun run notType
              functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle
              (bodyIH source.clock clock g target.code body) (bodyWf g) (ih (first :: rest).length bound)
  intro g sourceFun targetFun sourceArgs targetArgs source target result final clock run notType functions args functionWf
    argsWf stateWf states ready sourceCompiler targetCompiler oracle
  exact all (sourceArgs.length + 1) g sourceFun targetFun sourceArgs targetArgs source target result final
    (by omega) clock run notType functions args functionWf argsWf stateWf states ready sourceCompiler targetCompiler oracle

/-- The clock-allowing application induction follows from the ordinary
well-formed expression traversal induction at smaller clocks, including both
open and extracted recursive groups. Source-body well-formedness remains a
separate premise. This is Flapjack-specific infrastructure, not a HOL theorem
port. -/
theorem growingAppSimClockBelowWithClock_of_traversals {C F : Type}
    (passFuel relationFuel clockLimit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (requested : Option Nat)
    (exprIH : ∀ callerClock, callerClock < clockLimit → ∀ depth (initial final : State)
      (body converted : ClosLang.Exp),
      callsFuel depth body initial = some (converted, final) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) initial →
      wellFormed initial →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel callerClock compiler final allowed [body] [converted])
    (bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state)) :
    GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel clockLimit compiler allowed requested := by
  apply growingAppSimClockBelowWithClock_of_bodies passFuel relationFuel clockLimit compiler allowed requested ?_ bodyWf
  intro callerClock clockBound g code sourceBody targetBody loc sourceFns targetFns index arity related sourceLookup targetLookup
  apply recClosureRelFuel_body_arity_withClock passFuel relationFuel callerClock compiler g allowed code loc
    sourceFns targetFns index arity sourceBody targetBody related sourceLookup targetLookup
  intro converted depth initial final _ traversal distinct fresh initialWf
  exact exprIH callerClock clockBound depth initial final sourceBody converted traversal distinct fresh initialWf

/-- A retained application traversal follows from simulations of its
argument and function traversals and the ordinary smaller-clock expression
induction. A general source evaluation well-formedness premise supplies the
argument, function, and closure-body obligations. Known-location rewrites
are handled separately. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_retained_withClock_of_traversals {C F : Type}
    (passFuel relationFuel traversalFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (unknown : ∀ address, location = some address → sptLookup address final.1 = none)
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (exprIH : ∀ callerClock, callerClock < limit → ∀ depth (before after : State)
      (body converted : ClosLang.Exp),
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before → wellFormed before →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel callerClock compiler after allowed [body] [converted])
    (evalWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate expressions env state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [.app trace location sourceFn sourceArgs] [out] := by
  have argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state) := by
    intro g code env state
    exact evalWf g code sourceArgs env state
  have fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state) := by
    intro g code env state
    exact evalWf g code [sourceFn] env state
  have bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state) := by
    intro g code body _ _ _ _ _ _ _ _ _ env state
    exact evalWf g code [body] env state
  have appIH := growingAppSimClockBelowWithClock_of_traversals passFuel relationFuel limit compiler allowed location exprIH bodyWf
  cases location with
  | none =>
    exact callsFuel_app_none_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace
      sourceFn sourceArgs initial final out run argsIH fnIH argsWf fnWf appIH
  | some address =>
    exact callsFuel_app_unknown_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace address
      sourceFn sourceArgs initial final out run (unknown address rfl) argsIH fnIH argsWf fnWf appIH

/-- A clock-bounded simulation supplies the pure-function witness above
a required pass state. This is Flapjack-specific infrastructure. -/
theorem pure_function_growing_witness_below {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required g : State) (requiredGrowth : stateExtends required g) (allowed : Set Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (clock : source.clock < limit) (sourceValue : ClosSem.Value)
    (sourceRun : evaluate [sourceFn] sourceEnv source = (.val [sourceValue], source))
    (targetPure : ClosLang.pure targetFn = true)
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (fnIH : GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [sourceFn] [targetFn]) :
    ∃ nextG targetValue,
      stateExtends g nextG ∧ ValueRelFuel relationFuel nextG allowed target.code sourceValue targetValue ∧
      StateRelFuel relationFuel nextG allowed source target ∧ StateWellFormedFuel relationFuel nextG allowed target.code source ∧
      IncrementalInstallReady nextG source target := by
  obtain ⟨targetEnv, _, envs⟩ := envRelFuel_exists_of_wellFormed relationFuel g allowed target.code sourceEnv envWf
  obtain ⟨nextG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady, _, _, _, _⟩ :=
    fnIH g requiredGrowth sourceEnv targetEnv source target (.val [sourceValue]) source clock sourceRun (by simp)
      (by simpa using envs 0 [(0, targetFn)]) envWf sourceWf states ready sourceCompiler targetCompiler oracle
  have targetSafe : targetResult ≠ .err (.abort .typeError) := by
    intro bad
    subst targetResult
    simp [resultRel] at related
  have pureList : ClosLang.pureList [targetFn] = true := by simp [ClosLang.pureList, targetPure]
  obtain ⟨targetValues, rfl, rfl⟩ := ClosProps.evaluate_pure [targetFn] targetEnv target targetFinal
    targetResult pureList targetRun targetSafe
  cases related with
  | cons head tail =>
    cases tail
    exact ⟨nextG, _, extended, head, finalStates, finalWf, finalReady⟩

/-- A clock-allowing simulation supplies the pure-function witness above
a required pass state. This is Flapjack-specific infrastructure. -/
theorem pure_function_growing_witness_below_withClock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required g : State) (requiredGrowth : stateExtends required g) (allowed : Set Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (clock : source.clock < limit) (sourceValue : ClosSem.Value)
    (sourceRun : evaluate [sourceFn] sourceEnv source = (.val [sourceValue], source))
    (targetPure : ClosLang.pure targetFn = true)
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle)
    (fnIH : GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [sourceFn] [targetFn]) :
    ∃ nextG targetValue,
      stateExtends g nextG ∧ ValueRelFuel relationFuel nextG allowed target.code sourceValue targetValue ∧
      StateRelFuel relationFuel nextG allowed source target ∧ StateWellFormedFuel relationFuel nextG allowed target.code source ∧
      IncrementalInstallReady nextG source target := by
  obtain ⟨targetEnv, _, envs⟩ := envRelFuel_exists_of_wellFormed relationFuel g allowed target.code sourceEnv envWf
  obtain ⟨extraClock, nextG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady, _, _, _, _⟩ :=
    fnIH g requiredGrowth sourceEnv targetEnv source target (.val [sourceValue]) source clock sourceRun (by simp)
      (by simpa using envs 0 [(0, targetFn)]) envWf sourceWf states ready sourceCompiler targetCompiler oracle
  have targetSafe : targetResult ≠ .err (.abort .typeError) := by
    intro bad
    subst targetResult
    simp [resultRel] at related
  have pureList : ClosLang.pureList [targetFn] = true := by simp [ClosLang.pureList, targetPure]
  obtain ⟨targetValues, rfl, rfl⟩ := ClosProps.evaluate_pure [targetFn] targetEnv { target with clock := target.clock + extraClock } targetFinal
    targetResult pureList targetRun targetSafe
  have extraZero : extraClock = 0 := by
    have oldClock := states.2.1
    have newClock := finalStates.2.1
    simp only at newClock
    omega
  subst extraClock
  simp only [Nat.add_zero] at related finalStates finalWf finalReady
  cases related with
  | cons head tail =>
    cases tail
    exact ⟨nextG, _, extended, head, finalStates, finalWf, finalReady⟩

/-- The pure known-location rewrite under a clock bound and pass-state
extension. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_pure_growing_below_at {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (pure : ClosLang.pure sourceFn = true)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, targetPure, outEq⟩ :=
    callsFuel_app_pure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known pure
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_call_args trace targetArgs.length (address + 1) targetArgs
    simpa [outEq] using envs
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g passGrowth sourceEnv targetEnv source target argsResult argsFinal clock
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq, evaluate, fixClock_evaluate, targetArgsRun]
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [sourceArgsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans passFinal g argsG passGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            have sourcePure : ClosLang.pureList [sourceFn] = true := by simp [ClosLang.pureList, pure]
            obtain ⟨fnValues, resultEq, finalEq⟩ :=
              ClosProps.evaluate_pure [sourceFn] sourceEnv argsFinal fnFinal fnResult sourcePure sourceFnRun fnSafe
            subst fnResult
            subst fnFinal
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal argsFinal fnValues sourceFnRun
            have envWf' := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
            have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal envWf' argsStateWf argsReady.auxEmpty
            rw [sourceFnRun] at functionWfEval
            obtain ⟨fnG, targetFnValue, fnExt, functionRel, fnStates, fnStateWf, fnReady⟩ :=
              pure_function_growing_witness_below passFuel relationFuel limit compiler passFinal argsG requiredArgs allowed sourceFn targetFn sourceEnv
                argsFinal targetArgsFinal argsClock fnValue sourceFnRun targetPure envWf' argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle (fnIH targetFn middle fnTraversal)
            have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetArgsFinal.code) sourceValues targetValues :=
              List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl (fun _ _ h => h)) valuesRel
            have appRun : evaluateApp (some address) fnValue sourceValues argsFinal = (result, final) := by
              simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
            have nonempty : sourceValues ≠ [] := by
              have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
              intro empty
              simp [empty] at len
            obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
              evaluateApp_known_full address fnValue sourceValues argsFinal final result nonempty appRun notType
            have sourceClosure' : destClosure targetArgsFinal.maxApp (some address) fnValue sourceValues =
                some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
            obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
              destClosure_known_direct relationFuel fnG allowed targetArgsFinal.code targetArgsFinal.maxApp address fnValue targetFnValue
                sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
            have code : targetArgsFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
              unfold findCode at found
              cases h : targetArgsFinal.code.lookup (address + 1) with
              | none => simp [h] at found
              | some entry =>
                rcases entry with ⟨arity, expression⟩
                simp only [h, bind, Option.bind_some] at found
                split at found
                · rename_i same
                  simp only [Option.some.injEq, Prod.mk.injEq] at found
                  obtain ⟨_, rfl⟩ := found
                  rw [same]
                · simp at found
            have targetClosure' : destClosure targetArgsFinal.maxApp (some address) targetFnValue targetValues =
                some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
              simpa [valuesRel'.length_eq] using targetClosure
            have targetEq := evaluate_pure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs
              targetEnv targetValues targetFnValue target targetArgsFinal stubEnv convertedBody targetArgsRun code targetClosure'
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetArgsFinal.code sourceValues :=
              valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl argsGrowth
            have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetArgsFinal.code fnValue := by
              have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                cases functionWfEval.1 with
                | cons head tail => exact head
              exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl (fun _ _ h => h)
            obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              appIH fnG fnValue targetFnValue sourceValues targetValues argsFinal targetArgsFinal result final argsClock appRun notType
                functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady argsCompiler targetArgsCompiler argsOracle
            refine ⟨finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [outEq] using targetEq.trans targetRun
            · intro key entry found
              exact growth key entry (argsGrowth key entry found)

/-- The clock-allowing pure known-location rewrite under a bound and pass-state
extension. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_pure_growing_below_at_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (pure : ClosLang.pure sourceFn = true)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, targetPure, outEq⟩ :=
    callsFuel_app_pure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known pure
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_call_args trace targetArgs.length (address + 1) targetArgs
    simpa [outEq] using envs
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsExtra, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g passGrowth sourceEnv targetEnv source target argsResult argsFinal clock
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsExtra, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq, evaluate, fixClock_evaluate, targetArgsRun]
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [sourceArgsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans passFinal g argsG passGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            have sourcePure : ClosLang.pureList [sourceFn] = true := by simp [ClosLang.pureList, pure]
            obtain ⟨fnValues, resultEq, finalEq⟩ :=
              ClosProps.evaluate_pure [sourceFn] sourceEnv argsFinal fnFinal fnResult sourcePure sourceFnRun fnSafe
            subst fnResult
            subst fnFinal
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal argsFinal fnValues sourceFnRun
            have envWf' := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
            have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal envWf' argsStateWf argsReady.auxEmpty
            rw [sourceFnRun] at functionWfEval
            obtain ⟨fnG, targetFnValue, fnExt, functionRel, fnStates, fnStateWf, fnReady⟩ :=
              pure_function_growing_witness_below_withClock passFuel relationFuel limit compiler passFinal argsG requiredArgs allowed sourceFn targetFn sourceEnv
                argsFinal targetArgsFinal argsClock fnValue sourceFnRun targetPure envWf' argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle (fnIH targetFn middle fnTraversal)
            have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetArgsFinal.code) sourceValues targetValues :=
              List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl (fun _ _ h => h)) valuesRel
            have appRun : evaluateApp (some address) fnValue sourceValues argsFinal = (result, final) := by
              simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
            have nonempty : sourceValues ≠ [] := by
              have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
              intro empty
              simp [empty] at len
            obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
              evaluateApp_known_full address fnValue sourceValues argsFinal final result nonempty appRun notType
            have sourceClosure' : destClosure targetArgsFinal.maxApp (some address) fnValue sourceValues =
                some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
            obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
              destClosure_known_direct relationFuel fnG allowed targetArgsFinal.code targetArgsFinal.maxApp address fnValue targetFnValue
                sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
            have code : targetArgsFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
              unfold findCode at found
              cases h : targetArgsFinal.code.lookup (address + 1) with
              | none => simp [h] at found
              | some entry =>
                rcases entry with ⟨arity, expression⟩
                simp only [h, bind, Option.bind_some] at found
                split at found
                · rename_i same
                  simp only [Option.some.injEq, Prod.mk.injEq] at found
                  obtain ⟨_, rfl⟩ := found
                  rw [same]
                · simp at found
            have targetClosure' : destClosure targetArgsFinal.maxApp (some address) targetFnValue targetValues =
                some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
              simpa [valuesRel'.length_eq] using targetClosure
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetArgsFinal.code sourceValues :=
              valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl argsGrowth
            have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetArgsFinal.code fnValue := by
              have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                cases functionWfEval.1 with
                | cons head tail => exact head
              exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl (fun _ _ h => h)
            obtain ⟨appExtra, finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
              appIH fnG fnValue targetFnValue sourceValues targetValues argsFinal targetArgsFinal result final argsClock appRun notType
                functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady argsCompiler targetArgsCompiler argsOracle
            have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
              { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) appExtra
              targetArgsRun (by simp)
            have shiftedArgs' : evaluate targetArgs targetEnv
                { target with clock := target.clock + (argsExtra + appExtra) } =
                (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + appExtra }) := by
              simpa [Nat.add_assoc] using shiftedArgs
            have targetEq := evaluate_pure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs
              targetEnv targetValues targetFnValue { target with clock := target.clock + (argsExtra + appExtra) }
              { targetArgsFinal with clock := targetArgsFinal.clock + appExtra } stubEnv convertedBody shiftedArgs'
              (by simpa using code) (by simpa using targetClosure')
            refine ⟨argsExtra + appExtra, finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt, ?_, related,
              finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, ?_⟩
            · simpa [outEq] using targetEq.trans targetRun
            · intro key entry found
              exact growth key entry (argsGrowth key entry found)

/-- The impure known-location rewrite under a clock bound and pass-state
extension. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_impure_growing_below_at {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (impure : ClosLang.pure sourceFn = false)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, outEq⟩ :=
    callsFuel_app_impure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known impure
  have bindingEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      ((targetArgs ++ [targetFn]).map (0, ·)) := by
    apply envRelFuel_let_bindings (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFn])
      (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
        (ClosCall.variables .none targetArgs.length))
    simpa [outEq] using envs
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.mem_append]
    exact Or.inl member
  have fnEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetFn)] := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member ⊢
    exact Or.inr member
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g passGrowth sourceEnv targetEnv source target argsResult argsFinal clock
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq]
          exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFn targetEnv target targetArgsFinal targetError targetArgsRun
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [sourceArgsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans passFinal g argsG passGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [sourceFnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates, fnStateWf,
              fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH targetFn middle fnTraversal argsG requiredArgs sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal argsClock
                sourceFnRun fnSafe (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val values => simp [resultRel] at fnRel
              | err targetError =>
                have eq : result = .err error ∧ final = fnFinal := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                rw [outEq]
                exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFn targetEnv
                  targetValues target targetArgsFinal targetFnFinal targetError targetArgsRun targetFnRun
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues sourceFnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) sourceValues targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have fnClock : fnFinal.clock < limit := by
                  have bound := evaluate_clock_le [sourceFn] sourceEnv argsFinal
                  rw [sourceFnRun] at bound
                  exact Nat.lt_of_le_of_lt bound argsClock
                have appRun : evaluateApp (some address) fnValue sourceValues fnFinal = (result, final) := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
                have nonempty : sourceValues ≠ [] := by
                  have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
                  intro empty
                  simp [empty] at len
                obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
                  evaluateApp_known_full address fnValue sourceValues fnFinal final result nonempty appRun notType
                have sourceClosure' : destClosure targetFnFinal.maxApp (some address) fnValue sourceValues =
                    some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
                obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
                  destClosure_known_direct relationFuel fnG allowed targetFnFinal.code targetFnFinal.maxApp address fnValue targetFnValue
                    sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
                have code : targetFnFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
                  unfold findCode at found
                  cases h : targetFnFinal.code.lookup (address + 1) with
                  | none => simp [h] at found
                  | some entry =>
                    rcases entry with ⟨arity, expression⟩
                    simp only [h, bind, Option.bind_some] at found
                    split at found
                    · rename_i same
                      simp only [Option.some.injEq, Prod.mk.injEq] at found
                      obtain ⟨_, rfl⟩ := found
                      rw [same]
                    · simp at found
                have targetClosure' : destClosure targetFnFinal.maxApp (some address) targetFnValue targetValues =
                    some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
                  simpa [valuesRel'.length_eq] using targetClosure
                have targetEq := callsFuel_app_impure_target_eq traversalFuel trace stubTrace address sourceFn (first :: rest)
                  initial passFinal out targetFn targetArgs middle targetEnv targetValues targetFnValue target targetArgsFinal targetFnFinal
                  stubEnv convertedBody passRun known impure argsTraversal fnTraversal targetArgsRun targetFnRun code targetClosure'
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code sourceValues :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
                  appIH fnG fnValue targetFnValue sourceValues targetValues fnFinal targetFnFinal result final fnClock appRun notType
                    functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady fnCompiler targetFnCompiler fnOracle
                exact ⟨finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt,
                  targetEq.trans targetRun, related, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, fun key entry found => growth key entry (prefixGrowth key entry found)⟩

/-- The clock-allowing impure known-location rewrite under a bound and pass-state
extension. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific simulation infrastructure. -/
theorem callsFuel_app_impure_growing_below_at_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (impure : ClosLang.pure sourceFn = false)
    (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, outEq⟩ :=
    callsFuel_app_impure_shape traversalFuel trace address sourceFn sourceArgs initial passFinal out passRun known impure
  have bindingEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
      ((targetArgs ++ [targetFn]).map (0, ·)) := by
    apply envRelFuel_let_bindings (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFn])
      (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
        (ClosCall.variables .none targetArgs.length))
    simpa [outEq] using envs
  have argsEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.mem_append]
    exact Or.inl member
  have fnEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetFn)] := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member ⊢
    exact Or.inr member
  have initialArgsWf := argsWf g target.code sourceEnv source envWf sourceWf ready.auxEmpty
  cases sourceArgs with
  | nil =>
    have bad : result = .err (.abort .typeError) := by simpa [evaluate] using congrArg Prod.fst run.symm
    exact (notType bad).elim
  | cons first rest =>
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      rw [sourceArgsRun] at initialArgsWf
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have eq : result = .err (.abort .typeError) := by simpa [sourceArgsRun] using congrArg Prod.fst run.symm
        exact notType eq
      obtain ⟨argsExtra, argsG, targetArgsResult, targetArgsFinal, argsExt, targetArgsRun, argsRel, argsStates, argsStateWf,
        argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal g passGrowth sourceEnv targetEnv source target argsResult argsFinal clock
          sourceArgsRun argsSafe argsEnv envWf sourceWf states ready sourceCompiler targetCompiler oracle
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have eq : result = .err error ∧ final = argsFinal := by simpa [sourceArgsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := eq
          refine ⟨argsExtra, argsG, .err targetError, targetArgsFinal, argsExt, ?_, argsRel, argsStates, argsStateWf,
            argsReady, argsCompiler, targetArgsCompiler, argsOracle, argsGrowth⟩
          rw [outEq]
          exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFn targetEnv { target with clock := target.clock + argsExtra } targetArgsFinal targetError targetArgsRun
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have argsClock : argsFinal.clock < limit := by
            have bound := evaluate_clock_le (first :: rest) sourceEnv source
            rw [sourceArgsRun] at bound
            exact Nat.lt_of_le_of_lt bound clock
          have requiredArgs := stateExtends_trans passFinal g argsG passGrowth argsExt
          have valuesRel : List.Forall₂ (ValueRelFuel relationFuel argsG allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          have fnEnv' := envRelFuel_mono fnEnv argsExt Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf argsExt Set.Subset.rfl argsGrowth
          have functionWfEval := fnWf argsG targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf argsReady.auxEmpty
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            rw [sourceFnRun] at functionWfEval
            have fnSafe : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have eq : result = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType eq
            obtain ⟨fnExtra, fnG, targetFnResult, targetFnFinal, fnExt, targetFnRun, fnRel, fnStates, fnStateWf,
              fnReady, fnCompiler, targetFnCompiler, fnOracle, fnGrowth⟩ :=
              fnIH targetFn middle fnTraversal argsG requiredArgs sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal argsClock
                sourceFnRun fnSafe (by simpa using fnEnv') fnEnvWf argsStateWf argsStates argsReady
                argsCompiler targetArgsCompiler argsOracle
            have prefixExt := stateExtends_trans g argsG fnG argsExt fnExt
            have prefixGrowth : ∀ key entry, target.code.lookup key = some entry → targetFnFinal.code.lookup key = some entry :=
              fun key entry found => fnGrowth key entry (argsGrowth key entry found)
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val values => simp [resultRel] at fnRel
              | err targetError =>
                have eq : result = .err error ∧ final = fnFinal := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := eq
                refine ⟨argsExtra + fnExtra, fnG, .err targetError, targetFnFinal, prefixExt, ?_, fnRel, fnStates, fnStateWf,
                  fnReady, fnCompiler, targetFnCompiler, fnOracle, prefixGrowth⟩
                have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
                  { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) fnExtra
                  targetArgsRun (by simp)
                have shiftedArgs' : evaluate targetArgs targetEnv
                    { target with clock := target.clock + (argsExtra + fnExtra) } =
                    (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra }) := by
                  simpa [Nat.add_assoc] using shiftedArgs
                rw [outEq]
                exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFn targetEnv
                  targetValues { target with clock := target.clock + (argsExtra + fnExtra) }
                  { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra } targetFnFinal targetError shiftedArgs' targetFnRun
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues sourceFnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra } targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel relationFuel fnG allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel relationFuel fnG allowed targetFnFinal.code) sourceValues targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h fnExt Set.Subset.rfl fnGrowth) valuesRel
                have fnClock : fnFinal.clock < limit := by
                  have bound := evaluate_clock_le [sourceFn] sourceEnv argsFinal
                  rw [sourceFnRun] at bound
                  exact Nat.lt_of_le_of_lt bound argsClock
                have appRun : evaluateApp (some address) fnValue sourceValues fnFinal = (result, final) := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using run
                have nonempty : sourceValues ≠ [] := by
                  have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
                  intro empty
                  simp [empty] at len
                obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
                  evaluateApp_known_full address fnValue sourceValues fnFinal final result nonempty appRun notType
                have sourceClosure' : destClosure targetFnFinal.maxApp (some address) fnValue sourceValues =
                    some (.fullApp sourceBody sourceBodyEnv sourceRest) := by simpa [← fnStates.2.2.1] using sourceClosure
                obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
                  destClosure_known_direct relationFuel fnG allowed targetFnFinal.code targetFnFinal.maxApp address fnValue targetFnValue
                    sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel' notAllowed
                have code : targetFnFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
                  unfold findCode at found
                  cases h : targetFnFinal.code.lookup (address + 1) with
                  | none => simp [h] at found
                  | some entry =>
                    rcases entry with ⟨arity, expression⟩
                    simp only [h, bind, Option.bind_some] at found
                    split at found
                    · rename_i same
                      simp only [Option.some.injEq, Prod.mk.injEq] at found
                      obtain ⟨_, rfl⟩ := found
                      rw [same]
                    · simp at found
                have targetClosure' : destClosure targetFnFinal.maxApp (some address) targetFnValue targetValues =
                    some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
                  simpa [valuesRel'.length_eq] using targetClosure
                have argumentWf : ValuesWellFormedFuel relationFuel fnG allowed targetFnFinal.code sourceValues :=
                  valuesWellFormedFuel_mono initialArgsWf.1 prefixExt Set.Subset.rfl prefixGrowth
                have functionWf : ValueWellFormedFuel relationFuel fnG allowed targetFnFinal.code fnValue := by
                  have valueWf : ValueWellFormedFuel relationFuel argsG allowed targetArgsFinal.code fnValue := by
                    cases functionWfEval.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf fnExt Set.Subset.rfl fnGrowth
                obtain ⟨appExtra, finalG, targetResult, targetFinal, appExt, targetRun, related, finalStates, finalWf, finalReady,
                  finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
                  appIH fnG fnValue targetFnValue sourceValues targetValues fnFinal targetFnFinal result final fnClock appRun notType
                    functionRel valuesRel' functionWf argumentWf fnStateWf fnStates fnReady fnCompiler targetFnCompiler fnOracle
                have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 targetArgs targetEnv
                  { target with clock := target.clock + argsExtra } targetArgsFinal (.val targetValues) (fnExtra + appExtra)
                  targetArgsRun (by simp)
                have shiftedArgs' : evaluate targetArgs targetEnv
                    { target with clock := target.clock + (argsExtra + (fnExtra + appExtra)) } =
                    (.val targetValues, { targetArgsFinal with clock := targetArgsFinal.clock + (fnExtra + appExtra) }) := by
                  simpa [Nat.add_assoc] using shiftedArgs
                have shiftedFn := (evaluate_addClock (C := C) (F := F)).1 [targetFn] targetEnv
                  { targetArgsFinal with clock := targetArgsFinal.clock + fnExtra } targetFnFinal
                  (.val [targetFnValue]) appExtra targetFnRun (by simp)
                have shiftedFn' : evaluate [targetFn] targetEnv
                    { targetArgsFinal with clock := targetArgsFinal.clock + (fnExtra + appExtra) } =
                    (.val [targetFnValue], { targetFnFinal with clock := targetFnFinal.clock + appExtra }) := by
                  simpa [Nat.add_assoc] using shiftedFn
                have targetEq := callsFuel_app_impure_target_eq traversalFuel trace stubTrace address sourceFn (first :: rest)
                  initial passFinal out targetFn targetArgs middle targetEnv targetValues targetFnValue
                  { target with clock := target.clock + (argsExtra + (fnExtra + appExtra)) }
                  { targetArgsFinal with clock := targetArgsFinal.clock + (fnExtra + appExtra) }
                  { targetFnFinal with clock := targetFnFinal.clock + appExtra }
                  stubEnv convertedBody passRun known impure argsTraversal fnTraversal shiftedArgs' shiftedFn'
                  (by simpa using code) (by simpa using targetClosure')
                exact ⟨argsExtra + (fnExtra + appExtra), finalG, targetResult, targetFinal, stateExtends_trans g fnG finalG prefixExt appExt,
                  targetEq.trans targetRun, related, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, fun key entry found => growth key entry (prefixGrowth key entry found)⟩

/-- Both known-location rewrite branches compose under the same clock
bound. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_known_growing_below_at {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  cases purity : ClosLang.pure sourceFn with
  | false =>
    exact callsFuel_app_impure_growing_below_at passFuel relationFuel traversalFuel limit compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g passGrowth sourceEnv targetEnv
      source target result final clock run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle
  | true =>
    exact callsFuel_app_pure_growing_below_at passFuel relationFuel traversalFuel limit compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g passGrowth sourceEnv targetEnv
      source target result final clock run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- Both known-location rewrite branches compose with target clock
allowances. Expression, application and well-formedness hypotheses remain
assumptions. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_known_growing_below_at_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, passFinal))
    (known : (sptLookup address passFinal.1).isSome = true) (notAllowed : address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed (some address))
    (g : State) (passGrowth : stateExtends passFinal g) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target) (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (oracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ extraClock finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv { target with clock := target.clock + extraClock } = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  cases purity : ClosLang.pure sourceFn with
  | false =>
    exact callsFuel_app_impure_growing_below_at_withClock passFuel relationFuel traversalFuel limit compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g passGrowth sourceEnv targetEnv
      source target result final clock run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle
  | true =>
    exact callsFuel_app_pure_growing_below_at_withClock passFuel relationFuel traversalFuel limit compiler allowed trace address sourceFn
      sourceArgs initial passFinal out passRun known purity notAllowed argsIH fnIH argsWf fnWf appIH g passGrowth sourceEnv targetEnv
      source target result final clock run notType envs envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- All application traversal branches compose under a clock bound and
above the final pass state. Child, application, and source well-formedness
hypotheses remain assumptions. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, passFinal))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address passFinal.1).isSome = true → address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelow (F := F) passFuel relationFuel limit compiler allowed location) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.app trace location sourceFn sourceArgs] [out] := by
  cases location with
  | none =>
    exact callsFuel_app_none_growing_below passFuel relationFuel traversalFuel limit compiler allowed trace
      sourceFn sourceArgs initial passFinal out passRun argsIH fnIH argsWf fnWf appIH
  | some address =>
    cases lookup : sptLookup address passFinal.1 with
    | none =>
      exact callsFuel_app_unknown_growing_below passFuel relationFuel traversalFuel limit compiler allowed trace address
        sourceFn sourceArgs initial passFinal out passRun lookup argsIH fnIH argsWf fnWf appIH
    | some value =>
      have known : (sptLookup address passFinal.1).isSome = true := by simp [lookup]
      intro g passGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
        sourceCompiler targetCompiler oracle
      exact callsFuel_app_known_growing_below_at passFuel relationFuel traversalFuel limit compiler allowed trace address
        sourceFn sourceArgs initial passFinal out passRun known (notAllowed address rfl known) argsIH fnIH argsWf fnWf appIH
        g passGrowth sourceEnv targetEnv source target result final clock run notType (by simpa using envs) envWf sourceWf
        states ready sourceCompiler targetCompiler oracle

/-- All application traversal branches compose with target clock allowances and
above the final pass state. Child, application, and source well-formedness
hypotheses remain assumptions. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial passFinal : State) (out : ClosLang.Exp)
    (passRun : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, passFinal))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address passFinal.1).isSome = true → address ∉ allowed)
    (argsIH : ∀ targetArgs middle, callsListFuel traversalFuel sourceArgs initial = some (targetArgs, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel traversalFuel sourceFn middle = some (targetFn, passFinal) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed [sourceFn] [targetFn])
    (argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state))
    (fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state))
    (appIH : GrowingAppSimClockBelowWithClock (F := F) passFuel relationFuel limit compiler allowed location) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.app trace location sourceFn sourceArgs] [out] := by
  cases location with
  | none =>
    exact callsFuel_app_none_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace
      sourceFn sourceArgs initial passFinal out passRun argsIH fnIH argsWf fnWf appIH
  | some address =>
    cases lookup : sptLookup address passFinal.1 with
    | none =>
      exact callsFuel_app_unknown_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace address
        sourceFn sourceArgs initial passFinal out passRun lookup argsIH fnIH argsWf fnWf appIH
    | some value =>
      have known : (sptLookup address passFinal.1).isSome = true := by simp [lookup]
      intro g passGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
        sourceCompiler targetCompiler oracle
      exact callsFuel_app_known_growing_below_at_withClock passFuel relationFuel traversalFuel limit compiler allowed trace address
        sourceFn sourceArgs initial passFinal out passRun known (notAllowed address rfl known) argsIH fnIH argsWf fnWf appIH
        g passGrowth sourceEnv targetEnv source target result final clock run notType (by simpa using envs) envWf sourceWf
        states ready sourceCompiler targetCompiler oracle

/-- An application traversal follows from simulations of its
argument and function traversals and the ordinary smaller-clock expression
induction. A general source evaluation well-formedness premise supplies the
argument, function, and closure-body obligations. Known-location rewrites require their location to be outside the open set. This is Flapjack-specific infrastructure. -/
theorem callsFuel_app_withClock_of_traversals {C F : Type}
    (passFuel relationFuel traversalFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address final.1).isSome = true → address ∉ allowed)
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (exprIH : ∀ callerClock, callerClock < limit → ∀ depth (before after : State)
      (body converted : ClosLang.Exp),
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before → wellFormed before →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel callerClock compiler after allowed [body] [converted])
    (evalWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate expressions env state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [.app trace location sourceFn sourceArgs] [out] := by
  have argsWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate sourceArgs env state) := by
    intro g code env state
    exact evalWf g code sourceArgs env state
  have fnWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [sourceFn] env state) := by
    intro g code env state
    exact evalWf g code [sourceFn] env state
  have bodyWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
      (index arity : Nat), recClosureRelFuel relationFuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate [body] env state) := by
    intro g code body _ _ _ _ _ _ _ _ _ env state
    exact evalWf g code [body] env state
  have appIH := growingAppSimClockBelowWithClock_of_traversals passFuel relationFuel limit compiler allowed location exprIH bodyWf
  exact callsFuel_app_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed trace location
    sourceFn sourceArgs initial final out run notAllowed argsIH fnIH argsWf fnWf appIH

/-- Under the HOL-shaped open/known disjointness invariant, every known
application location satisfies the direct-call side condition. This is
Flapjack-specific infrastructure. -/
theorem known_application_not_open (allowed : Set Nat) (state : State)
    (disjoint : Disjoint allowed (sptDomain state.1)) (location : Option Nat) :
    ∀ address, location = some address → (sptLookup address state.1).isSome = true → address ∉ allowed := by
  intro address _ known member
  have inDomain : sptDomain state.1 address := by simpa [sptDomain] using known
  exact Set.disjoint_left.mp disjoint member inDomain

/-- With open/known disjointness, the complete application traversal case
uses the ordinary smaller-clock traversal induction. Evaluation
well-formedness remains a premise. This is Flapjack-specific infrastructure,
not a HOL theorem port. -/
theorem callsFuel_app_withClock_of_disjoint {C F : Type}
    (passFuel relationFuel traversalFuel limit : Nat) (compiler : ClosSem.Compiler C)
    (allowed : Set Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (traversalFuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (disjoint : Disjoint allowed (sptDomain final.1))
    (argsIH : ∀ target middle, callsListFuel traversalFuel sourceArgs initial = some (target, middle) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed sourceArgs target)
    (fnIH : ∀ target middle, callsFuel traversalFuel sourceFn middle = some (target, final) →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed [sourceFn] [target])
    (exprIH : ∀ callerClock, callerClock < limit → ∀ depth (before after : State)
      (body converted : ClosLang.Exp),
      callsFuel depth body before = some (converted, after) →
      (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) before → wellFormed before →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel callerClock compiler after allowed [body] [converted])
    (evalWf : ∀ (g : State) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
      (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
      OracleAuxEmpty state.compileOracle → EvalWellFormedFuel relationFuel g allowed code (evaluate expressions env state)) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed
      [.app trace location sourceFn sourceArgs] [out] := by
  exact callsFuel_app_withClock_of_traversals passFuel relationFuel traversalFuel limit compiler allowed trace location
    sourceFn sourceArgs initial final out run (known_application_not_open allowed final disjoint location)
    argsIH fnIH exprIH evalWf

/-- Appending older auxiliary code preserves the generated pass state when
the combined code has distinct labels. -/
theorem stateExtends_append_aux (known : NumSet) (generated old : List (Nat × (Nat × ClosLang.Exp)))
    (distinct : ((generated ++ old).map Prod.fst).Nodup) :
    stateExtends (known, generated) (known, generated ++ old) := by
  refine ⟨?_, ?_, distinct⟩
  · intro key member
    exact ⟨member, rfl⟩
  · intro key value lookup
    exact logicalAssocLookup_append_hit generated old key value lookup

/-- The function-creation traversal has a simulation at every runtime state
extending its generated pass state, under the source location conditions. -/
theorem callsFuel_fn_growing_from {C F : Type} (passFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (name : Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body out : ClosLang.Exp) (initial passFinal : State)
    (passRun : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, passFinal))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed) :
    GrowingExprsSimFrom (F := F) passFuel (traversalFuel + 1) compiler passFinal allowed
      [.fn name (some loc) none arity body] [out] := by
  intro g passGrowth sourceEnv targetEnv source target result final run notType envs _ sourceWf states ready
    sourceCompiler targetCompiler oracle
  obtain ⟨targetResult, targetFinal, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    callsFuel_fn_growing_at passFuel traversalFuel compiler allowed name loc arity body out initial passFinal g
      passRun initialWf locations annotations distinct fresh passGrowth coverage sourceEnv targetEnv source target result
      final run notType (by simpa using envs) sourceWf states ready sourceCompiler targetCompiler oracle
  exact ⟨g, targetResult, targetFinal, stateExtends_refl g ready.well.2, targetRun, related, finalStates,
    finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Recursive binding simulation only requires its body's simulation above
the final pass state, rather than for unrelated runtime compiler states. -/
theorem callsFuel_letrec_growing_from {C F : Type} (passFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (names : List Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body out : ClosLang.Exp) (initial passFinal : State)
    (passRun : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, passFinal))
    (bodyIH : ∀ targetBody middle, callsFuel traversalFuel body middle = some (targetBody, passFinal) →
      GrowingExprsSimFrom (F := F) passFuel traversalFuel compiler passFinal allowed [body] [targetBody])
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed) :
    GrowingExprsSimFrom (F := F) passFuel traversalFuel compiler passFinal allowed
      [.letrec names (some loc) none fns body] [out] := by
  intro g passGrowth sourceEnv targetEnv source target result final run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  exact callsFuel_letrec_growing_at passFuel traversalFuel compiler allowed names loc fns body out initial passFinal g
    passRun bodyIH initialWf locations annotations distinct fresh passGrowth coverage sourceEnv targetEnv source target
    result final run notType (by simpa using envs) envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- Clock-bounded recursive-binding simulation. Its body simulation and
location assumptions remain open. This is Flapjack-specific infrastructure. -/
theorem callsFuel_letrec_growing_below_at {C F : Type} (passFuel traversalFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (names : List Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body out : ClosLang.Exp) (initial passFinal g : State)
    (passRun : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, passFinal))
    (bodyIH : ∀ targetBody middle, callsFuel traversalFuel body middle = some (targetBody, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [body] [targetBody])
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (passGrowth : stateExtends passFinal g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F) (clock : source.clock < limit)
    (run : evaluate [.letrec names (some loc) none fns body] sourceEnv source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (envs : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel relationFuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (states : StateRelFuel relationFuel g allowed source target)
    (ready : IncrementalInstallReady g source target)
    (sourceCompiler : source.compile = compileIncFuelCallback passFuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle passFuel source.compileOracle) :
    ∃ finalG targetResult targetFinal,
      stateExtends g finalG ∧ evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback passFuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle passFuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨targetFns, targetBody, middle, rfl, bodyPass, closure⟩ :=
    callsFuel_letrec_relation_atFuel traversalFuel relationFuel names loc fns body out initial passFinal g allowed target.code passRun
      initialWf locations annotations distinct fresh passGrowth coverage ready.included
  have valid : fns.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
    by_contra invalid
    have bad : result = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst run.symm
    exact notType bad
  have targetValid : targetFns.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
    have arities := recClosureRelFuel_arities relationFuel g allowed target.code loc fns targetFns closure
    have same := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simp only [List.all_map, Function.comp_def] at same
    rw [← states.2.2.1, same]
    exact valid
  have bodyEnv := envRelFuel_letrec_enter names loc fns targetFns targetBody closure envs
  have bodyRun : evaluate [body]
      ((List.range fns.length).map (fun i => .recclosure (some loc) [] sourceEnv fns i) ++ sourceEnv)
      source = (result, final) := by simpa [evaluate, valid] using run
  have bodyEnvWf : ValuesWellFormedFuel relationFuel g allowed target.code
      ((List.range fns.length).map (fun i => .recclosure (some loc) [] sourceEnv fns i) ++ sourceEnv) :=
    valuesWellFormedFuel_append (recClosureBundle_wellFormedFuel loc sourceEnv fns targetFns envWf closure) envWf
  obtain ⟨finalG, targetResult, targetFinal, extended, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    bodyIH targetBody middle bodyPass g passGrowth _ _ source target result final clock bodyRun notType (by simpa using bodyEnv)
      bodyEnvWf sourceWf states ready sourceCompiler targetCompiler targetOracle
  refine ⟨finalG, targetResult, targetFinal, extended, ?_, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩
  simpa [evaluate, targetValid] using targetRun

/-- Recursive binding composes with a clock-bounded body simulation. Traversal and relation fuel are independent. This is
Flapjack-specific simulation infrastructure. -/
theorem callsFuel_letrec_growing_below {C F : Type} (passFuel traversalFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (names : List Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body out : ClosLang.Exp) (initial passFinal : State)
    (passRun : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, passFinal))
    (bodyIH : ∀ targetBody middle, callsFuel traversalFuel body middle = some (targetBody, passFinal) →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed [body] [targetBody])
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.letrec names (some loc) none fns body] [out] := by
  intro g passGrowth sourceEnv targetEnv source target result final clock run notType envs envWf sourceWf states ready
    sourceCompiler targetCompiler oracle
  exact callsFuel_letrec_growing_below_at passFuel traversalFuel relationFuel limit compiler allowed names loc fns body out initial passFinal g
    passRun bodyIH initialWf locations annotations distinct fresh passGrowth coverage sourceEnv targetEnv source target
    result final clock run notType (by simpa using envs) envWf sourceWf states ready sourceCompiler targetCompiler oracle

/-- Clock-bounded function creation at arbitrary relation fuel. This is
Flapjack-specific bounded-adapter infrastructure. -/
theorem callsFuel_fn_growing_below {C F : Type} (passFuel traversalFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (name : Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body out : ClosLang.Exp) (initial passFinal : State)
    (passRun : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, passFinal))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain passFinal.1 k → k ∈ allowed) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler passFinal allowed
      [.fn name (some loc) none arity body] [out] := by
  intro g passGrowth sourceEnv targetEnv source target result final _ run notType envs _ sourceWf states ready
    sourceCompiler targetCompiler oracle
  obtain ⟨targetResult, targetFinal, targetRun, related, finalStates, finalWf, finalReady,
    finalCompiler, targetFinalCompiler, finalOracle, growth⟩ :=
    callsFuel_fn_growing_atFuel passFuel traversalFuel relationFuel compiler allowed name loc arity body out initial passFinal g
      passRun initialWf locations annotations distinct fresh passGrowth coverage sourceEnv targetEnv source target result
      final run notType (by simpa using envs) sourceWf states ready sourceCompiler targetCompiler oracle
  exact ⟨g, targetResult, targetFinal, stateExtends_refl g ready.well.2, targetRun, related, finalStates,
    finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, growth⟩

/-- Simulations above a common pass state compose in evaluation order; the
required pass state remains below each subsequently grown runtime state. -/
theorem growingExprsSimFrom_of_forall₂ {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (sims : List.Forall₂ (fun source target =>
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed [source] [target])
      sourceExps targetExps) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler required allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro g _ sourceEnv targetEnv source target result final run _ _ _ stateWf states ready sourceCompiler targetCompiler oracle
    have eq : result = .val [] ∧ final = source := by simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .val [], target, stateExtends_refl g ready.well.2, by simp [evaluate], .nil,
      states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headSim tailSims tailIH =>
    intro g requiredGrowth sourceEnv targetEnv source target result final run notType envs envWf stateWf states ready
      sourceCompiler targetCompiler oracle
    have headEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headSafe : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have eq : result = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType eq
      obtain ⟨headG, targetHeadResult, targetHeadFinal, headExt, targetHeadRun, headRel, headStates,
        headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩ :=
        headSim g requiredGrowth sourceEnv targetEnv source target headResult headFinal headRun headSafe headEnv envWf
          stateWf states ready sourceCompiler targetCompiler oracle
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have eq : result = .err error ∧ final = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨headG, .err targetError, targetHeadFinal, headExt,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv target targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv target targetHeadFinal targetValues targetHeadRun
          have valueRel : ValueRelFuel relationFuel headG allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv headExt Set.Subset.rfl headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf headExt Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailSafe : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            have requiredHead := stateExtends_trans required g headG requiredGrowth headExt
            obtain ⟨finalG, targetTailResult, targetFinal, tailExt, targetTailRun, tailRel, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, tailGrowth⟩ :=
              tailIH headG requiredHead sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal tailRun tailSafe
                tailEnv' tailEnvWf headWf headStates headReady headCompiler targetHeadCompiler headOracle
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv target targetHeadFinal targetValue targetHeadRun
            rw [targetTailRun] at targetOuter
            have combinedExt := stateExtends_trans g headG finalG headExt tailExt
            have combinedGrowth : ∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry :=
              fun key entry found => tailGrowth key entry (headGrowth key entry found)
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨finalG, .err targetError, targetFinal, combinedExt, targetOuter, tailRel, finalStates,
                  finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valueRel tailExt Set.Subset.rfl tailGrowth
                exact ⟨finalG, .val (targetValue :: targetTailValues), targetFinal, combinedExt,
                  targetOuter, .cons grownValue tailRel, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, combinedGrowth⟩

/-- Clock-bounded single-expression simulations compose in evaluation order.
This is Flapjack-specific simulation infrastructure. -/
theorem growingExprsSimFromBelow_of_forall₂ {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (sims : List.Forall₂ (fun source target =>
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed [source] [target])
      sourceExps targetExps) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler required allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro g _ sourceEnv targetEnv source target result final clock run _ _ _ stateWf states ready sourceCompiler targetCompiler oracle
    have eq : result = .val [] ∧ final = source := by simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨g, .val [], target, stateExtends_refl g ready.well.2, by simp [evaluate], .nil,
      states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headSim tailSims tailIH =>
    intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf stateWf states ready
      sourceCompiler targetCompiler oracle
    have headEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headSafe : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have eq : result = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType eq
      obtain ⟨headG, targetHeadResult, targetHeadFinal, headExt, targetHeadRun, headRel, headStates,
        headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩ :=
        headSim g requiredGrowth sourceEnv targetEnv source target headResult headFinal clock headRun headSafe headEnv envWf
          stateWf states ready sourceCompiler targetCompiler oracle
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have eq : result = .err error ∧ final = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨headG, .err targetError, targetHeadFinal, headExt,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv target targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv target targetHeadFinal targetValues targetHeadRun
          have valueRel : ValueRelFuel relationFuel headG allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv headExt Set.Subset.rfl headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf headExt Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailSafe : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            have headClock : headFinal.clock < limit := by
              have bound := evaluate_clock_le [sourceHead] sourceEnv source
              rw [headRun] at bound
              exact Nat.lt_of_le_of_lt bound clock
            have requiredHead := stateExtends_trans required g headG requiredGrowth headExt
            obtain ⟨finalG, targetTailResult, targetFinal, tailExt, targetTailRun, tailRel, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, tailGrowth⟩ :=
              tailIH headG requiredHead sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal headClock tailRun tailSafe
                tailEnv' tailEnvWf headWf headStates headReady headCompiler targetHeadCompiler headOracle
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv target targetHeadFinal targetValue targetHeadRun
            rw [targetTailRun] at targetOuter
            have combinedExt := stateExtends_trans g headG finalG headExt tailExt
            have combinedGrowth : ∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry :=
              fun key entry found => tailGrowth key entry (headGrowth key entry found)
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨finalG, .err targetError, targetFinal, combinedExt, targetOuter, tailRel, finalStates,
                  finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valueRel tailExt Set.Subset.rfl tailGrowth
                exact ⟨finalG, .val (targetValue :: targetTailValues), targetFinal, combinedExt,
                  targetOuter, .cons grownValue tailRel, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, combinedGrowth⟩

/-- Clock-allowing single-expression simulations compose through list
evaluation. The allowances are added after extending a successful head run.
This is Flapjack-specific simulation infrastructure, not a HOL theorem port. -/
theorem growingExprsSimFromBelowWithClock_of_forall₂ {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (sims : List.Forall₂ (fun source target =>
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed [source] [target])
      sourceExps targetExps) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler required allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro g _ sourceEnv targetEnv source target result final clock run _ _ _ stateWf states ready sourceCompiler targetCompiler oracle
    have eq : result = .val [] ∧ final = source := by simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨0, g, .val [], target, stateExtends_refl g ready.well.2, by simp [evaluate], .nil,
      states, stateWf, ready, sourceCompiler, targetCompiler, oracle, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headSim tailSims tailIH =>
    intro g requiredGrowth sourceEnv targetEnv source target result final clock run notType envs envWf stateWf states ready
      sourceCompiler targetCompiler oracle
    have headEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headSafe : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have eq : result = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType eq
      obtain ⟨headExtra, headG, targetHeadResult, targetHeadFinal, headExt, targetHeadRun, headRel, headStates,
        headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩ :=
        headSim g requiredGrowth sourceEnv targetEnv source target headResult headFinal clock headRun headSafe headEnv envWf
          stateWf states ready sourceCompiler targetCompiler oracle
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have eq : result = .err error ∧ final = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨headExtra, headG, .err targetError, targetHeadFinal, headExt,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv { target with clock := target.clock + headExtra } targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv { target with clock := target.clock + headExtra } targetHeadFinal targetValues targetHeadRun
          have valueRel : ValueRelFuel relationFuel headG allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv headExt Set.Subset.rfl headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf headExt Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailSafe : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            have headClock : headFinal.clock < limit := by
              have bound := evaluate_clock_le [sourceHead] sourceEnv source
              rw [headRun] at bound
              exact Nat.lt_of_le_of_lt bound clock
            have requiredHead := stateExtends_trans required g headG requiredGrowth headExt
            obtain ⟨tailExtra, finalG, targetTailResult, targetFinal, tailExt, targetTailRun, tailRel, finalStates,
              finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, tailGrowth⟩ :=
              tailIH headG requiredHead sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal headClock tailRun tailSafe
                tailEnv' tailEnvWf headWf headStates headReady headCompiler targetHeadCompiler headOracle
            have shiftedHead := (evaluate_addClock (C := C) (F := F)).1 [targetHead] targetEnv
              { target with clock := target.clock + headExtra } targetHeadFinal (.val [targetValue]) tailExtra
              targetHeadRun (by simp)
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv
              { target with clock := target.clock + (headExtra + tailExtra) }
              { targetHeadFinal with clock := targetHeadFinal.clock + tailExtra } targetValue
              (by simpa [Nat.add_assoc] using shiftedHead)
            rw [targetTailRun] at targetOuter
            have combinedExt := stateExtends_trans g headG finalG headExt tailExt
            have combinedGrowth : ∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry :=
              fun key entry found => tailGrowth key entry (headGrowth key entry found)
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨headExtra + tailExtra, finalG, .err targetError, targetFinal, combinedExt, targetOuter, tailRel, finalStates,
                  finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valueRel tailExt Set.Subset.rfl tailGrowth
                exact ⟨headExtra + tailExtra, finalG, .val (targetValue :: targetTailValues), targetFinal, combinedExt,
                  targetOuter, .cons grownValue tailRel, finalStates, finalWf, finalReady, finalCompiler,
                  targetFinalCompiler, finalOracle, combinedGrowth⟩

/-- Single-expression simulations compose while threading the growing open
set and summing target-clock allowances. This is Flapjack-specific simulation
infrastructure, not a HOL theorem port. -/
theorem growingExprsSimFromBelowWithOpenClock_of_forall₂ {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (required : State) {sourceExps targetExps : List ClosLang.Exp}
    (sims : List.Forall₂ (fun source target =>
      GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required [source] [target])
      sourceExps targetExps) :
    GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler required sourceExps targetExps := by
  induction sims with
  | nil =>
    intro g _ allowed sourceEnv targetEnv source target result final clock run _ _ _ stateWf states ready
      disjoint avoids sourceCompiler targetCompiler oracle
    have eq : result = .val [] ∧ final = source := by simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨0, g, allowed, .val [], target, stateExtends_refl g ready.well.2, Set.Subset.rfl,
      disjoint, avoids, by simp [evaluate], .nil, states, stateWf, ready, sourceCompiler,
      targetCompiler, oracle, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headSim tailSims tailIH =>
    intro g requiredGrowth allowed sourceEnv targetEnv source target result final clock run notType envs envWf stateWf states ready
      disjoint avoids sourceCompiler targetCompiler oracle
    have headEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headSafe : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have eq : result = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType eq
      obtain ⟨headExtra, headG, headAllowed, targetHeadResult, targetHeadFinal, headExt, headAllowedGrowth,
        headDisjoint, headAvoids, targetHeadRun, headRel, headStates, headWf, headReady,
        headCompiler, targetHeadCompiler, headOracle, headGrowth⟩ :=
        headSim g requiredGrowth allowed sourceEnv targetEnv source target headResult headFinal clock headRun headSafe
          headEnv envWf stateWf states ready disjoint avoids sourceCompiler targetCompiler oracle
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have eq : result = .err error ∧ final = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := eq
          exact ⟨headExtra, headG, headAllowed, .err targetError, targetHeadFinal, headExt,
            headAllowedGrowth, headDisjoint, headAvoids,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv { target with clock := target.clock + headExtra }
              targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headWf, headReady, headCompiler, targetHeadCompiler, headOracle, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv
            { target with clock := target.clock + headExtra } targetHeadFinal targetValues targetHeadRun
          have valueRel : ValueRelFuel relationFuel headG headAllowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel relationFuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv headExt headAllowedGrowth headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf headExt headAllowedGrowth headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailSafe : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            have headClock : headFinal.clock < limit := by
              have bound := evaluate_clock_le [sourceHead] sourceEnv source
              rw [headRun] at bound
              exact Nat.lt_of_le_of_lt bound clock
            have requiredHead := stateExtends_trans required g headG requiredGrowth headExt
            obtain ⟨tailExtra, finalG, finalAllowed, targetTailResult, targetFinal, tailExt, tailAllowedGrowth,
              finalDisjoint, finalAvoids, targetTailRun, tailRel, finalStates, finalWf, finalReady,
              finalCompiler, targetFinalCompiler, finalOracle, tailGrowth⟩ :=
              tailIH headG requiredHead headAllowed sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal
                headClock tailRun tailSafe tailEnv' tailEnvWf headWf headStates headReady headDisjoint headAvoids
                headCompiler targetHeadCompiler headOracle
            have shiftedHead := (evaluate_addClock (C := C) (F := F)).1 [targetHead] targetEnv
              { target with clock := target.clock + headExtra } targetHeadFinal (.val [targetValue]) tailExtra
              targetHeadRun (by simp)
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv
              { target with clock := target.clock + (headExtra + tailExtra) }
              { targetHeadFinal with clock := targetHeadFinal.clock + tailExtra } targetValue
              (by simpa [Nat.add_assoc] using shiftedHead)
            rw [targetTailRun] at targetOuter
            have combinedExt := stateExtends_trans g headG finalG headExt tailExt
            have combinedAllowed := Set.Subset.trans headAllowedGrowth tailAllowedGrowth
            have combinedGrowth : ∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry :=
              fun key entry found => tailGrowth key entry (headGrowth key entry found)
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨headExtra + tailExtra, finalG, finalAllowed, .err targetError, targetFinal,
                  combinedExt, combinedAllowed, finalDisjoint, finalAvoids, targetOuter, tailRel, finalStates,
                  finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valueRel tailExt tailAllowedGrowth tailGrowth
                exact ⟨headExtra + tailExtra, finalG, finalAllowed, .val (targetValue :: targetTailValues), targetFinal,
                  combinedExt, combinedAllowed, finalDisjoint, finalAvoids, targetOuter, .cons grownValue tailRel,
                  finalStates, finalWf, finalReady, finalCompiler, targetFinalCompiler, finalOracle, combinedGrowth⟩

/-- An open-location list simulation supplies the induction hypothesis for an
installed program with an empty environment. -/
theorem growingExprsSimFromBelowWithOpenClock_installedBelow {C F : Type}
    (passFuel relationFuel limit : Nat) (compiler : ClosSem.Compiler C) (g : State)
    (allowed : Set Nat) (program targetProgram : List ClosLang.Exp)
    (sim : GrowingExprsSimFromBelowWithOpenClock (F := F) passFuel relationFuel limit compiler g program targetProgram) :
    InstalledProgramSimBelowWithOpenClock (C := C) (F := F) passFuel relationFuel limit compiler g allowed program targetProgram := by
  intro source target result final clock run notType sourceWf states ready disjoint avoids
    sourceCompiler targetCompiler oracle
  have envs : EnvRelFuel relationFuel g allowed target.code [] [] 0 (targetProgram.map (0, ·)) := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel]
  exact sim g (stateExtends_refl g ready.well.2) allowed [] [] source target result final clock run notType
    envs .nil sourceWf states ready disjoint avoids sourceCompiler targetCompiler oracle

/-- A successful list traversal composes expression simulations that need
their own generated pass states, using label freshness to show that each
intermediate state extends into the final pass state. -/
theorem callsListFuel_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler after allowed [expression] [output]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed source target := by
  apply growingExprsSimFrom_of_forall₂ passFuel relationFuel compiler final allowed
  induction traversalFuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp e ++ codeLocations es).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp e ++ codeLocations es) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp e) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations es) middle := by
        have labels := callsFuel_labelsBound depth e initial middle e' headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [e] initial = some ([e'], middle) := by
        simp [callsListFuel, headRun]
      have middleWf := callsListFuel_wellFormed (depth + 1) [e] initial middle [e'] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialWf
      have boundedTail : callsListBounded depth es middle = some (es', next) := by
        simp [callsListBounded, tailRun]
      have tailExt := callsListBounded_stateExtends depth es middle next es' boundedTail tailDistinct middleFresh middleWf.2
      refine List.Forall₂.cons ?_ ?_
      · exact growingExprsSimFrom_mono passFuel relationFuel compiler middle next allowed [e] [e'] tailExt
          (exprIH depth (by omega) e e' initial middle headRun headDistinct headFresh initialWf
            (eligibleIH depth (by omega) e e' initial middle (by simp) headRun))
      · apply ih es es' middle next tailRun tailDistinct middleFresh middleWf
        · intro n bound expression output before after member exprRun
          exact eligibleIH n (by omega) expression output before after (by simp [member]) exprRun
        · intro n bound expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr
          exact exprIH n (by omega) expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr

/-- The production retry wrapper inherits the simulation above its final
pass state, whether its initial traversal succeeds or it uses the structural
retry budget. -/
theorem callsListBounded_growing_from {C F : Type} (passFuel relationFuel traversalFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler after allowed [expression] [output]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler final allowed source target := by
  unfold callsListBounded at run
  cases first : callsListFuel traversalFuel source initial with
  | none =>
    simp only [first] at run
    exact callsListFuel_growing_from passFuel relationFuel _ compiler allowed source target initial final
      run distinct fresh initialWf eligible eligibleIH exprIH
  | some result =>
    have equal : result = (target, final) := by simpa [first] using run
    subst result
    apply callsListFuel_growing_from passFuel relationFuel traversalFuel compiler allowed source target initial final
      first distinct fresh initialWf eligible
    · intro depth bound expression output before after member expressionRun
      exact eligibleIH depth (by omega) expression output before after member expressionRun
    · intro depth bound expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr
      exact exprIH depth (by omega) expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr

/-- Clock-bounded list traversal and retry composition. These are
Flapjack-specific simulation lemmas. -/
theorem callsListFuel_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed source target := by
  apply growingExprsSimFromBelow_of_forall₂ passFuel relationFuel limit compiler final allowed
  induction traversalFuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp e ++ codeLocations es).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp e ++ codeLocations es) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp e) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations es) middle := by
        have labels := callsFuel_labelsBound depth e initial middle e' headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [e] initial = some ([e'], middle) := by
        simp [callsListFuel, headRun]
      have middleWf := callsListFuel_wellFormed (depth + 1) [e] initial middle [e'] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialWf
      have boundedTail : callsListBounded depth es middle = some (es', next) := by
        simp [callsListBounded, tailRun]
      have tailExt := callsListBounded_stateExtends depth es middle next es' boundedTail tailDistinct middleFresh middleWf.2
      refine List.Forall₂.cons ?_ ?_
      · exact growingExprsSimFromBelow_mono_state passFuel relationFuel limit compiler middle next allowed [e] [e'] tailExt
          (exprIH depth (by omega) e e' initial middle headRun headDistinct headFresh initialWf
            (eligibleIH depth (by omega) e e' initial middle (by simp) headRun))
      · apply ih es es' middle next tailRun tailDistinct middleFresh middleWf
        · intro n bound expression output before after member exprRun
          exact eligibleIH n (by omega) expression output before after (by simp [member]) exprRun
        · intro n bound expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr
          exact exprIH n (by omega) expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr

/-- The production retry wrapper inherits the simulation above its final
pass state, whether its initial traversal succeeds or it uses the structural
retry budget. -/
theorem callsListBounded_growing_below {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler final allowed source target := by
  unfold callsListBounded at run
  cases first : callsListFuel traversalFuel source initial with
  | none =>
    simp only [first] at run
    exact callsListFuel_growing_below passFuel relationFuel _ limit compiler allowed source target initial final
      run distinct fresh initialWf eligible eligibleIH exprIH
  | some result =>
    have equal : result = (target, final) := by simpa [first] using run
    subst result
    apply callsListFuel_growing_below passFuel relationFuel traversalFuel limit compiler allowed source target initial final
      first distinct fresh initialWf eligible
    · intro depth bound expression output before after member expressionRun
      exact eligibleIH depth (by omega) expression output before after member expressionRun
    · intro depth bound expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr
      exact exprIH depth (by omega) expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr

/-- Clock-allowing list traversal and retry composition. Expression
cases and eligibility remain assumptions; this is Flapjack-specific
simulation infrastructure. -/
theorem callsListFuel_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < traversalFuel → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed source target := by
  apply growingExprsSimFromBelowWithClock_of_forall₂ passFuel relationFuel limit compiler final allowed
  induction traversalFuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp e ++ codeLocations es).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp e ++ codeLocations es) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp e) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations es) middle := by
        have labels := callsFuel_labelsBound depth e initial middle e' headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [e] initial = some ([e'], middle) := by
        simp [callsListFuel, headRun]
      have middleWf := callsListFuel_wellFormed (depth + 1) [e] initial middle [e'] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialWf
      have boundedTail : callsListBounded depth es middle = some (es', next) := by
        simp [callsListBounded, tailRun]
      have tailExt := callsListBounded_stateExtends depth es middle next es' boundedTail tailDistinct middleFresh middleWf.2
      refine List.Forall₂.cons ?_ ?_
      · exact growingExprsSimFromBelowWithClock_mono_state passFuel relationFuel limit compiler middle next allowed [e] [e'] tailExt
          (exprIH depth (by omega) e e' initial middle headRun headDistinct headFresh initialWf
            (eligibleIH depth (by omega) e e' initial middle (by simp) headRun))
      · apply ih es es' middle next tailRun tailDistinct middleFresh middleWf
        · intro n bound expression output before after member exprRun
          exact eligibleIH n (by omega) expression output before after (by simp [member]) exprRun
        · intro n bound expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr
          exact exprIH n (by omega) expression output before after exprRun exprDistinct exprFresh beforeWf eligibleExpr

/-- The production retry wrapper inherits the simulation above its final
pass state, whether its initial traversal succeeds or it uses the structural
retry budget. -/
theorem callsListBounded_growing_below_withClock {C F : Type} (passFuel relationFuel traversalFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded traversalFuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      expression ∈ source → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max traversalFuel (listBudget source + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler final allowed source target := by
  unfold callsListBounded at run
  cases first : callsListFuel traversalFuel source initial with
  | none =>
    simp only [first] at run
    exact callsListFuel_growing_below_withClock passFuel relationFuel _ limit compiler allowed source target initial final
      run distinct fresh initialWf eligible eligibleIH exprIH
  | some result =>
    have equal : result = (target, final) := by simpa [first] using run
    subst result
    apply callsListFuel_growing_below_withClock passFuel relationFuel traversalFuel limit compiler allowed source target initial final
      first distinct fresh initialWf eligible
    · intro depth bound expression output before after member expressionRun
      exact eligibleIH depth (by omega) expression output before after member expressionRun
    · intro depth bound expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr
      exact exprIH depth (by omega) expression output before after expressionRun expressionDistinct expressionFresh beforeWf eligibleExpr

/-- The incremental pass exposes a list simulation above its emitted state,
subject to the expression-case induction and source conditions. The premise
`wellFormed (known, [])` restricts this result to an empty known-location
domain. The subsequent `compileIncFuel_growing_with_existing` handles an
existing well-formed auxiliary-code list. -/
theorem compileIncFuel_growing_from {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (known : NumSet) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel known program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup) (initialWf : wellFormed ((known, []) : State))
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler after allowed [expression] [output]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler (nextKnown, converted.2) allowed program.1 converted.1 := by
  have traversal := compileIncFuel_traversal passFuel known program nextKnown converted run
  have fresh : LabelsFresh (codeLocations program.1) (known, []) := by simp [LabelsFresh]
  exact callsListBounded_growing_from passFuel relationFuel passFuel compiler allowed program.1 converted.1
    (known, []) (nextKnown, converted.2) traversal distinct fresh initialWf eligible eligibleIH exprIH

/-- Incremental conversion also admits a simulation above its emitted code
merged with a well-formed existing auxiliary state. The expression cases and
their eligibility conditions remain hypotheses of this composition lemma. -/
theorem compileIncFuel_growing_with_existing {C F : Type} (passFuel relationFuel : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler after allowed [expression] [output]) :
    GrowingExprsSimFrom (F := F) passFuel relationFuel compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  have traversal := compileIncFuel_traversal passFuel g.1 program nextKnown converted run
  have appended := callsListBounded_appendAux passFuel program.1 (g.1, []) g.2
  have merged : callsListBounded passFuel program.1 g =
      some (converted.1, (nextKnown, converted.2 ++ g.2)) := by
    simpa [appendAux, traversal] using appended
  exact callsListBounded_growing_from passFuel relationFuel passFuel compiler allowed program.1 converted.1
    g (nextKnown, converted.2 ++ g.2) merged distinct fresh initialWf eligible eligibleIH exprIH

/-- Clock-bounded simulation of incremental conversion with existing code.
The expression induction and eligibility remain assumptions. This is
Flapjack-specific simulation infrastructure. -/
theorem compileIncFuel_growing_below_with_existing {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  have traversal := compileIncFuel_traversal passFuel g.1 program nextKnown converted run
  have appended := callsListBounded_appendAux passFuel program.1 (g.1, []) g.2
  have merged : callsListBounded passFuel program.1 g =
      some (converted.1, (nextKnown, converted.2 ++ g.2)) := by
    simpa [appendAux, traversal] using appended
  exact callsListBounded_growing_below passFuel relationFuel passFuel limit compiler allowed program.1 converted.1
    g (nextKnown, converted.2 ++ g.2) merged distinct fresh initialWf eligible eligibleIH exprIH

/-- Incremental conversion composes clock-allowing expression cases at
the merged compiler state. The expression induction remains an assumption.
This is Flapjack-specific infrastructure, not a HOL theorem port. -/
theorem compileIncFuel_growing_below_with_existing_clock {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  have traversal := compileIncFuel_traversal passFuel g.1 program nextKnown converted run
  have appended := callsListBounded_appendAux passFuel program.1 (g.1, []) g.2
  have merged : callsListBounded passFuel program.1 g =
      some (converted.1, (nextKnown, converted.2 ++ g.2)) := by
    simpa [appendAux, traversal] using appended
  exact callsListBounded_growing_below_withClock passFuel relationFuel passFuel limit compiler allowed program.1 converted.1
    g (nextKnown, converted.2 ++ g.2) merged distinct fresh initialWf eligible eligibleIH exprIH

/-- A successful incremental pass supplies the installed-program simulation
at its merged compiler state, assuming the expression-case induction and its
eligibility conditions. This is Flapjack-specific infrastructure. -/
theorem compileIncFuel_installedBelow_with_existing {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) passFuel relationFuel compiler after allowed [expression] [output]) :
    InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel limit compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  apply growingExprsSimFrom_installedBelow
  exact compileIncFuel_growing_with_existing passFuel relationFuel compiler allowed g program nextKnown converted
    run distinct fresh initialWf eligible eligibleIH exprIH

/-- A clock-bounded expression-case induction supplies the installed
program simulation. This is Flapjack-specific simulation infrastructure. -/
theorem compileIncFuel_installedBelow_from_bounded_cases {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelow (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    InstalledProgramSimBelow (C := C) (F := F) passFuel relationFuel limit compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  apply growingExprsSimFromBelow_installedBelow
  exact compileIncFuel_growing_below_with_existing passFuel relationFuel limit compiler allowed g program nextKnown converted
    run distinct fresh initialWf eligible eligibleIH exprIH

/-- Clock-allowing expression cases supply clock-allowing installed-program
simulation at the merged pass state. This is Flapjack-specific infrastructure;
the expression induction remains open. -/
theorem compileIncFuel_installedBelow_withClock_from_cases {C F : Type} (passFuel relationFuel limit : Nat)
    (compiler : ClosSem.Compiler C) (allowed : Set Nat) (g : State) (program : ClosSem.Program)
    (nextKnown : NumSet) (converted : ClosSem.Program)
    (run : compileIncFuel? passFuel g.1 program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup)
    (fresh : LabelsFresh (codeLocations program.1) g) (initialWf : wellFormed g)
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      expression ∈ program.1 → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max passFuel (listBudget program.1 + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelowWithClock (F := F) passFuel relationFuel limit compiler after allowed [expression] [output]) :
    InstalledProgramSimBelowWithClock (C := C) (F := F) passFuel relationFuel limit compiler
      (nextKnown, converted.2 ++ g.2) allowed program.1 converted.1 := by
  apply growingExprsSimFromBelowWithClock_installedBelow
  exact compileIncFuel_growing_below_with_existing_clock passFuel relationFuel limit compiler allowed g program nextKnown converted
    run distinct fresh initialWf eligible eligibleIH exprIH

/-- The successful install case obtains the installed-program simulation
from the actual incremental traversal and the oracle's location invariant.
The expression-case induction and eligibility remain assumptions. This is
Flapjack-specific simulation infrastructure. -/
theorem doInstall_success_evaluate_from_cases {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      expression ∈ program → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFrom (F := F) fuel relationFuel compiler after allowed [expression] [output]) :
    ∃ nextKnown converted targetInstalled finalG targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      evaluate converted.1 [] targetInstalled = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, _, _, _, _, _, resultEq, exprEq, _, _, _, _, _, _, _, _⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = (source.compileOracle 0).2.1 := by
    have : program = expressions := by simpa [nonzero] using resultEq
    exact this.trans exprEq
  have distinct : (codeLocations program).Nodup := by simpa [programEq] using ready.distinct 0
  have fresh : LabelsFresh (codeLocations program) g := by
    apply labelsFresh_of_codeIncludes g (codeLocations program) target.code ready.well.2 ready.included
    simpa [programEq] using ready.fresh 0
  apply doInstall_success_evaluate fuel relationFuel g allowed compiler source target sourceValues targetValues
    program installed result final ready states sourceWf values sourceCompiler targetCompiler targetOracle
    installRun programRun notType
  intro nextKnown converted passRun
  exact compileIncFuel_installedBelow_with_existing fuel relationFuel source.clock compiler allowed g (program, [])
    nextKnown converted passRun distinct fresh ready.well eligible eligibleIH exprIH

/-- A successful installation uses clock-bounded expression cases, with
location conditions supplied by the actual oracle. This is
Flapjack-specific simulation infrastructure. -/
theorem doInstall_success_evaluate_from_bounded_cases {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      expression ∈ program → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelow (F := F) fuel relationFuel source.clock compiler after allowed [expression] [output]) :
    ∃ nextKnown converted targetInstalled finalG targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      evaluate converted.1 [] targetInstalled = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, _, _, _, _, _, resultEq, exprEq, _, _, _, _, _, _, _, _⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = (source.compileOracle 0).2.1 := by
    have : program = expressions := by simpa [nonzero] using resultEq
    exact this.trans exprEq
  have distinct : (codeLocations program).Nodup := by simpa [programEq] using ready.distinct 0
  have fresh : LabelsFresh (codeLocations program) g := by
    apply labelsFresh_of_codeIncludes g (codeLocations program) target.code ready.well.2 ready.included
    simpa [programEq] using ready.fresh 0
  apply doInstall_success_evaluate fuel relationFuel g allowed compiler source target sourceValues targetValues
    program installed result final ready states sourceWf values sourceCompiler targetCompiler targetOracle
    installRun programRun notType
  intro nextKnown converted passRun
  exact compileIncFuel_installedBelow_from_bounded_cases fuel relationFuel source.clock compiler allowed g (program, [])
    nextKnown converted passRun distinct fresh ready.well eligible eligibleIH exprIH


/-- A successful installation uses clock-allowing expression cases, with
location conditions supplied by the actual oracle. The expression induction
remains an assumption. This is Flapjack-specific simulation infrastructure. -/
theorem doInstall_success_evaluate_withClock_from_cases {C F : Type} (fuel relationFuel : Nat) (g : State)
    (allowed : Set Nat) (compiler : ClosSem.Compiler C)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (installed : ClosSem.State (NumSet × C) F)
    (result : SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (final : ClosSem.State (NumSet × C) F)
    (ready : IncrementalInstallReady g source target)
    (states : StateRelFuel relationFuel g allowed source target)
    (sourceWf : StateWellFormedFuel relationFuel g allowed target.code source)
    (values : List.Forall₂ (ValueRelFuel relationFuel g allowed target.code) sourceValues targetValues)
    (sourceCompiler : source.compile = compileIncFuelCallback fuel compiler)
    (targetCompiler : target.compile = compiler)
    (targetOracle : target.compileOracle = compileIncFuelOracle fuel source.compileOracle)
    (installRun : doInstall sourceValues source = (.val program, installed))
    (programRun : evaluate program [] installed = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (eligible : ClosLang.Exp → State → Prop)
    (eligibleIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      expression ∈ program → callsFuel depth expression before = some (output, after) → eligible expression after)
    (exprIH : ∀ depth, depth < max fuel (listBudget program + 1) → ∀ expression output before after,
      callsFuel depth expression before = some (output, after) →
      (codeLocationsExp expression).Nodup → LabelsFresh (codeLocationsExp expression) before →
      wellFormed before → eligible expression after →
      GrowingExprsSimFromBelowWithClock (F := F) fuel relationFuel source.clock compiler after allowed [expression] [output]) :
    ∃ nextKnown converted targetInstalled extraClock finalG targetResult targetFinal,
      compileIncFuel? fuel g.1 (program, []) = some (nextKnown, converted) ∧
      doInstall targetValues target = (.val converted.1, targetInstalled) ∧
      doInstall targetValues { target with clock := target.clock + extraClock } =
        (.val converted.1, { targetInstalled with clock := targetInstalled.clock + extraClock }) ∧
      IncrementalInstallReady (nextKnown, converted.2 ++ g.2) installed targetInstalled ∧
      stateExtends g (nextKnown, converted.2 ++ g.2) ∧
      stateExtends (nextKnown, converted.2 ++ g.2) finalG ∧
      evaluate converted.1 [] { targetInstalled with clock := targetInstalled.clock + extraClock } =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel relationFuel finalG allowed targetFinal.code))
        (ValueRelFuel relationFuel finalG allowed targetFinal.code) result targetResult ∧
      StateRelFuel relationFuel finalG allowed final targetFinal ∧
      StateWellFormedFuel relationFuel finalG allowed targetFinal.code final ∧
      IncrementalInstallReady finalG final targetFinal ∧
      final.compile = compileIncFuelCallback fuel compiler ∧ targetFinal.compile = compiler ∧
      targetFinal.compileOracle = compileIncFuelOracle fuel final.compileOracle ∧
      (∀ key entry, target.code.lookup key = some entry → targetFinal.code.lookup key = some entry) := by
  obtain ⟨expressions, _, _, _, _, _, resultEq, exprEq, _, _, _, _, _, _, _, _⟩ :=
    doInstall_nonType_ready fuel relationFuel g allowed compiler source target sourceValues targetValues
      (.val program) installed ready states values sourceCompiler targetCompiler targetOracle installRun (by simp)
  have nonzero : source.clock ≠ 0 := by
    intro zero
    simp [zero] at resultEq
  have programEq : program = (source.compileOracle 0).2.1 := by
    have : program = expressions := by simpa [nonzero] using resultEq
    exact this.trans exprEq
  have distinct : (codeLocations program).Nodup := by simpa [programEq] using ready.distinct 0
  have fresh : LabelsFresh (codeLocations program) g := by
    apply labelsFresh_of_codeIncludes g (codeLocations program) target.code ready.well.2 ready.included
    simpa [programEq] using ready.fresh 0
  apply doInstall_success_evaluate_withClock fuel relationFuel g allowed compiler source target sourceValues targetValues
    program installed result final ready states sourceWf values sourceCompiler targetCompiler targetOracle
    installRun programRun notType
  intro nextKnown converted passRun
  exact compileIncFuel_installedBelow_withClock_from_cases fuel relationFuel source.clock compiler allowed g (program, [])
    nextKnown converted passRun distinct fresh ready.well eligible eligibleIH exprIH

end Flapjack.Compiler.Backend.ClosCall
