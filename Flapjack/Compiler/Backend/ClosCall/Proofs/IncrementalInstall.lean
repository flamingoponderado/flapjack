import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalCode
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantDirectCall
import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantListSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.InstallWellformed
import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracle

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

end Flapjack.Compiler.Backend.ClosCall
