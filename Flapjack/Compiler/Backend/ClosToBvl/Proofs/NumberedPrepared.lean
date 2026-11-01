import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationBounds
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationDistinct
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainLocations
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LabelOrigins
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SortPermutation

/-! Location annotations supplied by closure numbering to prepared programs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- Chaining top-level expressions adds no closure-code locations. -/
theorem chainExps_codeLocations (start : Nat) (expressions : List ClosLang.Exp) :
    ClosProps.codeLocations ((chainExps start expressions).map (fun (_, _, body) => body)) =
      ClosProps.codeLocations expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, ClosProps.codeLocations]
    | cons second tail =>
      simpa [chainExps, ClosProps.codeLocations, ClosProps.codeLocationsExp] using
        congrArg (fun locations => ClosProps.codeLocationsExp first ++ locations) (ih (start + 1))

/-- Every entry in a chain of numbered expressions retains the locations
assigned by the numbering pass. -/
theorem numberedChain_locations (chainStart numberingStart : Nat) (expressions : List ClosLang.Exp) :
    ∀ name arity body, (name, arity, body) ∈ chainExps chainStart (ClosNumber.renumberList numberingStart expressions).2 →
      ClosProps.everyFnLocationSome [body] := by
  have numbered := ClosNumber.renumberList_locations expressions numberingStart
  have chain := (chainExps_annotations chainStart (ClosNumber.renumberList numberingStart expressions).2).1.mpr numbered
  intro name arity body member
  have inBodies : body ∈ (chainExps chainStart (ClosNumber.renumberList numberingStart expressions).2).map
      (fun (_, _, body) => body) := by
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  exact ClosNumber.locations_member _ body chain inBodies

/-- The no-optimization closure preprocessing path returns a program whose
function bodies have both required annotation kinds. -/
theorem compileCommonNoOpts_annotations (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program)) :
    (∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnLocationSome [body]) ∧
    (∀ name arity body, (name, arity, body) ∈ program → ClosProps.everyFnVarsSome [body]) := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at compiled
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at compiled
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (compiled.symm.trans run)
        cases equal
        constructor
        · apply ClosAnnotate.compile_locations
          intro name arity body member
          have source := numberedChain_locations config.nextLoc aligned expressions name arity body
          simp only [numbered] at source
          exact source member
        · exact ClosAnnotate.compile_varsSome _

/-- The no-optimization preprocessing path places closure locations in the
interval reserved by the numbering state, even after annotation and chaining. -/
theorem compileCommonNoOpts_location_bounds (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program))
    (location : Nat) (member : location ∈ ClosProps.codeLocations (program.map (fun (_, _, body) => body))) :
    config.nextLoc + max 1 expressions.length ≤ location ∧ location < current.nextLoc := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at compiled
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at compiled
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (compiled.symm.trans run)
        cases equal
        have raw := ClosAnnotate.compile_codeLocations (chainExps config.nextLoc numberedExpressions) member
        rw [chainExps_codeLocations] at raw
        have numberedMember : location ∈ ClosProps.codeLocations (ClosNumber.renumberList aligned expressions).2 := by
          simpa [numbered] using raw
        have bounds := ClosNumber.renumberList_location_bounds expressions aligned location numberedMember
        have lower : config.nextLoc + max 1 expressions.length ≤ aligned := by
          dsimp [aligned, next]
          split <;> omega
        simp only [numbered] at bounds
        simp only
        omega

/-- Prepared top-level entries have distinct labels in the interval reserved
before closure numbering. -/
theorem compileCommonNoOpts_entry_labels (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program)) :
    (program.map Prod.fst).Nodup ∧
      ∀ label ∈ program.map Prod.fst,
        config.nextLoc ≤ label ∧ label < config.nextLoc + max 1 expressions.length := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at compiled
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at compiled
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (compiled.symm.trans run)
        cases equal
        have length := ClosNumber.renumberList_length expressions aligned
        simp only [numbered] at length
        rw [annotated_labels]
        constructor
        · exact chainExps_labels_nodup _ _
        · intro label member
          have bounds := chainExps_label_bounds config.nextLoc numberedExpressions label member
          simpa only [length] using bounds

/-- Entry labels and nested closure labels from no-optimization preprocessing
are disjoint because numbering starts after the reserved entry interval. -/
theorem compileCommonNoOpts_entries_disjoint (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program))
    (label : Nat) (entry : label ∈ program.map Prod.fst) :
    label ∉ ClosProps.codeLocations (program.map (fun (_, _, body) => body)) := by
  intro nested
  have a := (compileCommonNoOpts_entry_labels config current expressions program compiled).2 label entry
  have b := compileCommonNoOpts_location_bounds config current expressions program compiled label nested
  omega

/-- Numbering, chaining, and annotation produce pairwise distinct nested
closure locations on the no-optimization path. -/
theorem compileCommonNoOpts_nested_nodup (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : compileCommonNoOpts? config expressions = some (current, program)) :
    (ClosProps.codeLocations (program.map (fun (_, _, body) => body))).Nodup := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at compiled
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at compiled
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (compiled.symm.trans run)
        cases equal
        have distinct := ClosNumber.renumberList_codeLocations_nodup expressions aligned
        simp only [numbered] at distinct
        have chainDistinct : (ClosProps.codeLocations
            ((chainExps config.nextLoc numberedExpressions).map (fun (_, _, body) => body))).Nodup := by
          simpa [chainExps_codeLocations] using distinct
        exact (ClosAnnotate.compile_codeLocations_sublist _).nodup chainDistinct

/-- Checked conversion of the no-optimization preprocessed program emits
pairwise distinct BVL labels. -/
theorem compileCommonNoOpts_converted_nodup (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (target : List (Nat × Nat × Bvl.Exp))
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (convert : compileProg? current.maxApp program = some target) :
    (target.map Prod.fst).Nodup := by
  rw [compileProg_checked_codeLocations current.maxApp program target convert]
  apply List.Nodup.append
  · have entries := (compileCommonNoOpts_entry_labels config current expressions program preprocess).1
    have shifted : ((program.map Prod.fst).map (fun label => label + numStubs current.maxApp)).Nodup :=
      entries.map (fun _ _ equal => Nat.add_right_cancel equal)
    simpa [List.map_map, Function.comp_def] using shifted
  · have nested := compileCommonNoOpts_nested_nodup config current expressions program preprocess
    apply List.Nodup.map (fun _ _ equal => Nat.add_right_cancel equal)
    exact List.nodup_reverse.mpr nested
  · intro label entryMember nestedMember
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp entryMember
    obtain ⟨location, locationMem, locationEq⟩ := List.mem_map.mp nestedMember
    have sourceEntry : entry.1 ∈ program.map Prod.fst := List.mem_map.mpr ⟨entry, entryMem, rfl⟩
    have sourceNested : location ∈ ClosProps.codeLocations (program.map (fun (_, _, body) => body)) := by
      simpa using locationMem
    have different := compileCommonNoOpts_entries_disjoint config current expressions program preprocess entry.1 sourceEntry
    have equal : entry.1 = location := by omega
    exact different (equal ▸ sourceNested)

/-- Each preprocessed entry survives checked BVL conversion at its shifted
label, in the interval reserved for top-level entries. -/
theorem compileCommonNoOpts_compiled_entry (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (target : List (Nat × Nat × Bvl.Exp))
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (convert : compileProg? current.maxApp program = some target)
    (label : Nat) (entry : label ∈ program.map Prod.fst) :
    label + numStubs current.maxApp ∈ target.map Prod.fst ∧
      config.nextLoc + numStubs current.maxApp ≤ label + numStubs current.maxApp ∧
      label + numStubs current.maxApp < config.nextLoc + max 1 expressions.length + numStubs current.maxApp := by
  have labels := compileProg_checked_label_origins current.maxApp program target convert
  have bounds := (compileCommonNoOpts_entry_labels config current expressions program preprocess).2 label entry
  constructor
  · rw [labels]
    apply List.mem_append_left
    obtain ⟨source, member, equal⟩ := List.mem_map.mp entry
    apply List.mem_map.mpr
    exact ⟨source, member, by simp only [equal]⟩
  · omega

/-- The next location returned by preprocessing lies beyond the complete
top-level entry interval. -/
theorem compileCommonNoOpts_nextLoc_lower (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp))
    (preprocess : compileCommonNoOpts? config expressions = some (current, program)) :
    config.nextLoc + max 1 expressions.length ≤ current.nextLoc := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at preprocess
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at preprocess
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (preprocess.symm.trans run)
        cases equal
        have monotone := ClosNumber.renumberList_start_le expressions aligned
        simp only [numbered] at monotone
        have lower : config.nextLoc + max 1 expressions.length ≤ aligned := by
          dsimp [aligned, next]
          split <;> omega
        simp only
        omega

/-- All labels emitted by checked BVL conversion of the preprocessed program
lie below its next fresh closure location, after adding the stub prefix. -/
theorem compileCommonNoOpts_compiled_labels_below (config current : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (target : List (Nat × Nat × Bvl.Exp))
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (convert : compileProg? current.maxApp program = some target)
    (label : Nat) (member : label ∈ target.map Prod.fst) :
    label < current.nextLoc + numStubs current.maxApp := by
  rw [compileProg_checked_codeLocations current.maxApp program target convert] at member
  simp only [List.mem_append, List.mem_map, List.mem_reverse] at member
  cases member with
  | inl entries =>
    obtain ⟨source, sourceMem, equal⟩ := entries
    have entry : source.1 ∈ program.map Prod.fst := List.mem_map.mpr ⟨source, sourceMem, rfl⟩
    have bounds := (compileCommonNoOpts_entry_labels config current expressions program preprocess).2 source.1 entry
    have lower := compileCommonNoOpts_nextLoc_lower config current expressions program preprocess
    omega
  | inr locations =>
    obtain ⟨source, sourceMem, equal⟩ := locations
    have bounds := compileCommonNoOpts_location_bounds config current expressions program preprocess source sourceMem
    omega

/-- Every label in the sorted prepared output, including application and
runtime stubs, lies below the next closure location with the stub offset. -/
theorem compileNoOpts_prepared_labels_below (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (label : Nat) (member : label ∈ compiled.map Prod.fst) :
    label < current.nextLoc + numStubs current.maxApp := by
  have prepared : compilePrepared? config current expressions program = some (output, compiled, names) := by
    simpa [compileNoOpts?, preprocess] using compile
  obtain ⟨resultNames, generated⟩ := compilePrepared_entries config current expressions program
  have equal := Option.some.inj (prepared.symm.trans generated)
  cases equal
  obtain ⟨⟨name, arity, body⟩, inSorted, labelEq⟩ := List.mem_map.mp member
  simp only at labelEq
  subst label
  have inOriginal := (codeSort_mem (initialCompiledEntries current.maxApp current.start program)
    (name, arity, body)).1 inSorted
  simp only [initialCompiledEntries, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inOriginal
  have lower := compileCommonNoOpts_nextLoc_lower config current expressions program preprocess
  have stubCount : 2 ≤ numStubs current.maxApp := by simp [numStubs]
  rcases inOriginal with (stub | force | init) | compiledEntry
  · have bound := initCode_label_lt current.maxApp name (arity, body) stub
    omega
  · cases force
    omega
  · cases init
    omega
  · have converted : compileProg? current.maxApp program = some (compileProgExpsHOL current.maxApp program) :=
      compileProg_checked_eq_original current.maxApp program
    have targetMember : name ∈ (compileProgExpsHOL current.maxApp program).map Prod.fst :=
      List.mem_map.mpr ⟨(name, arity, body), compiledEntry, rfl⟩
    exact compileCommonNoOpts_compiled_labels_below config current expressions program _ preprocess converted name targetMember

/-- The complete prepared output has distinct labels, including both runtime
stubs and the application-stub table, after sorting. -/
theorem compileNoOpts_prepared_labels_nodup (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names)) :
    (compiled.map Prod.fst).Nodup := by
  classical
  have prepared : compilePrepared? config current expressions program = some (output, compiled, names) := by
    simpa [compileNoOpts?, preprocess] using compile
  obtain ⟨resultNames, generated⟩ := compilePrepared_entries config current expressions program
  have equal := Option.some.inj (prepared.symm.trans generated)
  cases equal
  let stubs := sptToAList (initCode current.maxApp)
  let converted := compileProgExpsHOL current.maxApp program
  let stubLabels := stubs.map Prod.fst ++ [numStubs current.maxApp - 2, numStubs current.maxApp - 1]
  have stubCount : 2 ≤ numStubs current.maxApp := by simp [numStubs]
  have stubDistinct : (stubs.map Prod.fst).Nodup := sptAllDistinctMapFstToAList _
  have stubBelow : ∀ label ∈ stubs.map Prod.fst, label < numStubs current.maxApp - 2 := by
    intro label member
    obtain ⟨⟨name, arity, body⟩, entry, equal⟩ := List.mem_map.mp member
    simp only at equal
    subst label
    exact initCode_label_lt current.maxApp name (arity, body) entry
  have prefixDistinct : stubLabels.Nodup := by
    dsimp [stubLabels]
    apply List.Nodup.append stubDistinct
    · simp
      omega
    · intro label inStub inSpecial
      have bound := stubBelow label inStub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inSpecial
      omega
  have prefixBelow : ∀ label ∈ stubLabels, label < numStubs current.maxApp := by
    intro label member
    simp only [stubLabels, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    cases member with
    | inl stub => have bound := stubBelow label stub; omega
    | inr special => omega
  have convertedRun : compileProg? current.maxApp program = some converted :=
    compileProg_checked_eq_original current.maxApp program
  have convertedDistinct := compileCommonNoOpts_converted_nodup config current expressions program converted preprocess convertedRun
  have convertedAbove : ∀ label ∈ converted.map Prod.fst, numStubs current.maxApp ≤ label :=
    compileProg_checked_label_lower current.maxApp program converted convertedRun
  have allDistinct : (stubLabels ++ converted.map Prod.fst).Nodup := by
    apply List.Nodup.append prefixDistinct convertedDistinct
    intro label inPrefix inConverted
    have low := prefixBelow label inPrefix
    have high := convertedAbove label inConverted
    omega
  have permutation := (codeSort_perm (initialCompiledEntries current.maxApp current.start program)).map Prod.fst
  apply permutation.nodup_iff.mpr
  simpa [initialCompiledEntries, stubs, converted, stubLabels, List.map_append] using allDistinct

/-- Stateful numbering supplies locations for each incremental main program;
annotation then supplies variables and preserves the supplied auxiliary-code
locations. The auxiliary code is passed through numbering unchanged. -/
theorem numberedAnnotatedOracle_annotations {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (auxLocations : ∀ index entry, entry ∈ (oracle index).2.2 →
      ClosProps.everyFnLocationSome [entry.2.2]) :
    ∀ index,
      let program := ((pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2
      ClosProps.everyFnLocationSome program.1 ∧ ClosProps.everyFnVarsSome program.1 ∧
        (∀ entry ∈ program.2, ClosProps.everyFnLocationSome [entry.2.2]) ∧
        (∀ entry ∈ program.2, ClosProps.everyFnVarsSome [entry.2.2]) := by
  apply annotatedOracle_annotations
  intro index
  constructor
  · simpa [stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_locations (oracle index).1.1 (oracle index).2.1
  · simpa [stateCo, ClosNumber.ignoreTable] using auxLocations index

/-- The numbering states of a consistent incremental oracle are monotone.
These states can serve as candidate boundaries for future generated code;
the separate proof that emitted labels lie between them is still required. -/
theorem numberingOracle_state_monotone {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ {i j}, i ≤ j → (oracle i).1.1 ≤ (oracle j).1.1 := by
  have step : ∀ i, (oracle i).1.1 ≤ (oracle (i + 1)).1.1 := by
    intro i
    have increase := ClosNumber.compileInc_start_lt (oracle i).1.1 (oracle i).2.1
    have next := state i
    simp only [ClosNumber.ignoreTable] at next
    omega
  intro i j order
  induction order with
  | refl => exact Nat.le_refl _
  | @step j order ih => exact Nat.le_trans ih (step j)

/-- Main expressions in a consistent numbered oracle use closure locations
between the current and next numbering states. Auxiliary code is unchanged
and therefore requires a separate range argument. -/
theorem numberingOracle_location_bounds {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index location : Nat)
    (member : location ∈ ClosProps.codeLocations
      ((stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2.1)) :
    (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1 := by
  have numbered : location ∈ ClosProps.codeLocations
      (ClosNumber.compileInc (oracle index).1.1 (oracle index).2.1).2 := by
    simpa [stateCo, ClosNumber.ignoreTable] using member
  have bounds := ClosNumber.compileInc_location_bounds (oracle index).1.1 location (oracle index).2.1 numbered
  have next := state index
  simp only [ClosNumber.ignoreTable] at next
  omega

/-- Numbering followed by variable annotation keeps all main-expression
closure locations inside the oracle entry's numbering interval. -/
theorem numberedAnnotatedOracle_location_bounds {C : Type}
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (index location : Nat)
    (member : location ∈ ClosProps.codeLocations
      (((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.1)) :
    (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1 := by
  apply numberingOracle_location_bounds oracle state index location
  apply ClosAnnotate.annotateList_codeLocations 0
  simpa [Function.comp_def, pureCo, ClosAnnotate.compileInc] using member

/-- Extracting a preserved name marker returns its starting location and
leaves precisely the closure locations of the remaining expressions. -/
theorem extractName_numbered_marker (start : Nat) (expressions : List ClosLang.Exp) :
    let marker := ClosLang.Exp.op .none (.intOp (.const (Int.ofNat start))) []
    (extractName (marker :: expressions)).1 = start ∧
    (extractName (marker :: expressions)).2.length = max 1 expressions.length ∧
    ClosProps.codeLocations (extractName (marker :: expressions)).2 = ClosProps.codeLocations expressions := by
  cases expressions with
  | nil => simp [extractName, ClosProps.codeLocations, ClosProps.codeLocationsExp]
  | cons first rest => simp [extractName]

/-- The numbered and annotated incremental main program retains its original
entry location, and the extracted chain reserves the expected number of slots. -/
theorem numberedAnnotated_extractName (start : Nat) (expressions : List ClosLang.Exp) :
    let output := ClosAnnotate.annotateList 0 (ClosNumber.compileInc start expressions).2
    (extractName output).1 = start ∧
      (extractName output).2.length = max 1 expressions.length ∧
      ClosProps.codeLocations (extractName output).2 ⊆
        ClosProps.codeLocations (ClosNumber.compileInc start expressions).2 := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  cases numbered : ClosNumber.renumberList aligned expressions with
  | mk nextLoc numberedExpressions =>
    have numberedLength := ClosNumber.renumberList_length expressions aligned
    simp only [numbered] at numberedLength
    have marker : ClosAnnotate.annotateList 0 (ClosNumber.compileInc start expressions).2 =
        .op .none (.intOp (.const (Int.ofNat start))) [] ::
          ClosAnnotate.annotateList 0 numberedExpressions := by
      simpa [ClosNumber.compileInc, next, aligned, numbered] using
        ClosAnnotate.annotateList_name_marker start numberedExpressions
    rw [marker]
    have extract := extractName_numbered_marker start (ClosAnnotate.annotateList 0 numberedExpressions)
    have length : (ClosAnnotate.annotateList 0 numberedExpressions).length = expressions.length := by
      simpa [ClosAnnotate.annotateList_length] using numberedLength
    refine ⟨extract.1, ?_, ?_⟩
    · simpa [length] using extract.2.1
    · rw [extract.2.2]
      have subset := ClosAnnotate.annotateList_codeLocations 0 numberedExpressions
      simpa [ClosNumber.compileInc, next, aligned, numbered, ClosProps.codeLocations,
        ClosProps.codeLocationsExp] using subset

/-- Numbered and annotated incremental main expressions have distinct
closure locations after the entry marker is extracted. -/
theorem numberedAnnotated_extractName_nodup (start : Nat) (expressions : List ClosLang.Exp) :
    let output := ClosAnnotate.annotateList 0 (ClosNumber.compileInc start expressions).2
    (ClosProps.codeLocations (extractName output).2).Nodup := by
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  cases numbered : ClosNumber.renumberList aligned expressions with
  | mk nextLoc numberedExpressions =>
    have marker : ClosAnnotate.annotateList 0 (ClosNumber.compileInc start expressions).2 =
        .op .none (.intOp (.const (Int.ofNat start))) [] ::
          ClosAnnotate.annotateList 0 numberedExpressions := by
      simpa [ClosNumber.compileInc, next, aligned, numbered] using
        ClosAnnotate.annotateList_name_marker start numberedExpressions
    rw [marker]
    have extract := extractName_numbered_marker start (ClosAnnotate.annotateList 0 numberedExpressions)
    dsimp only
    rw [extract.2.2]
    apply ClosAnnotate.annotateList_codeLocations_nodup
    have distinct := ClosNumber.renumberList_codeLocations_nodup expressions aligned
    simpa [numbered] using distinct

/-- If the extracted main code and unchanged auxiliary code lie in one
interval, incremental BVL conversion emits labels in that interval shifted
by the application-stub prefix. -/
theorem compileInc_labels_range (maxApp start limit : Nat)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (real : List ClosLang.Exp) (extract : extractName program.1 = (start, real))
    (entriesBound : start + max 1 real.length ≤ limit)
    (mainBounds : ∀ location ∈ ClosProps.codeLocations real, start ≤ location ∧ location < limit)
    (auxBounds : ∀ entry ∈ program.2, start ≤ entry.1 ∧ entry.1 < limit ∧
      ∀ location ∈ ClosProps.codeLocationsExp entry.2.2, start ≤ location ∧ location < limit)
    (label : Nat) (member : label ∈ (compileInc maxApp program).map Prod.fst) :
    start + numStubs maxApp ≤ label ∧ label < limit + numStubs maxApp := by
  let source := chainExps start real ++ program.2
  have convert : compileProg? maxApp source = some (compileInc maxApp program) := by
    simpa [source, compileInc, extract] using compileProg_checked_eq_original maxApp source
  rw [compileProg_checked_codeLocations maxApp source _ convert] at member
  simp only [List.mem_append, List.mem_map, List.mem_reverse] at member
  cases member with
  | inl entries =>
    obtain ⟨entry, entryMem, equal⟩ := entries
    have origin : entry ∈ chainExps start real ∨ entry ∈ program.2 := by
      simpa [source] using entryMem
    cases origin with
    | inl chain =>
      have entryLabel : entry.1 ∈ (chainExps start real).map Prod.fst :=
        List.mem_map.mpr ⟨entry, chain, rfl⟩
      have bounds := chainExps_label_bounds start real entry.1 entryLabel
      omega
    | inr auxiliary =>
      have bounds := auxBounds entry auxiliary
      omega
  | inr locations =>
    obtain ⟨location, sourceMem, equal⟩ := locations
    simp only [source, List.map_append, ClosProps.codeLocations_append, List.mem_append,
      chainExps_codeLocations] at sourceMem
    cases sourceMem with
    | inl main =>
      have bounds := mainBounds location main
      omega
    | inr auxiliary =>
      obtain ⟨body, inBodies, inBody⟩ := (ClosProps.mem_codeLocations location _).1 auxiliary
      obtain ⟨entry, entryMem, equalBody⟩ := List.mem_map.mp inBodies
      have bounds := (auxBounds entry entryMem).2.2 location (by simpa [equalBody] using inBody)
      omega

/-- Stateful numbering and annotation place the next incremental BVL program
in its state interval, provided the untouched auxiliary code also lies there. -/
theorem numberedAnnotatedOracle_labels_range {C : Type} (maxApp : Nat)
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (auxBounds : ∀ index entry, entry ∈ (oracle index).2.2 →
      (oracle index).1.1 ≤ entry.1 ∧ entry.1 < (oracle (index + 1)).1.1 ∧
      ∀ location ∈ ClosProps.codeLocationsExp entry.2.2,
        (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1)
    (index label : Nat)
    (member : label ∈ (compileInc maxApp
      ((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2).map Prod.fst) :
    (oracle index).1.1 + numStubs maxApp ≤ label ∧
      label < (oracle (index + 1)).1.1 + numStubs maxApp := by
  let start := (oracle index).1.1
  let limit := (oracle (index + 1)).1.1
  let expressions := (oracle index).2.1
  let auxiliary := (oracle index).2.2
  let numbered := ClosNumber.compileInc start expressions
  let program := (ClosAnnotate.annotateList 0 numbered.2, ClosAnnotate.compile auxiliary)
  have programEq :
      ((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2 = program := by
    simp [program, numbered, start, expressions, auxiliary, pureCo, stateCo,
      ClosNumber.ignoreTable, ClosAnnotate.compileInc]
  rw [programEq] at member
  let real := (extractName program.1).2
  have shape := numberedAnnotated_extractName start expressions
  have startEq : (extractName program.1).1 = start := by simpa [program, numbered] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by simpa [real, program, numbered] using shape.2.1
  have locationsSub : ClosProps.codeLocations real ⊆ ClosProps.codeLocations numbered.2 := by
    simpa [real, program, numbered] using shape.2.2
  have nextEq : limit = numbered.1 := by simpa [limit, numbered, start, expressions, ClosNumber.ignoreTable] using state index
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  apply compileInc_labels_range maxApp start limit program real extract ?_ ?_ ?_ label member
  · simpa [lengthEq, nextEq, numbered, max_assoc] using ClosNumber.compileInc_reservation start expressions
  · intro location inReal
    have bounds := ClosNumber.compileInc_location_bounds start location expressions (locationsSub inReal)
    simpa [nextEq, numbered] using bounds
  · intro ⟨name, arity, body⟩ inAux
    have sourceMem : (name, arity, body) ∈ ClosAnnotate.compile auxiliary := by simpa [program] using inAux
    obtain ⟨⟨oldName, oldArity, oldBody⟩, oldMem, equal⟩ := List.mem_map.mp sourceMem
    simp only [Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl, rfl⟩ := equal
    have oldBounds := auxBounds index (oldName, oldArity, oldBody) oldMem
    refine ⟨oldBounds.1, oldBounds.2.1, ?_⟩
    intro location inBody
    exact oldBounds.2.2 location (ClosAnnotate.annotateSing_codeLocations oldArity oldBody inBody)

/-- The executable no-optimization closure compiler satisfies the prepared
entry behavior theorem without separate program-annotation assumptions.
Correctness of preprocessing and the oracle label bounds remain prerequisites
for a theorem about the original source expressions. -/
theorem compileNoOpts_tree_semantics {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (sourceOracle : ClosSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle
      (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] ≠ .fail)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBoundary : current.nextLoc + numStubs current.maxApp ≤ boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp (sourceOracle index).2).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp (sourceOracle index).2).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (futureAnnotations : ∀ index, ClosProps.everyFnLocationSome (sourceOracle index).2.1 ∧
      ClosProps.everyFnVarsSome (sourceOracle index).2.1 ∧
      (∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnLocationSome [entry.2.2]) ∧
      (∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnVarsSome [entry.2.2])) :
    BvlSem.semantics ffi (sptFromAList compiled) (pureCo (compileInc current.maxApp) ∘ sourceOracle)
        targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle
        (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] := by
  have prepared : compilePrepared? config current expressions program = some (output, compiled, names) := by
    simpa [compileNoOpts?, preprocess] using compile
  obtain ⟨locations, varsAnnotated⟩ := compileCommonNoOpts_annotations config current expressions program preprocess
  exact compilePrepared_tree_semantics_of_boundaries ffi config current output expressions program compiled names
    sourceOracle targetCompiler boundary prepared nonfail
    (compileNoOpts_prepared_labels_nodup config current output expressions program compiled names preprocess compile)
    locations varsAnnotated monotone
    (fun location member => Nat.lt_of_lt_of_le
      (compileNoOpts_prepared_labels_below config current output expressions program compiled names
        preprocess compile location member) initialBoundary)
    futureDistinct ranges futureAnnotations

/-- No-optimization compilation with the stateful numbering and annotation
oracle. Only the unchanged auxiliary code still needs input locations;
numbering establishes them for the incremental main expressions. -/
theorem compileNoOpts_numberedOracle_semantics {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : Nat → (Nat × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (targetCompiler : BvlSem.Compiler C)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program)
      (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
      (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] ≠ .fail)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialState : current.nextLoc ≤ (oracle 0).1.1)
    (futureDistinct : ∀ index, ((compileInc current.maxApp
      ((pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2).map Prod.fst).Nodup)
    (auxBounds : ∀ index entry, entry ∈ (oracle index).2.2 →
      (oracle index).1.1 ≤ entry.1 ∧ entry.1 < (oracle (index + 1)).1.1 ∧
      ∀ location ∈ ClosProps.codeLocationsExp entry.2.2,
        (oracle index).1.1 ≤ location ∧ location < (oracle (index + 1)).1.1)
    (auxLocations : ∀ index entry, entry ∈ (oracle index).2.2 →
      ClosProps.everyFnLocationSome [entry.2.2]) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program)
        (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
        (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] := by
  apply compileNoOpts_tree_semantics ffi config current output expressions program compiled names
    (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    targetCompiler (fun index => (oracle index).1.1 + numStubs current.maxApp)
    preprocess compile nonfail
  · intro i j order
    exact Nat.add_le_add_right (numberingOracle_state_monotone oracle oracleState order) _
  · exact Nat.add_le_add_right initialState _
  · exact futureDistinct
  · exact numberedAnnotatedOracle_labels_range current.maxApp oracle oracleState auxBounds
  · exact numberedAnnotatedOracle_annotations oracle auxLocations

end Flapjack.Compiler.Backend.ClosToBvl
