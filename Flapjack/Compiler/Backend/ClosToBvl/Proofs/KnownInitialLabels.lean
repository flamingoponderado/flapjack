import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownLabelOracle

/-! Initial prepared-program label properties after closure optimization. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosProps

/-- A prepared annotated chain has distinct labels below its fresh bound when
its nested closure locations are distinct and occur after the entry interval.
This is Lean-side assembly infrastructure, not a standalone HOL declaration. -/
theorem preparedChain_label_properties (original current output : Config)
    (expressions : List ClosLang.Exp) (start limit : Nat) (optimized : List ClosLang.Exp)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (compile : compilePrepared? original current expressions (ClosAnnotate.compile (chainExps start optimized)) =
      some (output, compiled, names))
    (nestedDistinct : (codeLocations optimized).Nodup)
    (bounds : ∀ location ∈ codeLocations optimized,
      start + max 1 optimized.length ≤ location ∧ location < limit)
    (entryBound : start + max 1 optimized.length ≤ limit) :
    (compiled.map Prod.fst).Nodup ∧
      ∀ label ∈ compiled.map Prod.fst, label < limit + numStubs current.maxApp := by
  classical
  let raw := ClosAnnotate.compile (chainExps start optimized)
  have entryDistinct : (raw.map Prod.fst).Nodup := by
    simpa [raw, annotated_labels] using chainExps_labels_nodup start optimized
  have entryBounds : ∀ label ∈ raw.map Prod.fst, start ≤ label ∧ label < start + max 1 optimized.length := by
    intro label member
    apply chainExps_label_bounds start optimized label
    simpa [raw, annotated_labels] using member
  have nestedSub : codeLocations (raw.map (fun (_, _, body) => body)) ⊆ codeLocations optimized := by
    have sub := ClosAnnotate.compile_codeLocations_sublist (chainExps start optimized)
    simpa [raw, chainExps_codeLocations] using sub.subset
  have nestedNodup : (codeLocations (raw.map (fun (_, _, body) => body))).Nodup := by
    have sub := ClosAnnotate.compile_codeLocations_sublist (chainExps start optimized)
    apply sub.nodup
    simpa [chainExps_codeLocations] using nestedDistinct
  have sourceDistinct : (raw.map Prod.fst ++ codeLocations (raw.map (fun (_, _, body) => body))).Nodup := by
    apply List.Nodup.append entryDistinct nestedNodup
    intro label entry nested
    have e := entryBounds label entry
    have n := bounds label (nestedSub nested)
    omega
  let converted := compileProgExpsHOL current.maxApp raw
  have convertedRun : compileProg? current.maxApp raw = some converted :=
    compileProg_checked_eq_original current.maxApp raw
  have convertedDistinct : (converted.map Prod.fst).Nodup :=
    compileProg_checked_nodup_of_source current.maxApp raw converted convertedRun sourceDistinct
  have convertedBelow : ∀ label ∈ converted.map Prod.fst, label < limit + numStubs current.maxApp := by
    intro label member
    rw [compileProg_checked_codeLocations current.maxApp raw converted convertedRun] at member
    simp only [List.mem_append, List.mem_map, List.mem_reverse] at member
    cases member with
    | inl entries =>
      obtain ⟨source, sourceMem, equal⟩ := entries
      have inEntries : source.1 ∈ raw.map Prod.fst := List.mem_map.mpr ⟨source, sourceMem, rfl⟩
      have b := entryBounds source.1 inEntries
      omega
    | inr locations =>
      obtain ⟨source, sourceMem, equal⟩ := locations
      have b := bounds source (nestedSub sourceMem)
      omega
  obtain ⟨resultNames, generated⟩ := compilePrepared_entries original current expressions raw
  have equal := Option.some.inj (compile.symm.trans generated)
  cases equal
  let stubs := sptToAList (initCode current.maxApp)
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
    · simp; omega
    · intro label inStub inSpecial
      have b := stubBelow label inStub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inSpecial
      omega
  have prefixBelow : ∀ label ∈ stubLabels, label < numStubs current.maxApp := by
    intro label member
    simp only [stubLabels, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    cases member with
    | inl stub => have b := stubBelow label stub; omega
    | inr special => omega
  have allDistinct : (stubLabels ++ converted.map Prod.fst).Nodup := by
    apply List.Nodup.append prefixDistinct convertedDistinct
    intro label inPrefix inConverted
    have low := prefixBelow label inPrefix
    have high := compileProg_checked_label_lower current.maxApp raw converted convertedRun label inConverted
    omega
  have permutation := (codeSort_perm (initialCompiledEntries current.maxApp current.start raw)).map Prod.fst
  constructor
  · apply permutation.nodup_iff.mpr
    simpa [initialCompiledEntries, stubs, converted, stubLabels, List.map_append] using allDistinct
  · intro label member
    obtain ⟨⟨name, arity, body⟩, inSorted, labelEq⟩ := List.mem_map.mp member
    simp only at labelEq
    subst label
    have inOriginal := (codeSort_mem (initialCompiledEntries current.maxApp current.start raw)
      (name, arity, body)).1 inSorted
    simp only [initialCompiledEntries, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inOriginal
    rcases inOriginal with (stub | force | init) | compiledEntry
    · have b := initCode_label_lt current.maxApp name (arity, body) stub
      omega
    · cases force; omega
    · cases init; omega
    · exact convertedBelow name (List.mem_map.mpr ⟨(name, arity, body), compiledEntry, rfl⟩)

/-- Numbering and the enabled known-function pipeline retain distinct closure
locations within the numbering interval, and preserve the number of entries.
This is Lean-side composition of the source passes and executable wrappers. -/
theorem numberedKnown_output_labels (fuel number : Nat) (c : ClosKnown.Config)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ClosKnown.ValApprox))
    (globals : Spt ClosKnown.ValApprox) (output : List ClosLang.Exp)
    (knownRun : ClosKnown.knownListTotal c (ClosFvs.compile (ClosNumber.renumberList number program).2)
      [] .ln = (optimized, globals))
    (optRun : ((optimized.map Prod.fst).mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some output) :
    output.length = program.length ∧ (codeLocations output).Nodup ∧
      ∀ location ∈ codeLocations output,
        number ≤ location ∧ location < (ClosNumber.renumberList number program).1 := by
  let numbered := (ClosNumber.renumberList number program).2
  have outputEq := Option.some.inj ((ClosKnown.ticks_letop_bounded fuel (optimized.map Prod.fst)).symm.trans optRun)
  have lengths := ClosKnown.knownListTotal_length c (ClosFvs.compile numbered) [] .ln
  rw [knownRun] at lengths
  have numberedLength := ClosNumber.renumberList_length program number
  have outputLength : output.length = program.length := by
    rw [← outputEq]
    have knownLength : optimized.length = numbered.length := by
      simpa [ClosFvs.compile, ClosFvs.removeList_length] using lengths
    simpa [ClosLetop.compileList_eq_map, ClosTicks.removeList_eq_map, knownLength, numbered] using numberedLength
  have run := ClosKnown.known_compileFuel_eq fuel c numbered optimized globals knownRun
  rw [outputEq] at run
  have counts := ClosKnown.compileFuel_codeLocationsBag fuel (some c) _ numbered output run
  have subset : codeLocations output ⊆ codeLocations numbered := by
    intro label member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member) (counts label))
  have distinct : (codeLocations output).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro label
    exact Nat.le_trans (counts label)
      (List.nodup_iff_count_le_one.mp (ClosNumber.renumberList_codeLocations_nodup program number) label)
  refine ⟨outputLength, distinct, ?_⟩
  intro location member
  exact ClosNumber.renumberList_location_bounds program number location (subset member)

end Flapjack.Compiler.Backend.ClosToBvl
