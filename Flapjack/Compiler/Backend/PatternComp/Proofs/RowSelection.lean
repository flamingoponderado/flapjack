import Flapjack.Compiler.Backend.PatternComp.Decision
import Flapjack.Compiler.Backend.PatternExh.Proofs.Match

/-! Row-selection lemmas for the pattern compiler. -/
namespace Flapjack.Compiler.Backend.PatternComp
open Flapjack PatternCommon PatternSemantics

private def toBroad (refs : HolFiniteMapExact Nat Term) : Nat → Option Term := refs.lookup

private def ofBroad (lookup : Nat → Option Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat Term := ⟨lookup, support⟩

/-- The canonical finite-map parameter roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_matchRows_takeUntilAny_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_append_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_isConstRow_failure_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_nonConstRow_not_success_nullary_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_filter_safe_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_moveConstUp_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_insertAny_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_isAny_pmatch_refs refs key

/-- A pattern containing an unconditional alternative cannot return a
non-match, though it may still report a type failure. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_Any_pmatch"
  (fmap_as_finite_support_parameters := [refs])]
theorem isAny_pmatch (refs : HolFiniteMapExact Nat Term) (value : Term) (pattern : Pat)
    (any : isAny pattern = true) : pmatch refs pattern value ≠ .failure := by
  cases pattern with
  | any => simp [pmatch]
  | cons _ _ | lit _ | ref _ => simp [isAny] at any
  | or left right =>
    simp only [isAny, Bool.or_eq_true] at any
    cases first : pmatch refs left value with
    | success =>
      cases second : pmatch refs right value <;> simp [pmatch, first, second]
    | typeFailure => simp [pmatch, first]
    | failure =>
      rcases any with leftAny | rightAny
      · exact (isAny_pmatch refs value left leftAny first).elim
      · simpa [pmatch, first] using isAny_pmatch refs value right rightAny

termination_by sizeOf pattern

/-- Matching appended row lists checks the entire suffix for type failures
even after a successful earlier match. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "match_append"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_append (refs : HolFiniteMapExact Nat Term) (value : Term)
    (left right : List (Pat × Nat)) :
    matchRows refs (left ++ right) value =
      match matchRows refs left value with
      | none => none
      | some (.success index) => if matchRows refs right value ≠ none then some (.success index) else none
      | some _ => matchRows refs right value := by
  induction left with
  | nil => simp [matchRows]
  | cons row left ih =>
    obtain ⟨pattern, index⟩ := row
    cases head : pmatch refs pattern value with
    | typeFailure => simp [matchRows, head]
    | failure => simpa [matchRows, head] using ih
    | success =>
      cases prefixResult : matchRows refs left value with
      | none => simp_all [matchRows]
      | some result =>
        cases result <;> cases suffixResult : matchRows refs right value <;>
          simp_all [matchRows]

/-- The exported source equation after reducing its constant application. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "pmatchResult_case_NONE" 92]
theorem pmatchResult_case_none {α : Type} (result : PmatchResult) :
    (match result with
     | .success => (none : Option α)
     | .failure => none
     | .typeFailure => none) = none := by
  cases result <;> rfl

/-- Truncating after an unconditional row preserves any non-error result. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "match_take_until_Any"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_takeUntilAny (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none) :
    matchRows refs (takeUntilAny rows) value = matchRows refs rows value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, index⟩ := row
    by_cases unconditional : isAny pattern = true
    · have cannotFail := isAny_pmatch refs value pattern unconditional
      cases head : pmatch refs pattern value with
      | failure => exact (cannotFail head).elim
      | typeFailure => simp [matchRows, head] at safe
      | success =>
        cases tail : matchRows refs rows value with
        | none => simp [matchRows, head, tail] at safe
        | some result => simp [takeUntilAny, unconditional, matchRows, head, tail]
    · cases head : pmatch refs pattern value with
      | typeFailure => simp [matchRows, head] at safe
      | failure =>
        have tailSafe : matchRows refs rows value ≠ none := by simpa [matchRows, head] using safe
        simpa [takeUntilAny, unconditional, matchRows, head] using ih tailSafe
      | success =>
        cases tail : matchRows refs rows value with
        | none => simp [matchRows, head, tail] at safe
        | some result =>
          have tailEq := ih (by simp [tail])
          simp [takeUntilAny, unconditional, matchRows, head, tail, tailEq]

/-- Replacing the last pattern with a wildcard preserves non-failure
results whenever the original rows do not produce a type error. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "match_insert_Any"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_insertAny (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none) :
    matchRows refs (insertAny rows) value ≠ none ∧
      (matchRows refs rows value ≠ some .failure →
       matchRows refs (insertAny rows) value = matchRows refs rows value) := by
  induction rows with
  | nil => simp [insertAny, matchRows]
  | cons row rows ih =>
    obtain ⟨pattern, index⟩ := row
    cases rows with
    | nil =>
      cases head : pmatch refs pattern value <;> simp_all [insertAny, matchRows, pmatch]
    | cons next rest =>
      cases head : pmatch refs pattern value with
      | typeFailure => simp [matchRows, head] at safe
      | failure =>
        have tailSafe : matchRows refs (next :: rest) value ≠ none := by
          simpa [matchRows, head] using safe
        simpa [insertAny, matchRows, head] using ih tailSafe
      | success =>
        cases tail : matchRows refs (next :: rest) value with
        | none =>
          have bad : matchRows refs ((pattern, index) :: next :: rest) value = none := by
            rw [matchRows, head, tail]
          exact (safe bad).elim
        | some result =>
          have tailSafe : matchRows refs (next :: rest) value ≠ none := by simp [tail]
          obtain ⟨insertedSafe, _⟩ := ih tailSafe
          cases inserted : matchRows refs (insertAny (next :: rest)) value with
          | none => exact (insertedSafe inserted).elim
          | some insertedResult =>
            have original : matchRows refs ((pattern, index) :: next :: rest) value =
                some (.success index) := by rw [matchRows, head, tail]
            have updated : matchRows refs (insertAny ((pattern, index) :: next :: rest)) value =
                some (.success index) := by rw [insertAny, matchRows, head, inserted]
            simp [original, updated]

/-- Removing rows cannot introduce a pattern type error. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "matdch_FILTER_NOT_NONE"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_filter_safe (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (predicate : Pat × Nat → Bool)
    (safe : matchRows refs rows value ≠ none) :
    matchRows refs (rows.filter predicate) value ≠ none := by
  induction rows with
  | nil => simp [matchRows]
  | cons row rows ih =>
    obtain ⟨pattern, index⟩ := row
    cases head : pmatch refs pattern value with
    | typeFailure => simp [matchRows, head] at safe
    | failure =>
      have tailSafe : matchRows refs rows value ≠ none := by simpa [matchRows, head] using safe
      by_cases keep : predicate (pattern, index) = true
      · simpa [List.filter, keep, matchRows, head] using ih tailSafe
      · simpa [List.filter, keep] using ih tailSafe
    | success =>
      have tailSafe : matchRows refs rows value ≠ none := by
        cases tail : matchRows refs rows value <;> simp_all [matchRows]
      have filteredSafe := ih tailSafe
      by_cases keep : predicate (pattern, index) = true
      · cases result : matchRows refs (rows.filter predicate) value with
        | none => exact (filteredSafe result).elim
        | some result => simp [List.filter, keep, matchRows, head, result]
      · simpa [List.filter, keep] using filteredSafe

/-- A safe constant row fails on a value that is not a nullary term. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_const_row_lemma"
  (fmap_as_finite_support_parameters := [refs])]
theorem isConstRow_failure {α : Type} (refs : HolFiniteMapExact Nat Term) (value : Term)
    (pattern : Pat) (payload : α) (notNullary : ∀ tag, value ≠ .term tag [])
    (constant : isConstRow (pattern, payload) = true)
    (safe : pmatch refs pattern value ≠ .typeFailure) :
    pmatch refs pattern value = .failure := by
  have notSuccess : pmatch refs pattern value ≠ .success := by
    cases pattern with
    | cons tag patterns =>
      cases patterns with
      | cons first rest => simp [isConstRow] at constant
      | nil =>
        cases value with
        | litv lit => simp [pmatch]
        | refPtr ref => simp [pmatch]
        | other => simp [pmatch]
        | term actual values =>
          cases values with
          | nil => exact (notNullary actual rfl).elim
          | cons first rest =>
            cases tag with
            | none => cases actual <;> simp [pmatch, pmatchList]
            | some tag =>
              obtain ⟨tag, siblings⟩ := tag
              cases actual <;> simp [pmatch] <;> split <;> simp
    | any | lit _ | ref _ | or _ _ => simp [isConstRow] at constant
  cases result : pmatch refs pattern value <;> simp_all

/-- Discarding rows that all fail leaves the selected result unchanged. -/
theorem matchRows_filter_discard_failures (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (predicate : Pat × Nat → Bool)
    (failures : ∀ row ∈ rows, predicate row = true → pmatch refs row.1 value = .failure) :
    matchRows refs (rows.filter (fun row => !predicate row)) value = matchRows refs rows value := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨pattern, index⟩ := row
    have tailFailures : ∀ row ∈ rest, predicate row = true → pmatch refs row.1 value = .failure := by
      intro row member selected
      exact failures row (List.mem_cons_of_mem _ member) selected
    have tailEq := ih tailFailures
    by_cases selected : predicate (pattern, index) = true
    · have head := failures (pattern, index) (by simp) selected
      simpa [List.filter, selected, matchRows, head] using tailEq
    · cases head : pmatch refs pattern value <;>
        simp [List.filter, selected, matchRows, head, tailEq]

/-- A list of rows whose patterns all fail produces match failure. -/
theorem matchRows_all_fail (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat))
    (failures : ∀ row ∈ rows, pmatch refs row.1 value = .failure) :
    matchRows refs rows value = some .failure := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨pattern, index⟩ := row
    have head := failures (pattern, index) (by simp)
    have tailFailures : ∀ row ∈ rest, pmatch refs row.1 value = .failure := by
      intro row member
      exact failures row (List.mem_cons_of_mem _ member)
    simpa [matchRows, head] using ih tailFailures

/-- Moving nullary constructor rows forward preserves matching for values
that are not nullary constructors, provided the original scan is safe. -/
theorem matchRows_moveConstUp_nonNullary (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none)
    (notNullary : ∀ tag, value ≠ .term tag []) :
    matchRows refs (moveConstUp rows) value = matchRows refs rows value := by
  let truncated := takeUntilAny rows
  have truncEq : matchRows refs truncated value = matchRows refs rows value :=
    matchRows_takeUntilAny refs value rows safe
  have truncSafe : matchRows refs truncated value ≠ none := by rw [truncEq]; exact safe
  have failures : ∀ row ∈ truncated, isConstRow row = true → pmatch refs row.1 value = .failure := by
    intro row member constant
    have notTypeFailure := PatternExh.matchRows_member_safe refs value truncated truncSafe row member
    exact isConstRow_failure refs value row.1 row.2 notNullary (by simpa using constant) notTypeFailure
  have filteredFailures : ∀ row ∈ truncated.filter isConstRow, pmatch refs row.1 value = .failure := by
    intro row member
    have membership := List.mem_filter.mp member
    exact failures row membership.1 membership.2
  have selectedFails := matchRows_all_fail refs value (truncated.filter isConstRow) filteredFailures
  have removedEq := matchRows_filter_discard_failures refs value truncated isConstRow failures
  unfold moveConstUp
  change matchRows refs (if 5 ≤ truncated.length || truncated.any isOrRow then truncated else
    truncated.filter isConstRow ++ truncated.filter (fun row => !isConstRow row)) value = _
  split
  · exact truncEq
  · rw [matchRows_append, selectedFails]
    exact removedEq.trans truncEq

/-- A nonconstant row without alternatives or a wildcard cannot match a
nullary constructor. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "not_is_const_row"
  (fmap_as_finite_support_parameters := [refs])]
theorem nonConstRow_not_success_nullary {α : Type} (refs : HolFiniteMapExact Nat Term)
    (tag : Option Nat) (row : Pat × α)
    (nonconstant : isConstRow row = false) (noOr : isOrRow row = false)
    (noAny : isAny row.1 = false) : pmatch refs row.1 (.term tag []) ≠ .success := by
  obtain ⟨pattern, index⟩ := row
  cases pattern with
  | any => simp [isAny] at noAny
  | or _ _ => simp [isOrRow] at noOr
  | lit _ | ref _ => simp [pmatch]
  | cons info patterns =>
    cases patterns with
    | nil => simp [isConstRow] at nonconstant
    | cons first rest =>
      cases info with
      | none => cases tag <;> simp [pmatch, pmatchList]
      | some info =>
        obtain ⟨actual, siblings⟩ := info
        cases tag <;> simp [pmatch] <;> split <;> simp

/-- If every unselected row before the final row fails, moving selected
rows to the front preserves a safe match. -/
theorem matchRows_partition_last (refs : HolFiniteMapExact Nat Term) (value : Term)
    (preRows : List (Pat × Nat)) (last : Pat × Nat) (predicate : Pat × Nat → Bool)
    (safe : matchRows refs (preRows ++ [last]) value ≠ none)
    (failures : ∀ row ∈ preRows, predicate row = false → pmatch refs row.1 value = .failure) :
    matchRows refs ((preRows ++ [last]).filter predicate ++
      (preRows ++ [last]).filter (fun row => !predicate row)) value =
      matchRows refs (preRows ++ [last]) value := by
  have discarded : matchRows refs (preRows.filter predicate) value = matchRows refs preRows value := by
    have h := matchRows_filter_discard_failures refs value preRows (fun row => !predicate row) (by
      intro row member selected
      apply failures row member
      simpa using selected)
    simpa using h
  have unselectedFails : matchRows refs (preRows.filter (fun row => !predicate row)) value = some .failure := by
    apply matchRows_all_fail
    intro row member
    have membership := List.mem_filter.mp member
    apply failures row membership.1
    simpa using membership.2
  have preRowsSafe : matchRows refs preRows value ≠ none := by
    intro bad
    apply safe
    simp [matchRows_append, bad]
  have selectedSafe : matchRows refs (preRows.filter predicate) value ≠ none := by
    rw [discarded]
    exact preRowsSafe
  cases preRowsResult : matchRows refs (preRows.filter predicate) value with
  | none => exact (selectedSafe preRowsResult).elim
  | some result =>
    have originalResult : matchRows refs preRows value = some result := discarded.symm.trans preRowsResult
    cases result <;> by_cases selected : predicate last = true <;>
      cases last with
      | mk pattern index =>
        cases head : pmatch refs pattern value <;>
          simp [List.filter_append, List.filter, matchRows_append, matchRows, selected, head,
            preRowsResult, originalResult, unselectedFails]

/-- Every retained row except the last lacks an unconditional pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "EVERY_take_until_Any"]
theorem every_takeUntilAny (rows : List (Pat × Nat)) :
    ∀ row ∈ (takeUntilAny rows).reverse.tail, isAny row.1 = false := by
  induction rows with
  | nil => simp [takeUntilAny]
  | cons row rows ih =>
    obtain ⟨pattern, payload⟩ := row
    by_cases h : isAny pattern = true
    · simp [takeUntilAny, h]
    · cases hs : (takeUntilAny rows).reverse with
      | nil => simp [takeUntilAny, h, hs]
      | cons first rest =>
        simp only [hs, List.tail_cons] at ih
        simp only [takeUntilAny, h, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, hs,
          List.cons_append, List.tail_cons]
        intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | equal
        · exact ih candidate member
        · subst candidate
          exact Bool.eq_false_iff.mpr h

/-- Moving nullary constructor rows preserves safe matching for nullary values. -/
theorem matchRows_moveConstUp_nullary (refs : HolFiniteMapExact Nat Term) (tag : Option Nat)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows (.term tag []) ≠ none) :
    matchRows refs (moveConstUp rows) (.term tag []) = matchRows refs rows (.term tag []) := by
  let value := Term.term tag []
  let truncated := takeUntilAny rows
  have truncEq : matchRows refs truncated value = matchRows refs rows value :=
    matchRows_takeUntilAny refs value rows safe
  have truncSafe : matchRows refs truncated value ≠ none := by rw [truncEq]; exact safe
  by_cases skip : (5 ≤ truncated.length || truncated.any isOrRow) = true
  · simpa [moveConstUp, truncated, skip] using truncEq
  · have noOr : truncated.any isOrRow = false := by
      cases h : truncated.any isOrRow <;> simp_all
    have noOrMember : ∀ row ∈ truncated, isOrRow row = false := by
      intro row member
      exact Bool.eq_false_iff.mpr ((List.any_eq_false.mp noOr) row member)
    rcases List.eq_nil_or_concat truncated with empty | ⟨preRows, last, decomposition⟩
    · have emptyTake : takeUntilAny rows = [] := empty
      simpa [moveConstUp, emptyTake, matchRows, empty, value] using truncEq
    · have decomposition : truncated = preRows ++ [last] := by simpa using decomposition
      have noAny : ∀ row ∈ preRows, isAny row.1 = false := by
        have h := every_takeUntilAny rows
        have takeEq : takeUntilAny rows = preRows ++ [last] := by simpa [truncated] using decomposition
        rw [takeEq] at h
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append] at h
        intro row member
        exact h row (List.mem_reverse.mpr member)
      have failures : ∀ row ∈ preRows, isConstRow row = false → pmatch refs row.1 value = .failure := by
        intro row member nonconstant
        have inTruncated : row ∈ truncated := by rw [decomposition]; simp [member]
        have notSuccess := nonConstRow_not_success_nullary refs tag row nonconstant
          (noOrMember row inTruncated) (noAny row member)
        have notTypeFailure := PatternExh.matchRows_member_safe refs value truncated truncSafe row inTruncated
        cases result : pmatch refs row.1 value with
        | success => exact (notSuccess result).elim
        | typeFailure => exact (notTypeFailure result).elim
        | failure => rfl
      have partitionEq := matchRows_partition_last refs value preRows last isConstRow (by
        simpa [← decomposition] using truncSafe) failures
      have reordered : matchRows refs (truncated.filter isConstRow ++
          truncated.filter (fun row => !isConstRow row)) value = matchRows refs truncated value := by
        simpa [← decomposition] using partitionEq
      simpa [moveConstUp, truncated, skip] using reordered.trans truncEq

/-- Moving nullary constructor rows preserves every non-error match result. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "match_move_const_up"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_moveConstUp (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none) :
    matchRows refs (moveConstUp rows) value = matchRows refs rows value := by
  by_cases nullary : ∃ tag, value = .term tag []
  · obtain ⟨tag, rfl⟩ := nullary
    exact matchRows_moveConstUp_nullary refs tag rows safe
  · apply matchRows_moveConstUp_nonNullary refs value rows safe
    intro tag equal
    exact nullary ⟨tag, equal⟩

end Flapjack.Compiler.Backend.PatternComp
