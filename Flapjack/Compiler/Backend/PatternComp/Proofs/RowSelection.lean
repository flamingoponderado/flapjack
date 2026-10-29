import Flapjack.Compiler.Backend.PatternComp.Decision
import Flapjack.Compiler.Backend.PatternSemantics.Semantics

/-! Row-selection lemmas for the pattern compiler. The finite-map carrier
and abstract matcher remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.PatternComp
open Flapjack PatternCommon PatternSemantics

/-- A pattern containing an unconditional alternative cannot return a
non-match, though it may still report a type failure. -/
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
theorem matchRows_append (refs : HolFiniteMapExact Nat Term) (value : Term)
    (left right : List (Pat × Nat)) :
    matchRows refs (left ++ right) value =
      match matchRows refs left value with
      | none => none
      | some (.success index) => if (matchRows refs right value).isSome then some (.success index) else none
      | some .failure => matchRows refs right value := by
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

/-- Truncating after an unconditional row preserves any non-error result. -/
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

/-- A nullary constructor cannot match a non-nullary term or a non-term. -/
theorem isConstRow_not_success (refs : HolFiniteMapExact Nat Term) (value : Term)
    (row : Pat × Nat) (constant : isConstRow row = true)
    (notNullary : ∀ tag, value ≠ .term tag []) : pmatch refs row.1 value ≠ .success := by
  obtain ⟨pattern, index⟩ := row
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

/-- Every row in a successful row scan is individually free of type errors. -/
theorem matchRows_member_safe (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none)
    (row : Pat × Nat) (member : row ∈ rows) : pmatch refs row.1 value ≠ .typeFailure := by
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨pattern, index⟩ := first
    have headSafe : pmatch refs pattern value ≠ .typeFailure := by
      intro bad
      apply safe
      rw [matchRows, bad]
    have tailSafe : matchRows refs rest value ≠ none := by
      cases head : pmatch refs pattern value with
      | typeFailure => exact (headSafe head).elim
      | failure => simpa [matchRows, head] using safe
      | success =>
        cases tail : matchRows refs rest value with
        | none =>
          apply False.elim
          apply safe
          rw [matchRows, head, tail]
        | some result => simp
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst row
      exact headSafe
    · exact ih tailSafe member

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
    have notSuccess := isConstRow_not_success refs value row constant notNullary
    have notTypeFailure := matchRows_member_safe refs value truncated truncSafe row member
    cases result : pmatch refs row.1 value with
    | success => exact (notSuccess result).elim
    | typeFailure => exact (notTypeFailure result).elim
    | failure => rfl
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
theorem nonConstRow_not_success_nullary (refs : HolFiniteMapExact Nat Term)
    (tag : Option Nat) (row : Pat × Nat)
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

end Flapjack.Compiler.Backend.PatternComp
