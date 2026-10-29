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

end Flapjack.Compiler.Backend.PatternComp
