import Flapjack.Compiler.Backend.FlatProps.PatternAppend

/-! Successful pattern-list matches for the pattern-binding simulation.
The untagged supporting statements are reviewed independently. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (MatchResult storeLookup)

/-- Successful list matching consumes exactly one value per pattern. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "pmatch_list_Match_IMP_LENGTH"]
theorem pmatchList_match_length {C F : Type} (state : FlatSem.State C F)
    (patterns : List FlatLang.Pat) (values : List Value) (bindings result : List (VarN × Value))
    (matched : FlatSem.pmatchList state patterns values bindings = .match result) :
    patterns.length = values.length := by
  induction patterns generalizing values bindings with
  | nil =>
    cases values <;> simp [FlatSem.pmatchList] at matched ⊢
  | cons pattern patterns ih =>
    cases values with
    | nil => simp [FlatSem.pmatchList] at matched
    | cons value values =>
      cases head : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [FlatSem.pmatchList, head] at matched
      | noMatch =>
        cases tail : FlatSem.pmatchList state patterns values bindings <;>
          simp [FlatSem.pmatchList, head, tail] at matched
      | «match» next =>
        have tail : FlatSem.pmatchList state patterns values next = .match result := by
          simpa [FlatSem.pmatchList, head] using matched
        simp [ih values next tail]

/-- Equal-length prefixes can be cancelled from equal concatenations. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "APPEND_LENGTH_EQ"]
theorem appendLengthEq {A : Type} (xs xs' ys ys' : List A) (lengths : xs.length = xs'.length) :
    xs ++ ys = xs' ++ ys' ↔ xs = xs' ∧ ys = ys' := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil => simp
    | cons x xs' => simp at lengths
  | cons x xs ih =>
    cases xs' with
    | nil => simp at lengths
    | cons x' xs' =>
      have tailLengths : xs.length = xs'.length := by simpa using lengths
      simp only [List.cons_append, List.cons.injEq]
      rw [ih xs' tailLengths]
      simp [and_assoc]

/-- Appended pattern lists match successfully exactly when their matches can
be split into consecutive successful matches. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "pmatch_list_append_Match_exists"]
theorem pmatchList_append_match_iff {C F : Type} (state : FlatSem.State C F)
    (left right : List FlatLang.Pat) (values : List Value) (bindings result : List (VarN × Value)) :
    FlatSem.pmatchList state (left ++ right) values bindings = .match result ↔
      ∃ leftValues rightValues intermediate, values = leftValues ++ rightValues ∧
        FlatSem.pmatchList state left leftValues bindings = .match intermediate ∧
        FlatSem.pmatchList state right rightValues intermediate = .match result := by
  constructor
  · intro matched
    induction left generalizing values bindings with
    | nil => exact ⟨[], values, bindings, rfl, by simp [FlatSem.pmatchList], matched⟩
    | cons pattern left ih =>
      cases values with
      | nil => simp [FlatSem.pmatchList] at matched
      | cons value values =>
        cases head : FlatSem.pmatch state pattern value bindings with
        | typeError => simp [FlatSem.pmatchList, head] at matched
        | noMatch =>
          cases tail : FlatSem.pmatchList state (left ++ right) values bindings <;>
            simp [FlatSem.pmatchList, head, tail] at matched
        | «match» next =>
          have tail : FlatSem.pmatchList state (left ++ right) values next = .match result := by
            simpa [FlatSem.pmatchList, head] using matched
          obtain ⟨leftValues, rightValues, intermediate, split, first, second⟩ := ih values next tail
          refine ⟨value :: leftValues, rightValues, intermediate, ?_, ?_, second⟩
          · simp [split]
          · simpa [FlatSem.pmatchList, head] using first
  · rintro ⟨leftValues, rightValues, intermediate, rfl, first, second⟩
    induction left generalizing leftValues bindings with
    | nil =>
      cases leftValues with
      | nil =>
        simp [FlatSem.pmatchList] at first
        subst intermediate
        simpa using second
      | cons _ _ => simp [FlatSem.pmatchList] at first
    | cons pattern left ih =>
      cases leftValues with
      | nil => simp [FlatSem.pmatchList] at first
      | cons value leftValues =>
        cases head : FlatSem.pmatch state pattern value bindings with
        | typeError => simp [FlatSem.pmatchList, head] at first
        | noMatch =>
          cases tail : FlatSem.pmatchList state left leftValues bindings <;>
            simp [FlatSem.pmatchList, head, tail] at first
        | «match» next =>
          have tail : FlatSem.pmatchList state left leftValues next = .match intermediate := by
            simpa [FlatSem.pmatchList, head] using first
          simpa [FlatSem.pmatchList, head] using ih next leftValues tail

end Flapjack.Compiler.Backend.FlatPattern
