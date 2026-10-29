import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Successful pattern-list matches for the pattern-binding simulation.
These proof-side statements await HOL carrier and statement review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem

/-- Successful list matching consumes exactly one value per pattern. -/
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

/-- Successful matches of successive pattern lists compose. -/
theorem pmatchList_append_match {C F : Type} (state : FlatSem.State C F)
    (left right : List FlatLang.Pat) (leftValues rightValues : List Value)
    (bindings intermediate result : List (VarN × Value))
    (first : FlatSem.pmatchList state left leftValues bindings = .match intermediate)
    (second : FlatSem.pmatchList state right rightValues intermediate = .match result) :
    FlatSem.pmatchList state (left ++ right) (leftValues ++ rightValues) bindings = .match result := by
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
        simpa [FlatSem.pmatchList, head] using ih leftValues next tail

/-- A successful match of appended pattern lists splits at the boundary,
including the intermediate bindings. -/
theorem pmatchList_append_match_split {C F : Type} (state : FlatSem.State C F)
    (left right : List FlatLang.Pat) (values : List Value)
    (bindings result : List (VarN × Value))
    (matched : FlatSem.pmatchList state (left ++ right) values bindings = .match result) :
    ∃ leftValues rightValues intermediate, values = leftValues ++ rightValues ∧
      FlatSem.pmatchList state left leftValues bindings = .match intermediate ∧
      FlatSem.pmatchList state right rightValues intermediate = .match result := by
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

/-- Appended pattern lists match successfully exactly when their matches can
be split into consecutive successful matches. -/
theorem pmatchList_append_match_iff {C F : Type} (state : FlatSem.State C F)
    (left right : List FlatLang.Pat) (values : List Value) (bindings result : List (VarN × Value)) :
    FlatSem.pmatchList state (left ++ right) values bindings = .match result ↔
      ∃ leftValues rightValues intermediate, values = leftValues ++ rightValues ∧
        FlatSem.pmatchList state left leftValues bindings = .match intermediate ∧
        FlatSem.pmatchList state right rightValues intermediate = .match result := by
  constructor
  · exact pmatchList_append_match_split state left right values bindings result
  · rintro ⟨leftValues, rightValues, intermediate, rfl, first, second⟩
    exact pmatchList_append_match state left right leftValues rightValues bindings intermediate result first second

end Flapjack.Compiler.Backend.FlatPattern
