import Flapjack.Compiler.Backend.FlatProps.PatternAppend
import Batteries.Data.List.Basic
/-! Pattern-match outcome independence from incoming bindings. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (MatchResult)
open Flapjack.SemanticPrimitivesProps (mapMatch)

/-- Flapjack proof infrastructure: an append law fixes the result constructor. -/
private theorem outcomeChange {α : Type} (run : List α → MatchResult (List α))
    (law : ∀ tail, mapMatch (fun items => items ++ tail) (run []) = run tail)
    (left right : List α) :
    (run left = .noMatch → run right = .noMatch) ∧
    (run left = .typeError → run right = .typeError) ∧
    (∀ result, run left = .match result → ∃ result', run right = .match result') := by
  have first := law left
  have second := law right
  cases initial : run [] <;>
    simp only [initial, mapMatch] at first second <;>
    rw [← first, ← second] <;> simp

/-- Flapjack proof infrastructure shared by the three HOL outcome theorems. -/
private theorem pmatchChange {C F : Type} (state : FlatSem.State C F) :
    (∀ pattern value left right,
      (FlatSem.pmatch state pattern value left = .noMatch → FlatSem.pmatch state pattern value right = .noMatch) ∧
      (FlatSem.pmatch state pattern value left = .typeError → FlatSem.pmatch state pattern value right = .typeError) ∧
      (∀ result, FlatSem.pmatch state pattern value left = .match result →
        ∃ result', FlatSem.pmatch state pattern value right = .match result')) ∧
    (∀ patterns values left right,
      (FlatSem.pmatchList state patterns values left = .noMatch → FlatSem.pmatchList state patterns values right = .noMatch) ∧
      (FlatSem.pmatchList state patterns values left = .typeError → FlatSem.pmatchList state patterns values right = .typeError) ∧
      (∀ result, FlatSem.pmatchList state patterns values left = .match result →
        ∃ result', FlatSem.pmatchList state patterns values right = .match result')) := by
  constructor
  · intro pattern value left right
    apply outcomeChange (FlatSem.pmatch state pattern value) _ left right
    intro tail
    simpa using (pmatch_append (α := Unit) (β := Unit) tail).1 state pattern value [] ()
  · intro patterns values left right
    apply outcomeChange (FlatSem.pmatchList state patterns values) _ left right
    intro tail
    simpa using (pmatch_append (α := Unit) (β := Unit) tail).2 state patterns values [] ()

/-- A successful match remains successful with any incoming bindings. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_any_match"]
theorem pmatchAnyMatch {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value env result,
      FlatSem.pmatch state pattern value env = .match result →
        ∀ other, ∃ result', FlatSem.pmatch state pattern value other = .match result') ∧
    (∀ (state : FlatSem.State C F) patterns values env result,
      FlatSem.pmatchList state patterns values env = .match result →
        ∀ other, ∃ result', FlatSem.pmatchList state patterns values other = .match result') := by
  constructor
  · intro state pattern value env result run other
    exact (pmatchChange state).1 pattern value env other |>.2.2 result run
  · intro state patterns values env result run other
    exact (pmatchChange state).2 patterns values env other |>.2.2 result run

/-- A non-match remains a non-match with any incoming bindings. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_any_no_match"]
theorem pmatchAnyNoMatch {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value env,
      FlatSem.pmatch state pattern value env = .noMatch →
        ∀ other, FlatSem.pmatch state pattern value other = .noMatch) ∧
    (∀ (state : FlatSem.State C F) patterns values env,
      FlatSem.pmatchList state patterns values env = .noMatch →
        ∀ other, FlatSem.pmatchList state patterns values other = .noMatch) := by
  constructor
  · intro state pattern value env run other
    exact (pmatchChange state).1 pattern value env other |>.1 run
  · intro state patterns values env run other
    exact (pmatchChange state).2 patterns values env other |>.1 run

/-- A match type error remains a type error with any incoming bindings. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_any_match_error"]
theorem pmatchAnyError {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value env,
      FlatSem.pmatch state pattern value env = .typeError →
        ∀ other, FlatSem.pmatch state pattern value other = .typeError) ∧
    (∀ (state : FlatSem.State C F) patterns values env,
      FlatSem.pmatchList state patterns values env = .typeError →
        ∀ other, FlatSem.pmatchList state patterns values other = .typeError) := by
  constructor
  · intro state pattern value env run other
    exact (pmatchChange state).1 pattern value env other |>.2.1 run
  · intro state patterns values env run other
    exact (pmatchChange state).2 patterns values env other |>.2.1 run
/-- Successful list matching entails successful matching of each pair, for any incoming bindings. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_list_pairwise"]
theorem pmatchListPairwise {C F : Type} (patterns : List FlatLang.Pat) (values : List Value)
    (state : FlatSem.State C F) (env result : List (VarN × Value))
    (matched : FlatSem.pmatchList state patterns values env = .match result) :
    List.Forall₂ (fun p v => ∀ env, ∃ result, FlatSem.pmatch state p v env = .match result) patterns values := by
  induction patterns generalizing values env result with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons v vs => simp [FlatSem.pmatchList] at matched
  | cons p ps ih =>
    cases values with
    | nil => simp [FlatSem.pmatchList] at matched
    | cons v vs =>
      cases head : FlatSem.pmatch state p v env with
      | typeError => simp [FlatSem.pmatchList, head] at matched
      | noMatch =>
        simp only [FlatSem.pmatchList, head] at matched
        cases tail : FlatSem.pmatchList state ps vs env <;> simp_all
      | «match» next =>
        have tail : FlatSem.pmatchList state ps vs next = .match result := by
          simpa [FlatSem.pmatchList, head] using matched
        exact .cons (fun other => (pmatchAnyMatch (C := C) (F := F)).1 state p v env next head other) (ih vs next result tail)

end Flapjack.Compiler.Backend.FlatProps
