module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
public import Flapjack.SemanticPrimitivesProps.MatchMap

@[expose] public section

/-! Appending environments in flat pattern matching. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (MatchResult storeLookup)
open Flapjack.SemanticPrimitivesProps (mapMatch)

mutual
/-- Pattern matching only adds bindings in front of the incoming environment. -/
private theorem pmatch_append_bindings {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (value : Value) (pre suffix : List (VarN × Value)) :
    FlatSem.pmatch state pattern value (pre ++ suffix) =
      mapMatch (fun items => items ++ suffix) (FlatSem.pmatch state pattern value pre) := by
  cases pattern with
  | pany => simp [FlatSem.pmatch, mapMatch]
  | pvar name => simp [FlatSem.pmatch, mapMatch]
  | plit lit =>
    cases value <;> simp [FlatSem.pmatch, mapMatch]
    case litv actual =>
      split
      · simp
      · split <;> simp
  | pas pattern name =>
    simpa [FlatSem.pmatch] using pmatch_append_bindings state pattern value ((name, value) :: pre) suffix
  | pref pattern =>
    cases value <;> simp [FlatSem.pmatch, mapMatch]
    case loc flag index =>
      cases found : storeLookup index state.refs with
      | none => rfl
      | some entry =>
        cases entry <;> try rfl
        case refv contents => exact pmatch_append_bindings state pattern contents pre suffix
  | pcon stamp patterns =>
    cases value <;> simp [FlatSem.pmatch, mapMatch]
    case conv actual values =>
      by_cases ok : PmatchStampsOk stamp actual patterns.length values.length
      · by_cases same : stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = values.length
        · simpa only [if_pos ok, if_pos same, mapMatch] using
            pmatchList_append_bindings state patterns values pre suffix
        · simp only [if_pos ok, if_neg same]
      · simp [ok]
termination_by sizeOf pattern

/-- List matching preserves an unchanged suffix in successful bindings and
preserves non-match and type-error outcomes. -/
private theorem pmatchList_append_bindings {C F : Type} (state : FlatSem.State C F)
    (patterns : List FlatLang.Pat) (values : List Value) (pre suffix : List (VarN × Value)) :
    FlatSem.pmatchList state patterns values (pre ++ suffix) =
      mapMatch (fun items => items ++ suffix) (FlatSem.pmatchList state patterns values pre) := by
  cases patterns with
  | nil => cases values <;> simp [FlatSem.pmatchList, mapMatch]
  | cons pattern patterns =>
    cases values with
    | nil => simp [FlatSem.pmatchList, mapMatch]
    | cons value values =>
      have head := pmatch_append_bindings state pattern value pre suffix
      cases result : FlatSem.pmatch state pattern value pre with
      | typeError => simp [FlatSem.pmatchList, head, result, mapMatch]
      | «match» bindings =>
        simpa [FlatSem.pmatchList, head, result, mapMatch] using
          pmatchList_append_bindings state patterns values bindings suffix
      | noMatch =>
        have tail := pmatchList_append_bindings state patterns values pre suffix
        cases tailResult : FlatSem.pmatchList state patterns values pre <;>
          simp_all [FlatSem.pmatchList, mapMatch]
termination_by sizeOf patterns
end

/-- Appending a suffix to the incoming bindings maps each successful result
with the same suffix, for both patterns and pattern lists. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_append"]
theorem pmatch_append {C F α β : Type} (suffix : List (VarN × Value)) :
    (∀ (state : FlatSem.State C F) pattern value bindings (_unused : α),
      mapMatch (fun items => items ++ suffix) (FlatSem.pmatch state pattern value bindings) =
        FlatSem.pmatch state pattern value (bindings ++ suffix)) ∧
    (∀ (state : FlatSem.State C F) patterns values bindings (_unused : β),
      mapMatch (fun items => items ++ suffix) (FlatSem.pmatchList state patterns values bindings) =
        FlatSem.pmatchList state patterns values (bindings ++ suffix)) := by
  constructor
  · intro state pattern value bindings _
    exact (pmatch_append_bindings state pattern value bindings suffix).symm
  · intro state patterns values bindings _
    exact (pmatchList_append_bindings state patterns values bindings suffix).symm

end Flapjack.Compiler.Backend.FlatProps
