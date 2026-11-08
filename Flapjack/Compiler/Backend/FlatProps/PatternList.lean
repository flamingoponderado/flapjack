import Flapjack.Compiler.Backend.FlatProps.PatternOutcome

/-! Pattern list matching over appended lists. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem

/-- A nonempty list paired with an empty list raises a match type error. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_list_snoc_nil"]
theorem pmatchListSnocNil {C F : Type} (p : FlatLang.Pat) (ps : List FlatLang.Pat) (v : Value) (vs : List Value)
    (state : FlatSem.State C F) (env : List (VarN × Value)) :
    FlatSem.pmatchList state [] (vs ++ [v]) env = .typeError ∧
    FlatSem.pmatchList state (ps ++ [p]) [] env = .typeError := by
  cases ps <;> cases vs <;> simp [FlatSem.pmatchList]

/-- Matching appended lists checks both halves and preserves errors and bindings. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_list_append"]
theorem pmatchListAppend {C F : Type} (ps : List FlatLang.Pat) (vs : List Value) (ps' : List FlatLang.Pat) (vs' : List Value)
    (state : FlatSem.State C F) (env : List (VarN × Value)) (lengths : ps.length = vs.length) :
    FlatSem.pmatchList state (ps ++ ps') (vs ++ vs') env =
      match FlatSem.pmatchList state ps vs env with
      | .match env' => FlatSem.pmatchList state ps' vs' env'
      | .typeError => .typeError
      | .noMatch => match FlatSem.pmatchList state ps' vs' env with
        | .typeError => .typeError
        | _ => .noMatch := by
  have errorStable (a b : List (VarN × Value)) :
      (FlatSem.pmatchList state ps' vs' a = .typeError ↔
       FlatSem.pmatchList state ps' vs' b = .typeError) :=
    ⟨fun h => (pmatchAnyError (C := C) (F := F)).2 state ps' vs' a h b,
     fun h => (pmatchAnyError (C := C) (F := F)).2 state ps' vs' b h a⟩
  induction ps generalizing vs env with
  | nil =>
    cases vs with
    | nil => simp [FlatSem.pmatchList]
    | cons _ _ => simp at lengths
  | cons p ps ih =>
    cases vs with
    | nil => simp at lengths
    | cons v vs =>
      have tailLengths : ps.length = vs.length := by simpa using lengths
      cases head : FlatSem.pmatch state p v env with
      | typeError => simp [FlatSem.pmatchList, head]
      | «match» next =>
        have recurse := ih vs next tailLengths
        cases tail : FlatSem.pmatchList state ps vs next with
        | typeError => simpa [FlatSem.pmatchList, head, tail] using recurse
        | noMatch =>
          have stable := errorStable next env
          cases a : FlatSem.pmatchList state ps' vs' next <;>
            cases b : FlatSem.pmatchList state ps' vs' env <;>
            simp_all [FlatSem.pmatchList]
        | «match» result => simpa [FlatSem.pmatchList, head, tail] using recurse
      | noMatch =>
        have recurse := ih vs env tailLengths
        cases tail : FlatSem.pmatchList state ps vs env with
        | typeError => simp_all [FlatSem.pmatchList]
        | noMatch => cases last : FlatSem.pmatchList state ps' vs' env <;> simp_all [FlatSem.pmatchList]
        | «match» result =>
          have stable := errorStable result env
          cases a : FlatSem.pmatchList state ps' vs' result <;>
            cases b : FlatSem.pmatchList state ps' vs' env <;>
            simp_all [FlatSem.pmatchList]

/-- Appending one pattern and value preserves the preceding match outcome. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_list_snoc"]
theorem pmatchListSnoc {C F : Type} (ps : List FlatLang.Pat) (vs : List Value) (p : FlatLang.Pat) (v : Value)
    (state : FlatSem.State C F) (env : List (VarN × Value)) (lengths : ps.length = vs.length) :
    FlatSem.pmatchList state (ps ++ [p]) (vs ++ [v]) env =
      match FlatSem.pmatchList state ps vs env with
      | .match env' => FlatSem.pmatch state p v env'
      | .typeError => .typeError
      | .noMatch => match FlatSem.pmatch state p v env with
        | .typeError => .typeError
        | _ => .noMatch := by
  rw [pmatchListAppend ps vs [p] [v] state env lengths]
  cases FlatSem.pmatchList state ps vs env <;>
    simp only [FlatSem.pmatchList]
  all_goals cases FlatSem.pmatch state p v _ <;> simp

/-- Mapping a match changes its payload and leaves either failure unchanged. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "map_match_eq_case"]
theorem mapMatchEqCase {α : Type} (f : α → α)
    (value : Flapjack.SemanticPrimitivesHOL.MatchResult α) :
    Flapjack.SemanticPrimitivesProps.mapMatch f value =
      match value with
      | .match result => .match (f result)
      | other => other := by
  cases value <;> rfl

end Flapjack.Compiler.Backend.FlatProps
