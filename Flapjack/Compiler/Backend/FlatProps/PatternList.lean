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

/-- Matching with bindings is the empty-binding result with those bindings appended. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_nil"]
theorem pmatchNil {C F : Type} :
    (∀ (value : Value) (tail : List (VarN × Value)) (state : FlatSem.State C F) pattern,
      FlatSem.pmatch state pattern value tail =
        Flapjack.SemanticPrimitivesProps.mapMatch (fun items => items ++ tail)
          (FlatSem.pmatch state pattern value [])) ∧
    (∀ (values : List Value) (tail : List (VarN × Value)) (state : FlatSem.State C F) patterns,
      FlatSem.pmatchList state patterns values tail =
        Flapjack.SemanticPrimitivesProps.mapMatch (fun items => items ++ tail)
          (FlatSem.pmatchList state patterns values [])) := by
  constructor
  · intro value tail state pattern
    simpa using ((pmatch_append (α := Unit) (β := Unit) tail).1 state pattern value [] ()).symm
  · intro values tail state patterns
    simpa using ((pmatch_append (α := Unit) (β := Unit) tail).2 state patterns values [] ()).symm

/-- Flapjack proof infrastructure: track the binding accumulator in variable-list matching. -/
private theorem matchVarsAux {C F : Type} (state : State C F)
    (xs : List Flapjack.AstHOL.VarN) (vs : List Value) (bindings : List (Flapjack.AstHOL.VarN × Value))
    (len : xs.length = vs.length) :
    pmatchList state (xs.map FlatLang.Pat.pvar) vs bindings = .match ((xs.zip vs).reverse ++ bindings) := by
  induction xs generalizing vs bindings with
  | nil => cases vs <;> simp_all [pmatchList]
  | cons x xs ih =>
    cases vs with
    | nil => simp at len
    | cons v vs =>
      have lenTail : xs.length = vs.length := by simpa using len
      simpa [pmatchList, pmatch, List.reverse_cons, List.append_assoc] using ih vs ((x, v) :: bindings) lenTail

/-- Equal-length variable patterns bind the values in reverse pair order. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_list_MAP_Pvar"]
theorem pmatchList_mapPvar {C F : Type} (state : State C F) :
    ∀ (xs : List Flapjack.AstHOL.VarN) (vs : List Value), xs.length = vs.length →
      pmatchList state (xs.map FlatLang.Pat.pvar) vs [] = .match ((xs.zip vs).reverse) := by
  intro xs vs length
  simpa using matchVarsAux state xs vs [] length
end Flapjack.Compiler.Backend.FlatProps
