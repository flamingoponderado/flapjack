import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Pattern matching for the flat-language evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Original constructor-stamp compatibility relation. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "pmatch_stamps_ok"]
inductive PmatchStampsOk {α β γ : Type} : Option (α × Option (β × List (α × γ))) →
    Option (α × Option β) → γ → γ → Prop where
  | exception (cn cn' np nv) : PmatchStampsOk (some (cn, none)) (some (cn', none)) np nv
  | constructor (cn cn' ty ty' constructors np nv)
      (typeEq : ty = ty') (patternMem : (cn, np) ∈ constructors)
      (valueMem : (cn', nv) ∈ constructors) :
      PmatchStampsOk (some (cn, some (ty, constructors))) (some (cn', some ty')) np nv
  | tuple (np nv) (lengthEq : np = nv) : PmatchStampsOk none none np nv

/-- Flapjack-specific decidable case analysis for the original stamp relation. -/
def pmatchStampsOk {α β γ : Type} : Option (α × Option (β × List (α × γ))) →
    Option (α × Option β) → γ → γ → Prop
  | some (_, none), some (_, none), _, _ => True
  | some (cn, some (ty, constructors)), some (cn', some ty'), np, nv =>
    ty = ty' ∧ (cn, np) ∈ constructors ∧ (cn', nv) ∈ constructors
  | none, none, np, nv => np = nv
  | _, _, _, _ => False

/-- Flapjack-specific equivalence between the case analysis and the inductive relation. -/
theorem pmatchStampsOk_iff {α β γ : Type} (p : Option (α × Option (β × List (α × γ))))
    (v : Option (α × Option β)) (np nv : γ) :
    pmatchStampsOk p v np nv ↔ PmatchStampsOk p v np nv := by
  constructor
  · intro h
    rcases p with _ | ⟨cn, _ | ⟨ty, cs⟩⟩ <;>
      rcases v with _ | ⟨cn', _ | ty'⟩ <;> simp [pmatchStampsOk] at h
    · exact .tuple np nv h
    · exact .exception cn cn' np nv
    · exact .constructor cn cn' ty ty' cs np nv h.1 h.2.1 h.2.2
  · intro h
    cases h <;> simp_all [pmatchStampsOk]

instance {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : Option (α × Option (β × List (α × γ))))
    (v : Option (α × Option β)) (np nv : γ) :
    Decidable (PmatchStampsOk p v np nv) := by
  have : Decidable (pmatchStampsOk p v np nv) := by
    unfold pmatchStampsOk
    split <;> infer_instance
  exact decidable_of_iff (pmatchStampsOk p v np nv) (pmatchStampsOk_iff p v np nv)

mutual
/-- Match a flat pattern against a value, preserving the original error behavior. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "pmatch_def"]
def pmatch {C F : Type} (state : State C F) (pattern : FlatLang.Pat) (value : Value)
    (bindings : List (VarN × Value)) : MatchResult (List (VarN × Value)) :=
  match pattern, value with
  | .pvar name, _ => .match ((name, value) :: bindings)
  | .pany, _ => .match bindings
  | .plit lit, .litv actual =>
    if lit = actual then .match bindings else if litSameType lit actual then .noMatch else .typeError
  | .pcon stamp patterns, .conv actual values =>
    if ¬PmatchStampsOk stamp actual patterns.length values.length then .typeError
    else if stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = values.length then
      pmatchList state patterns values bindings
    else .noMatch
  | .pas pattern name, _ => pmatch state pattern value ((name, value) :: bindings)
  | .pref pattern, .loc _ index =>
    match storeLookup index state.refs with
    | some (.refv value) => pmatch state pattern value bindings
    | _ => .typeError
  | _, _ => .typeError
termination_by sizeOf pattern

/-- Match pattern and value lists, retaining type errors after an earlier mismatch. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "pmatch_def"]
def pmatchList {C F : Type} (state : State C F) (patterns : List FlatLang.Pat) (values : List Value)
    (bindings : List (VarN × Value)) : MatchResult (List (VarN × Value)) :=
  match patterns, values with
  | [], [] => .match bindings
  | pattern :: patterns, value :: values =>
    match pmatch state pattern value bindings with
    | .typeError => .typeError
    | .match next => pmatchList state patterns values next
    | .noMatch => match pmatchList state patterns values bindings with
      | .typeError => .typeError
      | _ => .noMatch
  | _, _ => .typeError
termination_by sizeOf patterns
end

/-- Select the first matching row, unless any row produces a type error. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "pmatch_rows_def"]
def pmatchRows {C F E : Type} (rows : List (FlatLang.Pat × E))
    (state : State C F) (value : Value) : MatchResult (List (VarN × Value) × FlatLang.Pat × E) :=
  match rows with
  | [] => .noMatch
  | (pattern, expr) :: rest =>
    match pmatch state pattern value [] with
    | .typeError => .typeError
    | .noMatch => pmatchRows rest state value
    | .match env => match pmatchRows rest state value with
      | .typeError => .typeError
      | _ => .match (env, pattern, expr)
end Flapjack.Compiler.Backend.FlatSem
