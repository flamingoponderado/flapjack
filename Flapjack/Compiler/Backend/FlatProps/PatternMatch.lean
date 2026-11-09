module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

@[expose] public section

/-! Flat pattern-matching properties. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Equality for matching states with the same reference store, used to prove
the source-shaped state and clock preservation theorems. -/
private theorem pmatch_refs_eq {C D F : Type} (first : FlatSem.State C F) (second : FlatSem.State D F)
    (refs : first.refs = second.refs) :
    (∀ pattern value bindings, FlatSem.pmatch first pattern value bindings =
      FlatSem.pmatch second pattern value bindings) ∧
    (∀ patterns values bindings, FlatSem.pmatchList first patterns values bindings =
      FlatSem.pmatchList second patterns values bindings) := by
  have one : ∀ pattern : FlatLang.Pat, ∀ value bindings,
      FlatSem.pmatch first pattern value bindings = FlatSem.pmatch second pattern value bindings := by
    apply FlatLang.Pat.rec
      (motive_1 := fun pattern => ∀ value bindings,
        FlatSem.pmatch first pattern value bindings = FlatSem.pmatch second pattern value bindings)
      (motive_2 := fun patterns => ∀ values bindings,
        FlatSem.pmatchList first patterns values bindings = FlatSem.pmatchList second patterns values bindings)
    case pany => intros; simp [FlatSem.pmatch]
    case pvar => intros; simp [FlatSem.pmatch]
    case plit => intro lit value bindings; cases value <;> simp [FlatSem.pmatch]
    case pcon =>
      intro stamp patterns ih value bindings
      cases value <;> simp [FlatSem.pmatch]
      case conv actual values =>
        split <;> simp_all
    case pref =>
      intro pattern ih value bindings
      cases value <;> simp [FlatSem.pmatch]
      case loc flag index =>
        simp only [refs]
        cases storeLookup index second.refs <;> simp_all
    case pas =>
      intro pattern name ih value bindings
      simpa [FlatSem.pmatch] using ih value ((name, value) :: bindings)
    case nil => intro values bindings; cases values <;> simp [FlatSem.pmatchList]
    case cons =>
      intro pattern patterns ihHead ihTail values bindings
      cases values with
      | nil => simp [FlatSem.pmatchList]
      | cons value values =>
        simp only [FlatSem.pmatchList, ihHead value bindings]
        cases FlatSem.pmatch second pattern value bindings <;> simp_all
  refine ⟨one, ?_⟩
  intro patterns
  induction patterns with
  | nil => intro values bindings; cases values <;> simp [FlatSem.pmatchList]
  | cons pattern patterns ih =>
    intro values bindings
    cases values with
    | nil => simp [FlatSem.pmatchList]
    | cons value values =>
      simp only [FlatSem.pmatchList, one pattern value bindings]
      cases FlatSem.pmatch second pattern value bindings <;> simp_all

/-- Matching depends on the state only through its reference store, even when
the states have different compiler-state types. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_state"]
theorem pmatch_state {C D F : Type} :
    (∀ (state : FlatSem.State C F) pattern value bindings (next : FlatSem.State D F) result,
      FlatSem.pmatch state pattern value bindings = result ∧ state.refs = next.refs →
        FlatSem.pmatch next pattern value bindings = result) ∧
    (∀ (state : FlatSem.State C F) patterns values bindings (next : FlatSem.State D F) result,
      FlatSem.pmatchList state patterns values bindings = result ∧ state.refs = next.refs →
        FlatSem.pmatchList next patterns values bindings = result) := by
  constructor
  · intro state pattern value bindings next result ⟨run, refs⟩
    exact ((pmatch_refs_eq state next refs).1 pattern value bindings).symm.trans run
  · intro state patterns values bindings next result ⟨run, refs⟩
    exact ((pmatch_refs_eq state next refs).2 patterns values bindings).symm.trans run

/-- A clock update leaves single-pattern and pattern-list matching unchanged. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_ignore_clock"]
theorem pmatch_ignoreClock {C F : Type} (state : FlatSem.State C F) (clock : Nat)
    (pattern : FlatLang.Pat) (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value))
    (patterns : List FlatLang.Pat) (values : List FlatSem.Value) :
    FlatSem.pmatch { state with clock := clock } pattern value bindings = FlatSem.pmatch state pattern value bindings ∧
    FlatSem.pmatchList { state with clock := clock } patterns values bindings = FlatSem.pmatchList state patterns values bindings :=
  ⟨pmatch_state.1 state pattern value bindings _ _ ⟨rfl, rfl⟩,
    pmatch_state.2 state patterns values bindings _ _ ⟨rfl, rfl⟩⟩

/-- Row selection is unaffected by changing the clock. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_rows_ignore_clock"]
theorem pmatchRows_ignoreClock {C F E : Type} (rows : List (FlatLang.Pat × E))
    (state : FlatSem.State C F) (value : FlatSem.Value) (clock : Nat) :
    FlatSem.pmatchRows rows { state with clock := clock } value = FlatSem.pmatchRows rows state value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    simp only [FlatSem.pmatchRows, (pmatch_ignoreClock state clock pattern value [] [] []).1, ih]

/-- A selected row matches with the returned bindings and belongs to the input. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_rows_IMP_pmatch"]
theorem pmatchRows_imp_pmatch {C F E : Type} (rows : List (FlatLang.Pat × E))
    (state : FlatSem.State C F) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : E)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body)) :
    FlatSem.pmatch state pattern value [] = .match bindings ∧ (pattern, body) ∈ rows := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨first, expression⟩ := row
    cases head : FlatSem.pmatch state first value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at selected
    | noMatch =>
      have tail : FlatSem.pmatchRows rest state value = .match (bindings, pattern, body) := by
        simpa [FlatSem.pmatchRows, head] using selected
      obtain ⟨matched, member⟩ := ih tail
      exact ⟨matched, List.mem_cons_of_mem _ member⟩
    | «match» newBindings =>
      cases tail : FlatSem.pmatchRows rest state value <;>
        simp_all [FlatSem.pmatchRows]

end Flapjack.Compiler.Backend.FlatProps
