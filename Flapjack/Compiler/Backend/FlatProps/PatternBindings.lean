import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
import Flapjack.HolRef

/-! Binding order for the flat pattern matcher. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend

/-- Successful flat matching prepends exactly the pattern's binding names;
the list case covers the recursive matcher used for constructor arguments. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_bindings"]
theorem pmatchBindings {C F : Type} :
    (∀ (state : FlatSem.State C F) pattern value bindings result,
      FlatSem.pmatch state pattern value bindings = .match result →
        result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst) ∧
    (∀ (state : FlatSem.State C F) patterns values bindings result,
      FlatSem.pmatchList state patterns values bindings = .match result →
        result.map Prod.fst = FlatLang.patsBindings patterns ++ bindings.map Prod.fst) := by
  have pat : ∀ (state : FlatSem.State C F) (pattern : FlatLang.Pat) (value : FlatSem.Value)
      (bindings : List (VarN × FlatSem.Value)) (result : List (VarN × FlatSem.Value)),
      FlatSem.pmatch state pattern value bindings = .match result →
        result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst := by
    intro state pattern
    apply FlatSem.pmatch.induct state
      (motive1 := fun pattern value bindings => ∀ result,
        FlatSem.pmatch state pattern value bindings = .match result →
          result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst)
      (motive2 := fun patterns values bindings => ∀ result,
        FlatSem.pmatchList state patterns values bindings = .match result →
          result.map Prod.fst = FlatLang.patsBindings patterns ++ bindings.map Prod.fst)
    all_goals
      intros
      simp_all [FlatSem.pmatch, FlatSem.pmatchList, FlatLang.patBindings, FlatLang.patsBindings]
      try grind
  constructor
  · exact pat
  · intro state patterns
    induction patterns with
    | nil =>
      intro values bindings result run
      cases values <;> simp_all [FlatSem.pmatchList, FlatLang.patsBindings]
    | cons pattern patterns ih =>
      intro values bindings result run
      cases values with
      | nil => simp [FlatSem.pmatchList] at run
      | cons value values =>
        simp only [FlatSem.pmatchList] at run
        split at run
        · simp_all
        · rename_i next headRun
          simp only [FlatLang.patsBindings]
          rw [ih values next result run, pat state pattern value bindings next headRun,
            List.append_assoc]
        · cases tailRun : FlatSem.pmatchList state patterns values bindings <;> simp_all

/-- Successful matching adds one binding for each pattern name. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_length"]
theorem pmatchLength {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (value : FlatSem.Value) (bindings result : List (VarN × FlatSem.Value))
    (run : FlatSem.pmatch state pattern value bindings = .match result) :
    result.length = (FlatLang.patBindings pattern).length + bindings.length := by
  have names := pmatchBindings.1 state pattern value bindings result run
  have lengths := congrArg List.length names
  simpa using lengths

end Flapjack.Compiler.Backend.FlatProps
