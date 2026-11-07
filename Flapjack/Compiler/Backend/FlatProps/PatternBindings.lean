import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Binding order for the flat pattern matcher. The carrier and evaluator
correspondence remains under review, so these results are untagged. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend

/-- Successful flat matching prepends exactly the pattern's binding names;
the list case covers the recursive matcher used for constructor arguments. -/
theorem pmatchBindings {C F : Type} (state : FlatSem.State C F) :
    (∀ pattern value bindings result,
      FlatSem.pmatch state pattern value bindings = .match result →
        result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst) ∧
    (∀ patterns values bindings result,
      FlatSem.pmatchList state patterns values bindings = .match result →
        result.map Prod.fst = FlatLang.patsBindings patterns ++ bindings.map Prod.fst) := by
  have all : ∀ pattern : FlatLang.Pat,
      ∀ value bindings result, FlatSem.pmatch state pattern value bindings = .match result →
        result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst := by
    apply FlatLang.Pat.rec
      (motive_1 := fun pattern => ∀ value bindings result,
        FlatSem.pmatch state pattern value bindings = .match result →
          result.map Prod.fst = FlatLang.patBindings pattern ++ bindings.map Prod.fst)
      (motive_2 := fun patterns => ∀ values bindings result,
        FlatSem.pmatchList state patterns values bindings = .match result →
          result.map Prod.fst = FlatLang.patsBindings patterns ++ bindings.map Prod.fst)
    case pany =>
      intro value bindings result run
      simp [FlatSem.pmatch] at run
      subst result
      simp [FlatLang.patBindings]
    case pvar =>
      intro name value bindings result run
      simp [FlatSem.pmatch] at run
      subst result
      simp [FlatLang.patBindings]
    case plit =>
      intro lit value bindings result run
      cases value <;> simp_all [FlatSem.pmatch, FlatLang.patBindings] <;>
        split at run <;> (try simp_all) <;> (try split at run) <;> simp_all
    case pcon =>
      intro stamp patterns ih value bindings result run
      cases value <;> simp_all [FlatSem.pmatch, FlatLang.patBindings]
      case conv actual values =>
        split at run <;> (try simp_all)
        split at run <;> (try simp_all)
        exact ih values bindings result run
    case pref =>
      intro pattern ih value bindings result run
      cases value <;> simp_all [FlatSem.pmatch, FlatLang.patBindings]
      case loc flag index =>
        cases entry : storeLookup index state.refs <;> simp_all
        rename_i cell
        cases cell <;> simp_all
        exact ih _ bindings result run
    case pas =>
      intro pattern name ih value bindings result run
      have h := ih value ((name, value) :: bindings) result (by simpa [FlatSem.pmatch] using run)
      simpa [FlatLang.patBindings, List.append_assoc] using h
    case nil =>
      intro values bindings result run
      cases values <;> simp_all [FlatSem.pmatchList, FlatLang.patsBindings]
    case cons =>
      intro pattern patterns ihHead ihTail values bindings result run
      cases values with
      | nil => simp [FlatSem.pmatchList] at run
      | cons value values =>
        simp only [FlatSem.pmatchList] at run
        cases headRun : FlatSem.pmatch state pattern value bindings with
        | typeError => simp [headRun] at run
        | noMatch =>
          cases tailRun : FlatSem.pmatchList state patterns values bindings <;> simp_all
        | «match» next =>
          simp only [headRun] at run
          have first := ihHead value bindings next headRun
          have second := ihTail values next result run
          simp only [FlatLang.patsBindings]
          rw [second, first, List.append_assoc]
  refine ⟨all, ?_⟩
  intro patterns
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
      cases headRun : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [headRun] at run
      | noMatch =>
        cases tailRun : FlatSem.pmatchList state patterns values bindings <;> simp_all
      | «match» next =>
        simp only [headRun] at run
        have first := all pattern value bindings next headRun
        have second := ih values next result run
        simp only [FlatLang.patsBindings]
        rw [second, first, List.append_assoc]

/-- Successful matching produces one binding for each pattern name, in
addition to the input bindings. -/
theorem pmatchLength {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (value : FlatSem.Value) (bindings result : List (VarN × FlatSem.Value))
    (run : FlatSem.pmatch state pattern value bindings = .match result) :
    result.length = (FlatLang.patBindings pattern).length + bindings.length := by
  have names := (pmatchBindings state).1 pattern value bindings result run
  have lengths := congrArg List.length names
  simpa using lengths

end Flapjack.Compiler.Backend.FlatProps
