module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Correctness
public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section

/-! Source-shaped flat-to-closure compiler simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString Flapjack.SemanticPrimitivesHOL

namespace CompileCorrectPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end CompileCorrectPort

/-- The specialized expression relation implies the source result relation. -/
theorem evalResultRel_to_source {source target}
    (related : EvalResultRel source target) :
    SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel source target := by
  cases related with
  | value values => exact values
  | raise values => exact values
  | abort error => rfl

/-- The declaration relation supplies the source's independently polymorphic
success-list witness; HOL types are inhabited. -/
theorem decResultRel_to_source {α : Type} [Nonempty α] {source target}
    (related : DecResultRel source target) :
    ∃ values : List α, SemanticPrimitivesProps.resultRel
      (List.Forall₂ (fun (_ : α) (_ : ClosSem.Value) => True)) ValueRel
      (match source with | none => .val values | some error => .err error) target := by
  cases related with
  | success values =>
    let inhabitant : α := Classical.choice inferInstance
    refine ⟨values.map (fun _ => inhabitant), ?_⟩
    change List.Forall₂ (fun (_ : α) (_ : ClosSem.Value) => True) (values.map (fun _ => inhabitant)) values
    induction values with
    | nil => exact .nil
    | cons head tail ih => exact .cons trivial ih
  | raise values => exact ⟨[], values⟩
  | abort error => exact ⟨[], rfl⟩

/-- Both source theorem conjuncts follow from the complete Lean simulations.
The independently polymorphic success-list type is inhabited, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [refs, code])]
theorem compileCorrect_sourceShape {C F α : Type} [Nonempty α] :
    (∀ (env : FlatSem.Environment FlatSem.Value) (source : FlatSem.State C F) (expressions : List FlatLang.Exp)
      (names : List (Option MlString)) (values : List ClosSem.Value)
      (result : Result (List FlatSem.Value) FlatSem.Value) (sourceLast : FlatSem.State C F)
      (target : ClosSem.State C F),
      FlatSem.evaluate env source expressions = (sourceLast, result) ∧ StateRel source target ∧
      EnvRel env names values ∧ expressions.all FlatProps.noMat = true ∧
      result ≠ .err (.abort .typeError) →
      ∃ targetResult targetLast,
        ClosSem.evaluate (compile names expressions) values target = (targetResult, targetLast) ∧
        StateRel sourceLast targetLast ∧
        SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel result targetResult) ∧
    (∀ (source : FlatSem.State C F) (declarations : List FlatLang.Exp)
      (result : Option (ErrorResult FlatSem.Value)) (sourceLast : FlatSem.State C F) (target : ClosSem.State C F),
      FlatSem.evaluateDecs source declarations = (sourceLast, result) ∧ StateRel source target ∧
      FlatProps.noMatDecs declarations = true ∧ result ≠ some (.abort .typeError) →
      ∃ targetResult targetLast,
        ClosSem.evaluate (compileDecs declarations) [] target = (targetResult, targetLast) ∧
        StateRel sourceLast targetLast ∧
        ∃ values : List α, SemanticPrimitivesProps.resultRel
          (List.Forall₂ (fun (_ : α) (_ : ClosSem.Value) => True)) ValueRel
          (match result with | none => .val values | some error => .err error) targetResult) := by
  constructor
  · intro env source expressions names values result sourceLast target premises
    obtain ⟨run, states, environments, safe, notTypeError⟩ := premises
    have noMat : FlatProps.noMatList expressions = true := by simpa [FlatProps.noMatList_eq_all] using safe
    have noError : (FlatSem.evaluate env source expressions).2 ≠ .err (.abort .typeError) := by
      simpa [run] using notTypeError
    have simulated := evaluate_simulation env names values source target expressions states environments noMat noError
    have relation : StateRel sourceLast (ClosSem.evaluate (compile names expressions) values target).2 ∧
        EvalResultRel result (ClosSem.evaluate (compile names expressions) values target).1 := by
      simpa [EvalSim, run] using simulated
    exact ⟨_, _, Prod.eta _, relation.1, evalResultRel_to_source relation.2⟩
  · intro source declarations result sourceLast target premises
    obtain ⟨run, states, safe, notTypeError⟩ := premises
    have noError : (FlatSem.evaluateDecs source declarations).2 ≠ some (.abort .typeError) := by
      simpa [run] using notTypeError
    have simulated := evaluate_decs_simulation source target declarations states safe noError
    have relation : StateRel sourceLast (ClosSem.evaluate (compileDecs declarations) [] target).2 ∧
        DecResultRel result (ClosSem.evaluate (compileDecs declarations) [] target).1 := by
      simpa [DecSim, run] using simulated
    obtain ⟨values, resultRel⟩ := decResultRel_to_source (α := α) relation.2
    refine ⟨_, _, Prod.eta _, relation.1, values, ?_⟩
    cases result <;> exact resultRel

/-- Compilation of declarations simulates the complete source declaration evaluation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_decs_correct"
  (fmap_as_finite_support := [refs, code])]
theorem compileDecs_correct {C F α : Type} [Nonempty α] :
    ∀ (source : FlatSem.State C F) (declarations : List FlatLang.Exp)
      (result : Option (ErrorResult FlatSem.Value)) (sourceLast : FlatSem.State C F) (target : ClosSem.State C F),
      FlatSem.evaluateDecs source declarations = (sourceLast, result) ∧ StateRel source target ∧
      FlatProps.noMatDecs declarations = true ∧ result ≠ some (.abort .typeError) →
      ∃ targetResult targetLast,
        ClosSem.evaluate (compileDecs declarations) [] target = (targetResult, targetLast) ∧
        StateRel sourceLast targetLast ∧
        ∃ values : List α, SemanticPrimitivesProps.resultRel
          (List.Forall₂ (fun (_ : α) (_ : ClosSem.Value) => True)) ValueRel
          (match result with | none => .val values | some error => .err error) targetResult :=
  (compileCorrect_sourceShape (C := C) (F := F) (α := α)).2

/-- The two concrete declaration evaluations have related final states and results. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_decs_correct2"
  (fmap_as_finite_support := [refs, code])]
theorem compileDecs_correct2 {C F α : Type}
    (source : FlatSem.State C F) (declarations : List FlatLang.Exp)
    (sourceResult : FlatSem.State C F × Option (ErrorResult FlatSem.Value))
    (target : ClosSem.State C F) (targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (targetLast : ClosSem.State C F)
    (premises : FlatSem.evaluateDecs source declarations = sourceResult ∧
      ClosSem.evaluate (compileDecs declarations) [] target = (targetResult, targetLast) ∧
      StateRel source target ∧ FlatProps.noMatDecs declarations = true ∧
      sourceResult.2 ≠ some (.abort .typeError)) :
    StateRel sourceResult.1 targetLast ∧
      SemanticPrimitivesProps.resultRel (fun (_ : List α) (_ : List ClosSem.Value) => True) ValueRel
        (match sourceResult.2 with | none => .val [] | some error => .err error) targetResult := by
  obtain ⟨sourceRun, targetRun, states, safe, notTypeError⟩ := premises
  obtain ⟨sourceLast, sourceError⟩ := sourceResult
  have noError : (FlatSem.evaluateDecs source declarations).2 ≠ some (.abort .typeError) := by
    simpa [sourceRun] using notTypeError
  have simulated := evaluate_decs_simulation source target declarations states safe noError
  have relation : StateRel sourceLast targetLast ∧ DecResultRel sourceError targetResult := by
    simpa [DecSim, sourceRun, targetRun] using simulated
  refine ⟨relation.1, ?_⟩
  cases relation.2 with
  | success values => trivial
  | raise related => exact related
  | abort error => rfl

end Flapjack.Compiler.Backend.FlatToClos
