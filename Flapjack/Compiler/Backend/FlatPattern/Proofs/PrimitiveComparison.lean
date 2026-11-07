import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveNumeric

/-! Comparison primitives for the proof-side flat pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- Primitive-typed related values are identical: literals are preserved, and
the only typed constructor values are empty Boolean constructors. -/
theorem checkType_related_eq (typ : PrimType) (value value' : FlatSem.Value)
    (related : ValueRel value value') (valid : FlatSem.checkType typ value = true) : value' = value := by
  cases value with
  | litv lit => exact (valueRel_lit lit value').1 related
  | conv stamp fields =>
    obtain ⟨fields', eq, contents⟩ := (valueRel_conv stamp fields value').1 related
    cases fields with
    | nil => cases contents; exact eq
    | cons _ _ => cases typ <;> simp [FlatSem.checkType] at valid
  | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
    cases typ <;> simp [FlatSem.checkType] at valid

/-- A successful primitive comparison has operands of the selected primitive type. -/
theorem doTest_success_types (test : Test) (typ : PrimType) (first second : FlatSem.Value) (result : Bool)
    (run : FlatSem.doTest test typ first second = .val result) :
    FlatSem.checkType typ first = true ∧ FlatSem.checkType typ second = true := by
  cases test with
  | equal =>
    by_cases check : FlatSem.checkType typ first && FlatSem.checkType typ second
    · simpa using check
    · simp [FlatSem.doTest, check] at run
  | compare ordering =>
    cases typ <;> cases first <;> cases second <;> simp [FlatSem.doTest, FlatSem.checkType] at run ⊢
    all_goals repeat' (split at run) <;> simp_all
  | altCompare ordering =>
    cases typ <;> cases first <;> cases second <;> simp [FlatSem.doTest, FlatSem.checkType] at run ⊢
    all_goals repeat' (split at run) <;> simp_all

/-- A successful type-specific comparison returns the same Boolean for related
operands. -/
theorem doTest_related (test : Test) (typ : PrimType) (first first' second second' : FlatSem.Value) (result : Bool)
    (firstRel : ValueRel first first') (secondRel : ValueRel second second')
    (run : FlatSem.doTest test typ first second = .val result) :
    FlatSem.doTest test typ first' second' = .val result := by
  obtain ⟨firstType, secondType⟩ := doTest_success_types test typ first second result run
  have firstEq := checkType_related_eq typ first first' firstRel firstType
  have secondEq := checkType_related_eq typ second second' secondRel secondType
  simpa [firstEq, secondEq] using run

/-- Type-specific equality and ordering tests preserve primitive application. -/
theorem doApp_test_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (test : Test) (typ : PrimType) (values values' : List FlatSem.Value)
    (result : SemanticPrimitivesHOL.Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.test test typ)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.test test typ)) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
      | nil =>
        cases tested : FlatSem.doTest test typ first second with
        | typeError => simp [FlatSem.doApp, FlatSem.doAppNumeric, tested] at run
        | val boolean =>
          have tested' := doTest_related test typ first first' second second' boolean firstRel secondRel tested
          simp [FlatSem.doApp, FlatSem.doAppNumeric, tested] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (FlatSem.boolValue boolean), by simp [FlatSem.doApp, FlatSem.doAppNumeric, tested'],
            states, .value (boolValue_related boolean)⟩

end Flapjack.Compiler.Backend.FlatPattern
