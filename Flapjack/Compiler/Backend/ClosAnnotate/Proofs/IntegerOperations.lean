module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Operations

@[expose] public section

/-! Integer primitives under the closure-annotation value relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Integer primitives observe only numeric arguments, which related values
preserve exactly. -/
theorem doIntApp_related (op : ClosLang.IntOp) (values nextValues : List Value)
    (related : List.Forall₂ ValueRel values nextValues) :
    doIntApp op values = doIntApp op nextValues := by
  cases related with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => cases first <;> cases op <;> simp [doIntApp]
    | cons second rest =>
      cases rest with
      | nil => cases first <;> cases second <;> cases op <;> simp [doIntApp]
      | cons third rest => cases op <;> simp [doIntApp]

/-- Every value returned by an integer primitive is related to itself. -/
theorem doIntApp_result_related (op : ClosLang.IntOp) (values : List Value) (value : Value)
    (run : doIntApp op values = some value) : ValueRel value value := by
  cases values with
  | nil =>
    cases op <;> simp_all [doIntApp]
    subst value
    exact .number _
  | cons first rest =>
    cases rest with
    | nil =>
      cases first <;> cases op <;> simp_all [doIntApp]
      all_goals obtain ⟨_, run⟩ := run; subst value; exact .block _ _ _ .nil
    | cons second rest =>
      cases rest with
      | nil =>
        cases first <;> cases second <;> cases op <;> simp_all [doIntApp]
        all_goals try obtain ⟨_, run⟩ := run
        all_goals try subst value
        all_goals first | exact .number _ | exact .block _ _ _ .nil
      | cons third rest => cases op <;> simp_all [doIntApp]

/-- All integer primitives preserve the candidate value and state relations,
including the same type error for invalid arguments or zero divisors. -/
theorem primitiveSimulation_int {C F : Type} (op : ClosLang.IntOp) :
    PrimitiveSimulation (C := C) (F := F) (.intOp op) := by
  intro values nextValues source target related states
  have same := doIntApp_related op values nextValues related
  cases result : doIntApp op values with
  | none =>
    have nextResult : doIntApp op nextValues = none := by rw [← same, result]
    refine ⟨.err (.abort .typeError), ?_, ?_⟩
    · simp [doApp, applyNumeric, nextResult]
    · simp [doApp, applyNumeric, result, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]
  | some value =>
    have nextResult : doIntApp op nextValues = some value := by rw [← same, result]
    refine ⟨.val (value, target), ?_, ?_⟩
    · simp [doApp, applyNumeric, nextResult]
    · simpa [doApp, applyNumeric, result, AppResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel] using
        And.intro (doIntApp_result_related op values value result) states

end Flapjack.Compiler.Backend.ClosAnnotate
