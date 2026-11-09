module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Operations

@[expose] public section

/-! Word primitives under the closure-annotation value relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Word primitives observe related number and word arguments identically. -/
theorem doWordApp_related (op : ClosLang.WordOp) (values nextValues : List Value)
    (related : List.Forall₂ ValueRel values nextValues) :
    doWordApp op values = doWordApp op nextValues := by
  cases related with
  | nil => cases op <;> rfl
  | cons first rest =>
    cases rest with
    | nil => cases first <;> cases op <;> simp [doWordApp, doWordAppIntegral]
    | cons second rest =>
      cases rest with
      | nil => cases first <;> cases second <;> cases op <;> simp [doWordApp, doWordAppIntegral]
      | cons third rest =>
        cases rest with
        | nil =>
          cases first <;> cases op <;> simp [doWordApp, doWordAppIntegral]
          all_goals cases second <;> cases third <;> rfl
        | cons fourth rest => cases op <;> simp [doWordApp, doWordAppIntegral]

/-- A successful word primitive returns a self-related scalar or Boolean. -/
theorem doWordApp_result_related (op : ClosLang.WordOp) (values : List Value) (value : Value)
    (run : doWordApp op values = some value) : ValueRel value value := by
  cases values with
  | nil => cases op <;> simp_all [doWordApp, doWordAppIntegral]
  | cons first rest =>
    cases rest with
    | nil =>
      cases first <;> cases op <;> simp_all [doWordApp, doWordAppIntegral]
      all_goals repeat (split at run)
      all_goals try simp_all
      all_goals try (rw [Option.bind_eq_some_iff] at run; obtain ⟨_, _, run⟩ := run; simp_all)
      all_goals try subst value
      all_goals first | exact .number _ | exact .word64 _
    | cons second rest =>
      cases rest with
      | nil =>
        cases first <;> cases second <;> cases op <;> simp_all [doWordApp, doWordAppIntegral]
        all_goals repeat (split at run)
        all_goals try simp_all
        all_goals try (rw [Option.bind_eq_some_iff] at run; obtain ⟨_, _, run⟩ := run)
        all_goals try (rw [Option.bind_eq_some_iff] at run; obtain ⟨_, _, run⟩ := run)
        all_goals try (obtain ⟨_, run⟩ := run; split at run <;> simp_all)
        all_goals try simp_all
        all_goals try subst value
        all_goals first | exact .number _ | exact .word64 _ | exact .block _ _ _ .nil
      | cons third rest =>
        cases rest with
        | nil =>
          cases first <;> cases op <;> simp_all [doWordApp, doWordAppIntegral]
          all_goals repeat (split at run)
          all_goals try simp_all
          all_goals try subst value
          all_goals exact .word64 _
        | cons fourth rest => cases op <;> simp_all [doWordApp, doWordAppIntegral]

/-- Word primitives preserve the candidate value and state relations. The
floating-point cases use the existing proof-side floating-point model. -/
theorem primitiveSimulation_word {C F : Type} (op : ClosLang.WordOp) :
    PrimitiveSimulation (C := C) (F := F) (.wordOp op) := by
  intro values nextValues source target related states
  have same := doWordApp_related op values nextValues related
  cases result : doWordApp op values with
  | none =>
    have nextResult : doWordApp op nextValues = none := by rw [← same, result]
    refine ⟨.err (.abort .typeError), ?_, ?_⟩
    · simp [doApp, applyNumeric, nextResult]
    · simp [doApp, applyNumeric, result, AppResultRel, ResultRel]
  | some value =>
    have nextResult : doWordApp op nextValues = some value := by rw [← same, result]
    refine ⟨.val (value, target), ?_, ?_⟩
    · simp [doApp, applyNumeric, nextResult]
    · simpa [doApp, applyNumeric, result, AppResultRel] using
        And.intro (doWordApp_result_related op values value result) states

end Flapjack.Compiler.Backend.ClosAnnotate
