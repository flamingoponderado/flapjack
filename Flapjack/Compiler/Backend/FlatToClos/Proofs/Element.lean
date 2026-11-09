import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Mathlib.Data.List.Forall2
import Flapjack.Misc.ListLookupRel

/-! Constructor and reference reads for the proof-side pass simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A successful flat field/reference read returns a related closure value
at the same index, without changing the states. -/
theorem element_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (index : Nat) (value : FlatSem.Value) (targetValue : ClosSem.Value) (result : FlatSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue)
    (run : FlatSem.doAppFlat source (.el index) [value] = some (some (source, .val result))) :
    ∃ targetResult, ClosSem.applyMemory .el [targetValue, .number (Int.ofNat index)] target =
      some (targetResult, target) ∧ ValueRel result targetResult := by
  cases related with
  | tuple fields =>
    rename_i sourceFields targetFields
    cases found : sourceFields[index]? with
    | none => simp [FlatSem.doAppFlat, found] at run
    | some sourceResult =>
      simp [FlatSem.doAppFlat, found] at run
      subst result
      obtain ⟨targetResult, targetFound, resultRel⟩ := forall₂_lookup fields _ _ found
      refine ⟨targetResult, ?_, resultRel⟩
      simp [ClosSem.applyMemory, targetFound]
  | con fields =>
    rename_i sourceFields targetFields tag typeId
    cases found : sourceFields[index]? with
    | none => simp [FlatSem.doAppFlat, found] at run
    | some sourceResult =>
      simp [FlatSem.doAppFlat, found] at run
      subst result
      obtain ⟨targetResult, targetFound, resultRel⟩ := forall₂_lookup fields _ _ found
      refine ⟨targetResult, ?_, resultRel⟩
      simp [ClosSem.applyMemory, targetFound]
  | loc flag pointer =>
    by_cases zero : index = 0
    · subst index
      cases found : storeLookup pointer source.refs with
      | none => simp [FlatSem.doAppFlat, found] at run
      | some entry =>
        cases entry with
        | w8array | varray | thunk => simp [FlatSem.doAppFlat, found] at run
        | refv sourceResult =>
          simp [FlatSem.doAppFlat, found] at run
          subst result
          obtain ⟨targetResult, targetFound, resultRel⟩ := lookup_ref states found
          exact ⟨targetResult, by simp [ClosSem.applyMemory, targetFound], resultRel⟩
    · simp [FlatSem.doAppFlat, zero] at run
  | int | char | string | word8 | word64 | float64 | vector | closure | recclosure =>
    simp [FlatSem.doAppFlat] at run

/-- The inserted element index evaluates before the operand without changing
the state. -/
theorem evaluate_element_args {C F : Type} (index : Nat) (operand : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op .none (.intOp (.const (Int.ofNat index))) [], operand] env state =
      match ClosSem.evaluate [operand] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => (.val (.number (Int.ofNat index) :: values), next) := by
  have constant : ClosSem.evaluate [.op .none (.intOp (.const (Int.ofNat index))) []] env state =
      (.val [.number (Int.ofNat index)], state) := by
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
  exact ClosProps.evaluate_cons_value _ _ _ _ _ _ constant

end Flapjack.Compiler.Backend.FlatToClos
