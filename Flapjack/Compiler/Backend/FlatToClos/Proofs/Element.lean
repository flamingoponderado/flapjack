import Flapjack.Compiler.Backend.FlatToClos.Proofs.MemoryExpressions
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Mathlib.Data.List.Forall2

/-! Constructor and reference reads for the proof-side pass simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Looking up a source list element in related lists finds a related target
element at the same index. -/
theorem valueList_get_related (source : List FlatSem.Value) (target : List ClosSem.Value)
    (index : Nat) (value : FlatSem.Value) (related : List.Forall₂ ValueRel source target)
    (found : source[index]? = some value) :
    ∃ targetValue, target[index]? = some targetValue ∧ ValueRel value targetValue := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp found
  have targetBound : index < target.length := by have := related.length_eq; omega
  have valuesRel := related.get bound targetBound
  change ValueRel source[index] target[index] at valuesRel
  rw [eq] at valuesRel
  exact ⟨target[index], List.getElem?_eq_some_iff.mpr ⟨targetBound, rfl⟩, valuesRel⟩

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
      obtain ⟨targetResult, targetFound, resultRel⟩ := valueList_get_related _ _ _ _ fields found
      refine ⟨targetResult, ?_, resultRel⟩
      simp [ClosSem.applyMemory, targetFound]
  | con fields =>
    rename_i sourceFields targetFields tag typeId
    cases found : sourceFields[index]? with
    | none => simp [FlatSem.doAppFlat, found] at run
    | some sourceResult =>
      simp [FlatSem.doAppFlat, found] at run
      subst result
      obtain ⟨targetResult, targetFound, resultRel⟩ := valueList_get_related _ _ _ _ fields found
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

/-- A unary element read is simulated for constructor fields and scalar
references, including operand errors. -/
theorem evaluate_element {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (index : Nat) (argument : FlatLang.Exp)
    (argSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.el index) [argument]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.el index) [argument]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [argument] argument []).1
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, arg1, List.reverse_singleton] at argSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluate_element_args]
  simp only [List.reverse_singleton, flatFix] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim notTypeError ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            cases run : FlatSem.doAppFlat next (.el index) [sourceValue] with
            | none => simp [FlatSem.doAppFlat] at run
            | some output =>
              cases output with
              | none => simp [FlatSem.applyResult, FlatSem.doApp, run] at notTypeError
              | some pair =>
                obtain ⟨after, result⟩ := pair
                cases result with
                | err error =>
                  cases sourceValue <;> simp [FlatSem.doAppFlat] at run
                  case loc flag pointer =>
                    split at run <;> simp_all
                | val result =>
                  have afterEq : after = next := by
                    cases sourceValue <;> simp [FlatSem.doAppFlat] at run
                    case conv stamp fields =>
                      cases h : fields[index]? <;> simp_all
                    case loc flag pointer =>
                      split at run <;> simp_all
                  subst after
                  obtain ⟨targetResult, targetRun, valueRel⟩ := element_related next nextTarget index sourceValue targetValue result states head run
                  simp only [Int.ofNat_eq_natCast] at targetRun
                  simp [FlatSem.applyResult, FlatSem.doApp, run, ClosSem.doApp, targetRun,
                    states, EvalResultRel.value (.cons valueRel .nil)]

end Flapjack.Compiler.Backend.FlatToClos
