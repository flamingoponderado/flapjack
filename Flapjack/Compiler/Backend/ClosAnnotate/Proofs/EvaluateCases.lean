module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.SemanticPrimitivesProps.ResultRelation

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Initial cases of closure-annotation evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The generic result relation instantiated for closure values. -/
abbrev ResultRel : Result (List Value) Value → Result (List Value) Value → Prop :=
  Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel

/-- All source code bodies lack pre-existing capture annotations. -/
def CodeSafe {C F : Type} (state : State C F) : Prop :=
  ∀ key arity body, state.code.lookup key = some (arity, body) → everyFnVarsNone [body]

/-- All future oracle programs lack pre-existing capture annotations. -/
def OracleSafe {C F : Type} (state : State C F) : Prop :=
  ∀ index, everyFnVarsNone (state.compileOracle index).2.1 ∧
    everyFnVarsNone ((state.compileOracle index).2.2.map (fun (_, _, body) => body))

/-- Simulation obligation for shifting an expression list. -/
def EvalSimulation {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (source : State C F) (nextEnv : List Value) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State C F) (m l : Nat) (index : Spt Nat),
    evaluate expressions env source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → env.length = m + l →
    (∀ n, altFv n expressions = true → EnvOk m l index env nextEnv n) →
    everyFnVarsNone expressions → CodeSafe source → OracleSafe source → StateRel source target →
    ∃ targetResult targetNext,
      evaluate (shiftList (altFree expressions).1 m l index) nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext

/-- Preservation obligation for code and oracle safety across evaluation. -/
def PreservesCodeOracle {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (source : State C F) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → CodeSafe source → OracleSafe source →
    CodeSafe next ∧ OracleSafe next

/-- Code and oracle safety preservation from one source state. -/
def PreservesCodeOracleAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → CodeSafe source → OracleSafe source →
    CodeSafe next ∧ OracleSafe next

/-- Restrict an unrestricted safety proof to one state. -/
theorem preservesCodeOracle_at {C F : Type} {expressions : List ClosLang.Exp}
    (safe : PreservesCodeOracle (C := C) (F := F) expressions) (source : State C F) :
    PreservesCodeOracleAt source expressions := by
  intro env result next run code oracle
  exact safe env source result next run code oracle

/-- Empty expression lists preserve evaluation and state. -/
theorem evaluate_nil {C F : Type} : EvalSimulation (C := C) (F := F) [] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [], target, by simp [altFree_nil, shiftList, evaluate], .nil, states⟩

/-- Variable evaluation is preserved by the compact environment mapping. -/
theorem evaluate_var {C F : Type} (trace : BackendCommon.Tra) (variableIndex : Nat) :
    EvalSimulation (C := C) (F := F) [.var trace variableIndex] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  cases found : env[variableIndex]? with
  | none =>
    simp [evaluate, found] at run
    exact False.elim (noType run.1.symm)
  | some value =>
    have sourceInfo := List.getElem?_eq_some_iff.mp found
    have tracked : variableIndex < l + m := by
      have bound := sourceInfo.1
      omega
    have rel := envOk_getVar m l index env nextEnv variableIndex
      (vars variableIndex (by simp [altFv_var])) tracked
    let _ : Nonempty Value := ⟨unitValue⟩
    let targetValue := Flapjack.holEl (getVar m l index variableIndex) nextEnv
    have sourceValue : Flapjack.holEl variableIndex env = value := by
      rw [Flapjack.holEl_eq_getElem _ _ sourceInfo.1]
      exact sourceInfo.2
    have targetLookup : nextEnv[getVar m l index variableIndex]? = some targetValue := by
      simp [targetValue, Flapjack.holEl_eq_getElem _ _ rel.2.1, rel.2.1]
    have valueRel : ValueRel value targetValue := by
      simpa [sourceValue, targetValue] using rel.2.2
    simp [evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.val [targetValue], target, ?_, .cons valueRel .nil, states⟩
    simp [altFree_var, shiftList, shiftSing, evaluate, targetLookup]

end Flapjack.Compiler.Backend.ClosAnnotate
