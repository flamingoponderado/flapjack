import Flapjack.Compiler.Backend.FlatPattern.Proofs.CompiledMatch
import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchRows

/-! Selected-row simulation for flat pattern compilation. The evaluator and
proof-side state/value relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A selected row's pattern matches with exactly the returned bindings. -/
theorem pmatchRows_selected_match {C F E : Type} (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × E)) (bindings : List (VarN × FlatSem.Value))
    (pattern : FlatLang.Pat) (body : E)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body)) :
    FlatSem.pmatch state pattern value [] = .match bindings := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at selected
  | cons row rows ih =>
    obtain ⟨first, expression⟩ := row
    cases head : FlatSem.pmatch state first value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at selected
    | noMatch =>
      have tail : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body) := by
        simpa [FlatSem.pmatchRows, head] using selected
      exact ih tail
    | «match» newBindings =>
      cases tail : FlatSem.pmatchRows rows state value <;>
        simp_all [FlatSem.pmatchRows]

/-- If a source row matches, compiled pattern dispatch evaluates its compiled
body under an environment related to the source's bound-variable environment.
This is a proof-side composition, not yet a reviewed HOL theorem port. -/
theorem evaluate_compiled_match_branch {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (n m : Nat) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (source target final : FlatSem.State C F) (value value' : FlatSem.Value)
    (sourceEnv targetEnv dispatchEnv : FlatSem.Environment FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body default : FlatLang.Exp)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (envs : EnvRel m sourceEnv targetEnv) (nameBound : n ≤ m)
    (rowBound : (compileMatch cfg rows).1 < n - 1)
    (dispatchEq : dispatchEnv.v = (encNumToName n, value') :: targetEnv.v)
    (sourceMatch : FlatSem.pmatchRows rows source value = .match (bindings, pattern, body))
    (evaluated : FlatSem.evaluate dispatchEnv target
      [compilePats cfg (compileMatch cfg rows).2.1 trace n
        (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] = (final, result)) :
    ∃ extEnv, FlatSem.evaluate extEnv target [(compileExp cfg body).2.2] = (final, result) ∧
      EnvRel (n - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv := by
  obtain ⟨index, targetBindings, bodyBound, flag, compiledBody, sourceAt, compiled, targetAt,
    bodyLe, patternLe, bindingRel, targetMatch⟩ :=
      compileMatch_pmatchRows_index_bound cfg stateCfg m source target value value' states values rows
        bindings pattern body sourceMatch
  have found : dispatchEnv.v.lookup (encNumToName n) = some value' := by simp [dispatchEq]
  have pure : FlatSem.evaluate dispatchEnv target [.varLocal trace (encNumToName n)] =
      (target, .val [value']) := by simp [FlatSem.evaluate, found]
  have targetSafe : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' ≠ .typeError := by
    rw [targetMatch]; simp
  have dispatch := evaluate_compilePats cfg (compileMatch cfg rows).2.1 trace n
    (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2
    dispatchEnv target value' pure targetSafe
  have branchEval : FlatSem.evaluate dispatchEnv target
      [compilePatRhs trace n (.varLocal trace (encNumToName n)) (pattern, compiledBody)] = (final, result) := by
    rw [targetMatch] at dispatch
    exact dispatch.symm.trans evaluated
  have patternMatch := pmatchRows_selected_match target value' (compileMatch cfg rows).2.2
    targetBindings pattern compiledBody targetMatch
  have patternBound : maxDecName (FlatLang.patBindings pattern) < n - 1 := by omega
  obtain ⟨extEnv, extEval, extRelated⟩ := evaluate_compilePatRhs trace n m pattern compiledBody
    target final dispatchEnv sourceEnv targetEnv value' bindings targetBindings result branchEval patternMatch
    envs bindingRel dispatchEq nameBound patternBound
  exact ⟨extEnv, by simpa [compiled] using extEval, extRelated⟩

/-- When the source rows do not match, compiled dispatch evaluates the
provided default expression in the target environment. -/
theorem evaluate_compiled_match_default {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (n m : Nat) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (source target : FlatSem.State C F) (value value' : FlatSem.Value)
    (targetEnv dispatchEnv : FlatSem.Environment FlatSem.Value) (default : FlatLang.Exp)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (dispatchEq : dispatchEnv.v = (encNumToName n, value') :: targetEnv.v)
    (sourceMatch : FlatSem.pmatchRows rows source value = .noMatch) :
    FlatSem.evaluate dispatchEnv target
      [compilePats cfg (compileMatch cfg rows).2.1 trace n
        (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2] =
      FlatSem.evaluate dispatchEnv target [default] := by
  have related := compileMatch_pmatchRows_related cfg stateCfg m source target value value' states values rows
  have targetMatch : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' = .noMatch := by
    simpa [sourceMatch] using related
  have found : dispatchEnv.v.lookup (encNumToName n) = some value' := by simp [dispatchEq]
  have pure : FlatSem.evaluate dispatchEnv target [.varLocal trace (encNumToName n)] =
      (target, .val [value']) := by simp [FlatSem.evaluate, found]
  have targetSafe : FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' ≠ .typeError := by
    rw [targetMatch]; simp
  have dispatch := evaluate_compilePats cfg (compileMatch cfg rows).2.1 trace n
    (.varLocal trace (encNumToName n)) default (compileMatch cfg rows).2.2
    dispatchEnv target value' pure targetSafe
  simpa [targetMatch] using dispatch

end Flapjack.Compiler.Backend.FlatPattern
