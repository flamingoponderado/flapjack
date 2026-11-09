module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.BindingRecursive
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.ValueRelation

@[expose] public section

/-! Evaluation of a compiled pattern branch. The clocked evaluator and
proof-side value relation are not yet reviewed as HOL ports. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Every name in a list is bounded by the maximum decoded name. -/
theorem decName_le_maxDecName (names : List VarN) (name : VarN) (member : name ∈ names) :
    decNameToNum name ≤ maxDecName names := by
  induction names with
  | nil => simp at member
  | cons first names ih =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      simp only [maxDecName]
      omega
    · have h := ih later
      simp only [maxDecName]
      omega

/-- A singleton generated variable supplies the binding simulation's input
premise whenever the environment contains the generated name. -/
theorem bindingInputs_single_generated {C F : Type} (trace : BackendCommon.Tra) (n : Nat)
    (used : NumSet) (pattern : FlatLang.Pat) (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value : FlatSem.Value) (tail : List (VarN × FlatSem.Value))
    (envEq : env.v = (encNumToName n, value) :: tail) (positive : 0 < n) :
    BindingInputs (n - 1) (n + 1) used env state
      [(pattern, n, .varLocal trace (encNumToName n))] [value] := by
  apply List.Forall₂.cons
  · intro env2 _ related
    have interval : n - 1 < decNameToNum (encNumToName n) ∧ decNameToNum (encNumToName n) < n + 1 := by
      simp only [decEnc]
      omega
    have eq := aLookupRel_eq_lookup _ _ _ (encNumToName n) ⟨related, interval⟩
    have found : env2.v.lookup (encNumToName n) = some value := by
      rw [← holALookup_eq_lookup, eq, envEq]
      simp [holALookup]
    simp [pureEvalTo, FlatSem.evaluate, found]
  · exact .nil

/-- Evaluate a compiled branch and recover an environment for its original
body. HOL's type-changing update of the single-field environment is rendered
by rebuilding it from `f env3.v`, retaining the independent input carrier. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "evaluate_compile_pat_rhs"]
theorem evaluate_compilePatRhs {C F A : Type} (env3 : FlatSem.Environment A)
    (f : List (VarN × A) → List (VarN × FlatSem.Value)) (state : FlatSem.State C F)
    (trace : BackendCommon.Tra) (n : Nat) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (final : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value)) (m : Nat)
    (env1 env2 : FlatSem.Environment FlatSem.Value) (sourceBindings : List (VarN × FlatSem.Value))
    (premises : FlatSem.evaluate ⟨f env3.v⟩ state
      [compilePatRhs trace n (.varLocal trace (encNumToName n)) (pattern, body)] = (final, result) ∧
    FlatSem.pmatch state pattern value [] = .match bindings ∧ EnvRel m env1 env2 ∧
    aLookupRel (fun name => decNameToNum name < m) ValueRel sourceBindings bindings ∧
    f env3.v = (encNumToName n, value) :: env2.v ∧ n ≤ m ∧
    maxDecName (FlatLang.patBindings pattern) < n - 1) :
    ∃ extEnv, FlatSem.evaluate extEnv state [body] = (final, result) ∧
      EnvRel (n - 1) { env1 with v := sourceBindings ++ env1.v } extEnv := by
  obtain ⟨evaluated, matched, envRel, bindingRel, envEq, bound, patBound⟩ := premises
  let env : FlatSem.Environment FlatSem.Value := ⟨f env3.v⟩
  change FlatSem.evaluate env state
    [compilePatRhs trace n (.varLocal trace (encNumToName n)) (pattern, body)] = (final, result) at evaluated
  change env.v = (encNumToName n, value) :: env2.v at envEq
  have positive : 0 < n := by omega
  let todo := [(pattern, n, FlatLang.Exp.varLocal trace (encNumToName n))]
  let compiled := compilePatBindings trace (n + 1) todo body
  have listMatch : FlatSem.pmatchList state (todo.map Prod.fst) [value] [] = .match bindings := by
    simp [todo, FlatSem.pmatchList, matched]
  have evalCompiled : FlatSem.evaluate env state [compiled.2] = (final, result) := by
    simpa [compilePatRhs, todo, compiled] using evaluated
  have inputs := bindingInputs_single_generated trace n compiled.1 pattern env state value env2.v envEq positive
  have initialRel : aLookupRel (fun name => decNameToNum name < n - 1) Eq env.v ([] ++ env2.v) := by
    rw [envEq]
    apply ((aLookupRel_cons_false (fun name => decNameToNum name < n - 1) (encNumToName n) Eq value
      env2.v env2.v).1 ?_).2
    · exact aLookupRel_refl _ _ _ (by intros; rfl)
    · simp only [decEnc]
      omega
  have itemBounds : ∀ item ∈ todo, (∀ name ∈ FlatLang.patBindings item.1, decNameToNum name < n - 1) ∧
      n - 1 < item.2.1 ∧ item.2.1 < n + 1 := by
    intro item member
    simp [todo] at member
    subst item
    constructor
    · intro name inPattern
      have h := decName_le_maxDecName (FlatLang.patBindings pattern) name inPattern
      omega
    · simp only
      omega
  have sim := bindingSimulation_all trace (n + 1) todo body (n - 1) state [value] [] bindings env final result env2.v
    listMatch evalCompiled inputs (by simp) (by omega) initialRel itemBounds
  obtain ⟨extEnv, extEval, extRelated⟩ := sim
  refine ⟨extEnv, extEval, (envRel_iff_lookup _ _ _).2 ?_⟩
  have combined := aLookupRel_append (fun name => decNameToNum name < m) ValueRel
    sourceBindings bindings env1.v env2.v ⟨bindingRel, (envRel_iff_lookup m env1 env2).1 envRel⟩
  intro name nameBound
  have h := combined name (by omega)
  have eq := aLookupRel_eq_lookup _ _ _ name ⟨extRelated, nameBound⟩
  simpa only [eq] using h

end Flapjack.Compiler.Backend.FlatPattern
