import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording
import Flapjack.SemanticPrimitivesProps.StoreRelation
import Flapjack.Misc.ListEl

/-! State relation for the source evaluator's recording simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Relate a declaration-backed Eval state to its recording-oracle state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "s_rel_def"]
noncomputable def stateRel {Config F : Type} (ci : CompilerInstance Config)
    (source target : State F) : Prop :=
  ∃ decState oracleState refs,
    target = { source with refs := refs, evalState := some (.evalOracle oracleState) } ∧
    List.Forall₂ (storeValueRel (ValueRel oracleState)) source.refs refs ∧
    source.evalState = some (.evalDecs decState) ∧
    oracleState.customDoEval = doEvalRecord ci ∧
    decState.compilerState = (oracleState.oracle 0).2.1 ∧
    decState.decodeDecs = vFunAbs ci.decsDom ci.decsV ∧
    decState.compiler = mkCompilerFunFromCi ci ∧
    (0 = (oracleState.oracle 0).1.1 → decState.compilerState = ci.configV ci.initState) ∧
    (0 < (oracleState.oracle 0).1.1 → (oracleState.oracle 1).2.1 = ci.configV ci.initState) ∧
    decState.envIdCounter = (oracleState.generation,
      (@Flapjack.holEl (List (SemEnv Value)) ⟨[]⟩ oracleState.generation oracleState.envs).length,
      oracleState.envs.length) ∧
    oracleState.generation < oracleState.envs.length ∧
    recordedOracleWellFormed (mkCompilerFunFromCi ci) oracleState.oracle

/-- Preserve the stored environment identifiers while extending the store. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "es_forward_def"]
def envStoreForward (before after : EvalOracleState) : Prop :=
  before.envs.length ≤ after.envs.length ∧
    ∀ id env, lookupEnv before id = some env → lookupEnv after id = some env

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "es_forward_refl"]
theorem envStoreForward_refl (state : EvalOracleState) : envStoreForward state state :=
  ⟨Nat.le_refl _, fun _ _ lookup => lookup⟩

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "es_forward_trans"]
theorem envStoreForward_trans (first second third : EvalOracleState)
    (premises : envStoreForward first second ∧ envStoreForward second third) :
    envStoreForward first third := by
  obtain ⟨⟨length₁, lookup₁⟩, ⟨length₂, lookup₂⟩⟩ := premises
  exact ⟨Nat.le_trans length₁ length₂, fun id env found => lookup₂ id env (lookup₁ id env found)⟩

/-- Extending the environment store preserves the recorded value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_forward"]
theorem valueRel_forward (before after : EvalOracleState) :
    ∀ x y, ValueRel before x y → envStoreForward before after → ValueRel after x y := by
  intro x y related forward
  apply valueRel_hol_induction before (ValueRel after) ?_ x y related
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env id encoded env' h
    obtain ⟨decoded, lookup, environments⟩ := h
    exact .env decoded (forward.2 id env' lookup) ((valueEnvRel_iff _ _ _).mpr environments)
  · intro xs ys values
    exact .vector values
  · intro stamp xs ys values
    exact .con values
  · intro env env' name body environments
    exact .closure ((valueEnvRel_iff _ _ _).mpr environments)
  · intro env env' funs name environments
    exact .recclosure ((valueEnvRel_iff _ _ _).mpr environments)
  · exact ValueRel.lit
  · exact ValueRel.loc

/-- Forward environment stores preserve values, value lists, environments and
stores under their respective relations. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "forward_rules"]
theorem forwardRules (before : EvalOracleState) (x y : Value) (after : EvalOracleState)
    (xs ys : List Value) (env env' : SemEnv Value) :
    (ValueRel before x y ∧ envStoreForward before after → ValueRel after x y) ∧
    (List.Forall₂ (ValueRel before) xs ys ∧ envStoreForward before after →
      List.Forall₂ (ValueRel after) xs ys) ∧
    (envRel (ValueRel before) env env' ∧ envStoreForward before after →
      envRel (ValueRel after) env env') ∧
    (∀ storeXs storeYs, List.Forall₂ (storeValueRel (ValueRel before)) storeXs storeYs ∧
      envStoreForward before after → List.Forall₂ (storeValueRel (ValueRel after)) storeXs storeYs) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨related, forward⟩
    exact valueRel_forward before after x y related forward
  · rintro ⟨related, forward⟩
    induction related with
    | nil => exact .nil
    | cons head _ ih => exact .cons (valueRel_forward before after _ _ head forward) ih
  · rintro ⟨related, forward⟩
    exact envRel_monoRel (ValueRel before) (ValueRel after)
      (fun a b relation => valueRel_forward before after a b relation forward) env env' related
  · intro storeXs storeYs
    rintro ⟨related, forward⟩
    induction related with
    | nil => exact .nil
    | cons head _ ih =>
      exact .cons (storeValueRel_mono (ValueRel before) (ValueRel after)
        (fun a b relation => valueRel_forward before after a b relation forward) _ _ head) ih

end Flapjack.Compiler.Backend.SourceEval.Proofs
