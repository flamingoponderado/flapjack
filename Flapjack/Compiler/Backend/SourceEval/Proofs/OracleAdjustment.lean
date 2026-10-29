import Flapjack.Compiler.Backend.SourceEval.Proofs

/-! Source evaluator oracle adjustment: environment bookkeeping lemmas. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_insert_decs"]
theorem isInsertDecs {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (s : EvalDecsState) :
    isInsertOracle ci f (some (.evalDecs s)) := by
  exact ⟨some (.evalDecs s), fun _ => 0, fun _ => (⟨0, 0⟩, Value.conv none [], []), rfl⟩

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "declare_env_adjust"]
theorem declareEnv_adjust {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (es : Option EvalState) (env : SemEnv Value) :
    declareEnv (adjustOracle ci f es) env =
      (declareEnv es env).map (fun (x, es₂) => (x, adjustOracle ci f es₂)) := by
  cases es with
  | none => rfl
  | some es =>
    cases es with
    | evalDecs s => cases s with | mk compiler compilerState counter decode => cases counter with | mk a rest => cases rest <;> rfl
    | evalOracle s =>
      simp only [adjustOracle, declareEnv]
      cases s.envs[s.generation]? <;> simp

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_reset"]
theorem adjustOracle_reset {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (es₁ es₂ : Option EvalState) :
    adjustOracle ci f (resetEnvGeneration es₁ es₂) =
      resetEnvGeneration (adjustOracle ci f es₁) (adjustOracle ci f es₂) := by
  cases es₁ with
  | none => cases es₂ <;> rfl
  | some es₁ =>
    cases es₁ <;> cases es₂ with
    | none => rfl
    | some es₂ => cases es₂ <;> simp [adjustOracle, resetEnvGeneration] <;> split <;> split <;> rfl

/-- For oracle states, insertion constrains the callback; its sequence can be
reconstructed by inserting the current sequence with shift zero. -/
theorem isInsertOracle_iff_callback {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (s : EvalOracleState) :
    isInsertOracle ci f (some (.evalOracle s)) ↔
      s.customDoEval = doEvalOracle (mkCompilerFunFromCi ci) f := by
  constructor
  · rintro ⟨state, shift, oracle, h⟩
    cases state with
    | none => simp [insertGenOracle] at h
    | some state =>
      cases state with
      | evalDecs decs => simp [insertGenOracle] at h
      | evalOracle prior =>
        simp only [insertGenOracle, Option.some.injEq, EvalState.evalOracle.injEq] at h
        exact congrArg EvalOracleState.customDoEval h
  · intro h
    refine ⟨some (.evalOracle s), fun _ => 0, s.oracle, ?_⟩
    cases s with
    | mk oracle callback envs generation =>
      simp only [insertGenOracle, Option.some.injEq, EvalState.evalOracle.injEq,
        EvalOracleState.mk.injEq, and_true] at ⊢
      exact ⟨by funext i; simp [Flapjack.holShiftSeq], h⟩

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_insert_related"]
theorem isInsert_related {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (es es₂ : EvalOracleState)
    (inserted : isInsertOracle ci f (some (.evalOracle es)))
    (related : es₂.customDoEval = es.customDoEval ∧ es₂.oracle = es.oracle) :
    isInsertOracle ci f (some (.evalOracle es₂)) := by
  apply (isInsertOracle_iff_callback ci f es₂).2
  exact related.1.trans ((isInsertOracle_iff_callback ci f es).1 inserted)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "is_insert_reset"]
theorem isInsert_reset {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (es₁ es₂ : Option EvalState) :
    isInsertOracle ci f (resetEnvGeneration es₁ es₂) ↔ isInsertOracle ci f es₂ := by
  cases es₁ with
  | none => rfl
  | some before =>
    cases es₂ with
    | none => cases before <;> rfl
    | some after =>
      cases before <;> cases after <;> simp only [resetEnvGeneration]
      all_goals first | rfl | exact iff_of_true (isInsertDecs ci f _) (isInsertDecs ci f _) | simp [isInsertOracle_iff_callback]

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "declare_env_is_insert"]
theorem declareEnv_isInsert {Config : Type} (ci : CompilerInstance Config)
    (f : List Dec → List Dec) (es : Option EvalState) (env : SemEnv Value)
    (x : Value) (es₂ : Option EvalState)
    (declared : declareEnv es env = some (x, es₂))
    (inserted : isInsertOracle ci f es) : isInsertOracle ci f es₂ := by
  cases es with
  | none => simp [declareEnv] at declared
  | some es =>
    cases es with
    | evalDecs state =>
      simp only [declareEnv, Option.some.injEq, Prod.mk.injEq] at declared
      obtain ⟨_, rfl⟩ := declared
      exact isInsertDecs ci f _
    | evalOracle state =>
      cases h : state.envs[state.generation]? with
      | none => simp [declareEnv, h] at declared
      | some generation =>
        simp [declareEnv, h] at declared
        obtain ⟨_, rfl⟩ := declared
        apply (isInsertOracle_iff_callback ci f _).2
        exact (isInsertOracle_iff_callback ci f state).1 inserted

/-- Changing the declaration transform maps only the successful callback's
declaration component; the oracle checks and state advancement are unchanged. -/
theorem doEvalOracle_comp (compiler : CompilerFun) (f g : List Dec → List Dec)
    (values : List Value) (oracle : EvalOracleFun) :
    doEvalOracle compiler (g ∘ f) values oracle =
      (doEvalOracle compiler f values oracle).map (fun (id, next, decs) => (id, next, g decs)) := by
  classical
  unfold doEvalOracle
  split <;> simp_all
  all_goals repeat' (split <;> simp_all)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_eval_adjust"]
theorem doEval_adjust {Config : Type} (ci : CompilerInstance Config)
    (f g : List Dec → List Dec) (values : List Value) (es : Option EvalState)
    (env : SemEnv Value) (decs : List Dec) (es₁ : Option EvalState)
    (success : doEval values es = some (env, decs, es₁))
    (inserted : isInsertOracle ci f es) :
    (doEval values (adjustOracle ci (g ∘ f) es) = some (env, g decs, adjustOracle ci (g ∘ f) es₁) ∨
     doEval values (adjustOracle ci (g ∘ f) es) = some (env, decs, adjustOracle ci (g ∘ f) es₁)) ∧
    isInsertOracle ci f es₁ := by
  classical
  cases es with
  | none => simp [doEval] at success
  | some es =>
    cases es with
    | evalDecs state =>
      simp only [doEval] at success
      split at success <;> simp_all
      all_goals repeat' (split at success <;> simp_all)
      all_goals
        obtain ⟨checks, rfl, rfl, rfl⟩ := success
        constructor
        · right
          have agrees := checks.2.2
          rw [checks.1] at agrees
          simp_all [doEval, adjustOracle]
        · exact isInsertDecs ci f _
    | evalOracle state =>
      have callback := (isInsertOracle_iff_callback ci f state).1 inserted
      simp only [doEval, callback] at success
      cases h : doEvalOracle (mkCompilerFunFromCi ci) f values state.oracle with
      | none => simp [h] at success
      | some result =>
        obtain ⟨id, next, ds⟩ := result
        simp only [h] at success
        cases lookup : lookupEnv state id with
        | none => simp [lookup] at success
        | some found =>
          simp [lookup] at success
          obtain ⟨rfl, rfl, rfl⟩ := success
          constructor
          · left
            simp only [lookupEnv] at lookup
            simp [adjustOracle, doEval, doEvalOracle_comp, h, lookupEnv, lookup, addEnvGeneration]
          · apply (isInsertOracle_iff_callback ci f _).2
            rfl

end Flapjack.Compiler.Backend.SourceEval.Proofs
