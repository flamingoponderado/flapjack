module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleReset
public import Flapjack.EvaluateHOL.Definition
public import Flapjack.EvaluateHOL.ClockFull

@[expose] public section

/-! Base cases of the source evaluator recording-state preservation proof. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack induction infrastructure: the common conclusion of the three
recording-state preservation conjuncts. -/
def RecordingStep {Config F : Type} (ci : CompilerInstance Config) (before after : State F) : Prop :=
  isRecord ci after.evalState ∧ recordForward before.evalState after.evalState ∧
    (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState before.evalState).oracle →
      recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState after.evalState).oracle)

/-- Flapjack induction infrastructure: the expression conjunct at fixed input. -/
def ExpsRecordAt {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluate s env exps = (s', res) ∧ isRecord ci s.evalState → RecordingStep ci s s'

/-- Flapjack induction infrastructure: the pattern-matching conjunct at fixed input. -/
def MatchRecordAt {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState → RecordingStep ci s s'

/-- Flapjack induction infrastructure: the declaration conjunct at fixed input. -/
def DecsRecordAt {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (decs : List Dec) : Prop :=
  ∀ (s' : State F) (res : Result (SemEnv Value) Value),
    evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState → RecordingStep ci s s'

/-- Flapjack infrastructure: a recording state preserves itself. -/
theorem recordingStep_refl {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (recorded : isRecord ci s.evalState) : RecordingStep ci s s :=
  ⟨recorded, recordForward_refl _, id⟩

/-- Flapjack infrastructure: changing fields outside the evaluation state is a
recording step. -/
theorem recordingStep_sameEval {Config F : Type} (ci : CompilerInstance Config) (s s' : State F)
    (recorded : isRecord ci s.evalState) (same : s'.evalState = s.evalState) : RecordingStep ci s s' := by
  simp only [RecordingStep, same]
  exact ⟨recorded, recordForward_refl _, id⟩

/-- Flapjack infrastructure: consecutive recording steps compose. -/
theorem recordingStep_trans {Config F : Type} (ci : CompilerInstance Config) (first middle last : State F)
    (steps : RecordingStep ci first middle ∧ RecordingStep ci middle last) : RecordingStep ci first last := by
  obtain ⟨⟨_, firstForward, firstWellFormed⟩, recorded, secondForward, secondWellFormed⟩ := steps
  exact ⟨recorded, recordForward_trans _ _ _ ⟨firstForward, secondForward⟩,
    fun h => secondWellFormed (firstWellFormed h)⟩

/-- The empty-expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_ExpsNil {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) : ExpsRecordAt ci s env [] := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by simpa [evaluate] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The expression-list sequencing induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_ExpsCons {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → ExpsRecordAt ci middle env (second :: rest)) ∧
      ExpsRecordAt ci s env [first]) : ExpsRecordAt ci s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluateConsSource] at run
  cases firstRun : evaluate s env [first] with
  | mk middle firstResult =>
    have firstStep := firstIH middle firstResult ⟨firstRun, recorded⟩
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      exact firstStep
    | val values =>
      simp only [firstRun] at run
      cases tailRun : evaluate middle env (second :: rest) with
      | mk last tailResult =>
        have tailStep := tailIH middle (.val values) values ⟨firstRun, rfl⟩ last tailResult
          ⟨tailRun, firstStep.1⟩
        cases tailResult <;> simp only [tailRun] at run <;> cases run <;>
          exact recordingStep_trans ci s middle s' ⟨firstStep, tailStep⟩

/-- The literal induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Lit {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (lit : Lit) : ExpsRecordAt ci s env [.lit lit] := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by simpa [evaluate] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The variable induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Var {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Ident ModN VarN) : ExpsRecordAt ci s env [.var name] := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by
    cases found : nsLookup env.v name <;> simpa [evaluate, found, typeError] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The function-value induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Fn {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    ExpsRecordAt ci s env [.fn name body] := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by simpa [evaluate] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The type-annotation induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Tannot {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (typ : AstT)
    (ih : ExpsRecordAt ci s env [expr]) : ExpsRecordAt ci s env [.tannot expr typ] := by
  intro s' res ⟨run, recorded⟩
  exact ih s' res ⟨by simpa [evaluate] using run, recorded⟩

/-- The location-annotation induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Lannot {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (ih : ExpsRecordAt ci s env [expr]) : ExpsRecordAt ci s env [.lannot expr loc] := by
  intro s' res ⟨run, recorded⟩
  exact ih s' res ⟨by simpa [evaluate] using run, recorded⟩

/-- The exception-raising induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Raise {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (ih : ExpsRecordAt ci s env [expr]) : ExpsRecordAt ci s env [.raise expr] := by
  intro s' res ⟨run, recorded⟩
  cases subRun : evaluate s env [expr] with
  | mk middle result =>
    have step := ih middle result ⟨subRun, recorded⟩
    cases result <;> simp [evaluate, subRun] at run <;> obtain ⟨rfl, _⟩ := run <;> exact step

/-- The empty-pattern-match induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_MatchNil {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (x err : Value) : MatchRecordAt ci s env x [] err := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by simpa [evaluateMatch] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The empty-declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_DecsNil {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) : DecsRecordAt ci s env [] := by
  intro s' res ⟨run, recorded⟩
  have eq : s = s' := by simpa [evaluateDecs] using congrArg Prod.fst run
  subst s'
  exact recordingStep_refl ci s recorded

/-- The declaration-list sequencing induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_DecsCons {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (first second : Dec) (rest : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → DecsRecordAt ci middle (extendDecEnv inner env) (second :: rest)) ∧
      DecsRecordAt ci s env [first]) : DecsRecordAt ci s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluateDecsConsSource] at run
  cases firstRun : evaluateDecs s env [first] with
  | mk middle firstResult =>
    have firstStep := firstIH middle firstResult ⟨firstRun, recorded⟩
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      exact firstStep
    | val inner =>
      simp only [firstRun] at run
      cases tailRun : evaluateDecs middle (extendDecEnv inner env) (second :: rest) with
      | mk last tailResult =>
        have tailStep := tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ last tailResult
          ⟨tailRun, firstStep.1⟩
        cases tailResult <;> simp only [tailRun, combineDecResult] at run <;> cases run <;>
          exact recordingStep_trans ci s middle s' ⟨firstStep, tailStep⟩

/-- The type-abbreviation declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dtabbrev {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (vars : List TvarN) (name : TypeN) (typ : AstT) :
    DecsRecordAt ci s env [.dtabbrev loc vars name typ] := by
  intro s' res ⟨run, recorded⟩
  have same : s'.evalState = s.evalState := by
    have eq : s = s' := by simpa [evaluateDecs] using congrArg Prod.fst run
    rw [← eq]
  exact recordingStep_sameEval ci s s' recorded same

/-- The datatype declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dtype {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (types : TypeDef) :
    DecsRecordAt ci s env [.dtype loc types] := by
  intro s' res ⟨run, recorded⟩
  have same : s'.evalState = s.evalState := by
    cases check : types.all checkDupCtors <;>
      simp [evaluateDecs, check, typeError] at run <;>
      obtain ⟨rfl, _⟩ := run <;> rfl
  exact recordingStep_sameEval ci s s' recorded same

/-- The exception declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dexn {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (name : ConN) (types : List AstT) : DecsRecordAt ci s env [.dexn loc name types] := by
  intro s' res ⟨run, recorded⟩
  have same : s'.evalState = s.evalState := by
    simp [evaluateDecs] at run
    obtain ⟨rfl, _⟩ := run
    rfl
  exact recordingStep_sameEval ci s s' recorded same

/-- The recursive declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dletrec {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × AstHOL.Exp)) : DecsRecordAt ci s env [.dletrec loc funs] := by
  intro s' res ⟨run, recorded⟩
  have same : s'.evalState = s.evalState := by
    cases check : (decide (funs.map fun (name, _, _) => name).Nodup &&
        funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr)) <;>
      simp [evaluateDecs, check, typeError] at run <;>
      obtain ⟨rfl, _⟩ := run <;> rfl
  exact recordingStep_sameEval ci s s' recorded same

/-- The environment declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Denv {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : VarN) : DecsRecordAt ci s env [.denv name] := by
  intro s' res ⟨run, recorded⟩
  cases declared : declareEnv s.evalState env with
  | none =>
    simp [evaluateDecs, declared, typeError] at run
    obtain ⟨rfl, _⟩ := run
    exact recordingStep_refl ci s recorded
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simp [evaluateDecs, declared] at run
    obtain ⟨rfl, _⟩ := run
    have facts := insert_declareEnv s.evalState env value next ci (oracleState s.evalState).oracle
      ⟨declared, recorded⟩
    exact ⟨facts.1, facts.2.1, facts.2.2.2⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
