module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForward

@[expose] public section

/-! Cases of the source evaluator recording-oracle clock suffix theorem. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack induction infrastructure: the expression conjunct at fixed input. -/
def ExpsSuffixAt {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
    (k ≤ s'.clock ∧ evaluate { s with clock := s.clock - k } env exps =
      ({ s' with clock := s'.clock - k }, res)) ∨
    ∃ s'', evaluate { s with clock := s.clock - k } env exps =
      (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState

/-- Flapjack induction infrastructure: the matching conjunct at fixed input. -/
def MatchSuffixAt {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
    (k ≤ s'.clock ∧ evaluateMatch { s with clock := s.clock - k } env x rows err =
      ({ s' with clock := s'.clock - k }, res)) ∨
    ∃ s'', evaluateMatch { s with clock := s.clock - k } env x rows err =
      (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState

/-- Flapjack induction infrastructure: the declaration conjunct at fixed input. -/
def DecsSuffixAt {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (decs : List Dec) : Prop :=
  ∀ (s' : State F) (res : Result (SemEnv Value) Value),
    evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
    (k ≤ s'.clock ∧ evaluateDecs { s with clock := s.clock - k } env decs =
      ({ s' with clock := s'.clock - k }, res)) ∨
    ∃ s'', evaluateDecs { s with clock := s.clock - k } env decs =
      (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState

/-- The empty expression-list case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_ExpsNil {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) : ExpsSuffixAt ci k s env [] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluate] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluate]⟩

/-- The literal case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Lit {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (lit : Lit) : ExpsSuffixAt ci k s env [.lit lit] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluate] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluate]⟩

/-- The function-value case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Fn {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    ExpsSuffixAt ci k s env [.fn name body] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluate] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluate]⟩

/-- The variable case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Var {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : Ident ModN VarN) : ExpsSuffixAt ci k s env [.var name] := by
  intro s' res ⟨run, _, bound⟩
  cases found : nsLookup env.v name <;> simp [evaluate, found, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;> exact Or.inl ⟨bound, by simp [evaluate, found, typeError]⟩

/-- The type-annotation case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Tannot {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (typ : AstT)
    (ih : ExpsSuffixAt ci k s env [expr]) : ExpsSuffixAt ci k s env [.tannot expr typ] := by
  intro s' res ⟨run, recorded, bound⟩
  simpa only [evaluate] using ih s' res ⟨by simpa only [evaluate] using run, recorded, bound⟩

/-- The location-annotation case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Lannot {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (ih : ExpsSuffixAt ci k s env [expr]) : ExpsSuffixAt ci k s env [.lannot expr loc] := by
  intro s' res ⟨run, recorded, bound⟩
  simpa only [evaluate] using ih s' res ⟨by simpa only [evaluate] using run, recorded, bound⟩
/-- The empty pattern-match case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_MatchNil {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (x err : Value) : MatchSuffixAt ci k s env x [] err := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluateMatch] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluateMatch]⟩

/-- The empty declaration-list case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_DecsNil {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) : DecsSuffixAt ci k s env [] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluateDecs] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluateDecs]⟩

/-- The type-abbreviation case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dtabbrev {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (vars : List TvarN) (name : TypeN) (typ : AstT) : DecsSuffixAt ci k s env [.dtabbrev loc vars name typ] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluateDecs] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluateDecs]⟩

/-- The exception declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dexn {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (name : ConN) (types : List AstT) : DecsSuffixAt ci k s env [.dexn loc name types] := by
  intro s' res ⟨run, _, bound⟩
  simp only [evaluateDecs] at run
  cases run
  exact Or.inl ⟨bound, by simp [evaluateDecs]⟩

/-- The datatype declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dtype {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (types : TypeDef) :
    DecsSuffixAt ci k s env [.dtype loc types] := by
  intro s' res ⟨run, _, bound⟩
  cases check : types.all checkDupCtors <;>
    simp [evaluateDecs, check, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;>
    exact Or.inl ⟨bound, by simp [evaluateDecs, check, typeError]⟩

/-- The recursive declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dletrec {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × AstHOL.Exp)) : DecsSuffixAt ci k s env [.dletrec loc funs] := by
  intro s' res ⟨run, _, bound⟩
  cases check : (decide (funs.map fun (name, _, _) => name).Nodup &&
      funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr)) <;>
    simp [evaluateDecs, check, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;>
    exact Or.inl ⟨bound, by simp [evaluateDecs, check, typeError]⟩
/-- The environment declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Denv {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : VarN) : DecsSuffixAt ci k s env [.denv name] := by
  intro s' res ⟨run, _, bound⟩
  cases declared : declareEnv s.evalState env with
  | none =>
    simp [evaluateDecs, declared, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluateDecs, declared, typeError]⟩
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simp [evaluateDecs, declared] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluateDecs, declared]⟩
/-- The expression-list sequencing case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_ExpsCons {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → ExpsSuffixAt ci k middle env (second :: rest)) ∧
      ExpsSuffixAt ci k s env [first]) : ExpsSuffixAt ci k s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluateConsSource] at run
  cases firstRun : evaluate s env [first] with
  | mk middle firstResult =>
    have firstSuffix := firstIH middle firstResult ⟨firstRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [first] middle firstResult ⟨firstRun, recorded⟩
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluateConsSource, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluateConsSource, equal]
    | val values =>
      simp only [firstRun] at run
      cases tailRun : evaluate middle env (second :: rest) with
      | mk last tailResult =>
        have tailRecorded := (evaluate_is_record_forward ci).1 middle env (second :: rest) last tailResult
          ⟨tailRun, firstRecorded.1⟩
        cases tailResult <;> simp only [tailRun] at run <;> cases run
        all_goals
          rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
          · have tailSuffix := tailIH middle (.val values) values ⟨firstRun, rfl⟩ s' _
              ⟨tailRun, firstRecorded.1, midBound⟩
            rcases tailSuffix with ⟨lastBound, tailEqual⟩ | ⟨short, tailEqual, forward⟩
            · left
              refine ⟨lastBound, ?_⟩
              rw [evaluateConsSource, firstEqual]
              simp only
              rw [tailEqual]
            · right
              refine ⟨short, ?_, forward⟩
              rw [evaluateConsSource, firstEqual]
              simp only
              rw [tailEqual]
          · right
            refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, tailRecorded.2.1⟩⟩
            rw [evaluateConsSource, firstEqual]
/-- The declaration-list sequencing case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_DecsCons {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (first second : Dec) (rest : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → DecsSuffixAt ci k middle (extendDecEnv inner env) (second :: rest)) ∧
      DecsSuffixAt ci k s env [first]) : DecsSuffixAt ci k s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluateDecsConsSource] at run
  cases firstRun : evaluateDecs s env [first] with
  | mk middle firstResult =>
    have firstSuffix := firstIH middle firstResult ⟨firstRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).2.2 s env [first] middle firstResult ⟨firstRun, recorded⟩
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluateDecsConsSource, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluateDecsConsSource, equal]
    | val inner =>
      simp only [firstRun] at run
      cases tailRun : evaluateDecs middle (extendDecEnv inner env) (second :: rest) with
      | mk last tailResult =>
        have tailRecorded := (evaluate_is_record_forward ci).2.2 middle (extendDecEnv inner env) (second :: rest) last tailResult
          ⟨tailRun, firstRecorded.1⟩
        cases tailResult <;> simp only [tailRun, combineDecResult] at run <;> cases run
        all_goals
          rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
          · have tailSuffix := tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' _
              ⟨tailRun, firstRecorded.1, midBound⟩
            rcases tailSuffix with ⟨lastBound, tailEqual⟩ | ⟨short, tailEqual, forward⟩
            · left
              refine ⟨lastBound, ?_⟩
              rw [evaluateDecsConsSource, firstEqual]
              simp only
              rw [tailEqual]
              rfl
            · right
              refine ⟨short, ?_, forward⟩
              rw [evaluateDecsConsSource, firstEqual]
              simp only
              rw [tailEqual]
              rfl
          · right
            refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, tailRecorded.2.1⟩⟩
            rw [evaluateDecsConsSource, firstEqual]
end Flapjack.Compiler.Backend.SourceEval.Proofs
