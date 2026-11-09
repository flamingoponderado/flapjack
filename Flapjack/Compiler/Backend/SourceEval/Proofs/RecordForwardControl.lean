module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForwardBase

@[expose] public section

/-! Control and declaration cases of recording-state preservation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The module declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dmod {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (ih : DecsRecordAt ci s env decs) : DecsRecordAt ci s env [.dmod name decs] := by
  intro s' res ⟨run, recorded⟩
  cases innerRun : evaluateDecs s env decs with
  | mk middle result =>
    have step := ih middle result ⟨innerRun, recorded⟩
    cases result <;> simp [evaluateDecs, innerRun] at run <;> obtain ⟨rfl, _⟩ := run <;> exact step

/-- The local declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dlocal {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (locals decs : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env locals = (middle, outcome) ∧
      outcome = .val inner → DecsRecordAt ci middle (extendDecEnv inner env) decs) ∧
      DecsRecordAt ci s env locals) : DecsRecordAt ci s env [.dlocal locals decs] := by
  obtain ⟨bodyIH, localsIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluateDecs, (fixClockEvaluate s env [] locals).2] at run
  cases localRun : evaluateDecs s env locals with
  | mk middle result =>
    have firstStep := localsIH middle result ⟨localRun, recorded⟩
    cases result with
    | err error =>
      simp only [localRun] at run
      cases run
      exact firstStep
    | val inner =>
      simp only [localRun] at run
      have lastStep := bodyIH middle (.val inner) inner ⟨localRun, rfl⟩ s' res ⟨run, firstStep.1⟩
      exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩

/-- The recursive-binding induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Letrec {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : (funs.map fun (name, _, _) => name).Nodup →
      ExpsRecordAt ci s { env with v := buildRecEnv funs env env.v } [body]) :
    ExpsRecordAt ci s env [.letrec funs body] := by
  intro s' res ⟨run, recorded⟩
  by_cases distinct : (funs.map fun (name, _, _) => name).Nodup
  · exact ih distinct s' res ⟨by simpa [evaluate, distinct] using run, recorded⟩
  · simp [evaluate, distinct, typeError] at run
    obtain ⟨rfl, _⟩ := run
    exact recordingStep_refl ci s recorded

/-- The constructor-expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Con {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : doConCheck env.c name args.length = true → ExpsRecordAt ci s env args.reverse) :
    ExpsRecordAt ci s env [.con name args] := by
  intro s' res ⟨run, recorded⟩
  by_cases check : doConCheck env.c name args.length = true
  · rw [evaluate] at run
    simp only [check, ↓reduceIte] at run
    cases subRun : evaluate s env args.reverse with
    | mk middle result =>
      have step := ih check middle result ⟨subRun, recorded⟩
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        exact step
      | val values =>
        cases built : buildConv env.c name values.reverse <;>
          simp [subRun, built, typeError] at run <;> obtain ⟨rfl, _⟩ := run <;> exact step
  · simp [evaluate, check, typeError] at run
    obtain ⟨rfl, _⟩ := run
    exact recordingStep_refl ci s recorded

/-- The value declaration induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Dlet {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      ExpsRecordAt ci s env [expr]) : DecsRecordAt ci s env [.dlet loc pat expr] := by
  intro s' res ⟨run, recorded⟩
  by_cases guard : (decide (patBindings pat).Nodup && everyExp (oneConCheck env.c) expr) = true
  · have parts : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true := by simpa using guard
    rw [evaluateDecs] at run
    simp only [guard, ↓reduceIte] at run
    cases subRun : evaluate s env [expr] with
    | mk middle result =>
      have step := ih parts middle result ⟨subRun, recorded⟩
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        exact step
      | val values =>
        cases matched : pmatch env.c middle.refs pat (headValue values) [] <;>
          simp [subRun, matched, typeError] at run <;> obtain ⟨rfl, _⟩ := run <;> exact step
  · simp [evaluateDecs, guard, typeError] at run
    obtain ⟨rfl, _⟩ := run
    exact recordingStep_refl ci s recorded

/-- The nonempty pattern-match induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_MatchCons {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp)) (err : Value)
    (ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      ExpsRecordAt ci s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        MatchRecordAt ci s env x rows err)) : MatchRecordAt ci s env x ((pat, expr) :: rows) err := by
  obtain ⟨bodyIH, restIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  by_cases distinct : (patBindings pat).Nodup
  · cases matched : pmatch env.c s.refs pat x [] with
    | noMatch =>
      exact restIH ⟨distinct, matched⟩ s' res ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded⟩
    | typeError =>
      simp [evaluateMatch, distinct, matched, typeError] at run
      obtain ⟨rfl, _⟩ := run
      exact recordingStep_refl ci s recorded
    | «match» bindings =>
      exact bodyIH bindings ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded⟩
  · simp [evaluateMatch, distinct, typeError] at run
    obtain ⟨rfl, _⟩ := run
    exact recordingStep_refl ci s recorded

/-- The let-expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Let {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Option VarN) (bound body : AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      ExpsRecordAt ci middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      ExpsRecordAt ci s env [bound]) : ExpsRecordAt ci s env [.let_ name bound body] := by
  obtain ⟨bodyIH, boundIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env [bound] []).1] at run
  cases boundRun : evaluate s env [bound] with
  | mk middle result =>
    have firstStep := boundIH middle result ⟨boundRun, recorded⟩
    cases result with
    | err error =>
      simp only [boundRun] at run
      cases run
      exact firstStep
    | val values =>
      simp only [boundRun] at run
      have lastStep := bodyIH middle (.val values) values ⟨boundRun, rfl⟩ s' res ⟨run, firstStep.1⟩
      exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩

/-- The conditional-expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_If {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (cond yes no : AstHOL.Exp)
    (ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      ExpsRecordAt ci middle env [branch]) ∧ ExpsRecordAt ci s env [cond]) :
    ExpsRecordAt ci s env [.if_ cond yes no] := by
  obtain ⟨branchIH, condIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env [cond] []).1] at run
  cases condRun : evaluate s env [cond] with
  | mk middle result =>
    have firstStep := condIH middle result ⟨condRun, recorded⟩
    cases result with
    | err error => simp only [condRun] at run; cases run; exact firstStep
    | val values =>
      simp only [condRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨rfl, _⟩ := run
        exact firstStep
      next branch chosen =>
        have lastStep := branchIH middle (.val values) values branch ⟨condRun, rfl, chosen⟩
          s' res ⟨run, firstStep.1⟩
        exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩

/-- The short-circuit expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Log {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (op : Lop) (first second : AstHOL.Exp)
    (ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      ExpsRecordAt ci middle env [branch]) ∧ ExpsRecordAt ci s env [first]) :
    ExpsRecordAt ci s env [.log op first second] := by
  obtain ⟨branchIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env [first] []).1] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    have firstStep := firstIH middle result ⟨firstRun, recorded⟩
    cases result with
    | err error => simp only [firstRun] at run; cases run; exact firstStep
    | val values =>
      simp only [firstRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨rfl, _⟩ := run
        exact firstStep
      next _ _ =>
        cases run
        exact firstStep
      next branch chosen =>
        have lastStep := branchIH middle (.val values) values (.exp branch) branch
          ⟨firstRun, rfl, chosen, rfl⟩ s' res ⟨run, firstStep.1⟩
        exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩

/-- The match-expression induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Mat {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
      MatchRecordAt ci middle env (headValue values) rows bindExnV) ∧ ExpsRecordAt ci s env [expr]) :
    ExpsRecordAt ci s env [.mat expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    have firstStep := exprIH middle result ⟨exprRun, recorded⟩
    cases result with
    | err error => simp only [exprRun] at run; cases run; exact firstStep
    | val values =>
      simp only [exprRun] at run
      by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true
      · simp only [check, ↓reduceIte] at run
        have lastStep := matchIH middle (.val values) values ⟨exprRun, rfl, check⟩ s' res ⟨run, firstStep.1⟩
        exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩
      · simp [check, typeError] at run
        obtain ⟨rfl, _⟩ := run
        exact firstStep

/-- The exception-handler induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_Handle {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .err err ∧ err = .raise value ∧
      canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
      MatchRecordAt ci middle env value rows value) ∧ ExpsRecordAt ci s env [expr]) :
    ExpsRecordAt ci s env [.handle expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    have firstStep := exprIH middle result ⟨exprRun, recorded⟩
    cases result with
    | val values => simp only [exprRun] at run; cases run; exact firstStep
    | err error =>
      cases error with
      | abort error => simp only [exprRun] at run; cases run; exact firstStep
      | raise value =>
        simp only [exprRun] at run
        by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true
        · simp only [check, ↓reduceIte] at run
          have lastStep := matchIH middle (.err (.raise value)) (.raise value) value
            ⟨exprRun, rfl, rfl, check⟩ s' res ⟨run, firstStep.1⟩
          exact recordingStep_trans ci s middle s' ⟨firstStep, lastStep⟩
        · simp [check, typeError] at run
          obtain ⟨rfl, _⟩ := run
          exact firstStep
end Flapjack.Compiler.Backend.SourceEval.Proofs
