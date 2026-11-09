module

public import Flapjack.EvaluateHOL.ClockFull

@[expose] public section

/-! Base cases for evaluation without an Eval state. -/
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack induction infrastructure: the expression simulation conjunct. -/
def NoEvalExpsAt {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (exps : List AstHOL.Exp) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluate s env exps = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
    s'.evalState = none ∧ evaluate { s with evalState := es } env exps = ({ s' with evalState := es }, res)

/-- Flapjack induction infrastructure: the match simulation conjunct. -/
def NoEvalMatchAt {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluateMatch s env x rows err = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
    s'.evalState = none ∧ evaluateMatch { s with evalState := es } env x rows err = ({ s' with evalState := es }, res)

/-- Flapjack induction infrastructure: the declaration simulation conjunct. -/
def NoEvalDecsAt {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (decs : List Dec) : Prop :=
  ∀ (s' : State F) (res : Result (SemEnv Value) Value),
    evaluateDecs s env decs = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
    s'.evalState = none ∧ evaluateDecs { s with evalState := es } env decs = ({ s' with evalState := es }, res)

/-- The empty-expression induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_ExpsNil {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value) :
    NoEvalExpsAt es s env [] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluate] at run
  cases run
  exact ⟨absent, by simp [evaluate]⟩

/-- The literal induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Lit {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value) (lit : Lit) :
    NoEvalExpsAt es s env [.lit lit] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluate] at run
  cases run
  exact ⟨absent, by simp [evaluate]⟩

/-- The function induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Fn {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : VarN) (body : AstHOL.Exp) : NoEvalExpsAt es s env [.fn name body] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluate] at run
  cases run
  exact ⟨absent, by simp [evaluate]⟩

/-- The variable induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Var {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : Ident ModN VarN) : NoEvalExpsAt es s env [.var name] := by
  intro s' res ⟨run, absent, _⟩
  cases found : nsLookup env.v name <;> simp [evaluate, found, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;> exact ⟨absent, by simp [evaluate, found, typeError]⟩

/-- The empty-match induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_MatchNil {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (x err : Value) : NoEvalMatchAt es s env x [] err := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluateMatch] at run
  cases run
  exact ⟨absent, by simp [evaluateMatch]⟩

/-- The empty-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_DecsNil {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value) :
    NoEvalDecsAt es s env [] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluateDecs] at run
  cases run
  exact ⟨absent, by simp [evaluateDecs]⟩

/-- The type-annotation induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Tannot {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (expr : AstHOL.Exp) (typ : AstT) (ih : NoEvalExpsAt es s env [expr]) :
    NoEvalExpsAt es s env [.tannot expr typ] := by
  intro s' res ⟨run, absent, safe⟩
  simpa only [evaluate] using ih s' res ⟨by simpa only [evaluate] using run, absent, safe⟩

/-- The location-annotation induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Lannot {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) (ih : NoEvalExpsAt es s env [expr]) :
    NoEvalExpsAt es s env [.lannot expr loc] := by
  intro s' res ⟨run, absent, safe⟩
  simpa only [evaluate] using ih s' res ⟨by simpa only [evaluate] using run, absent, safe⟩
/-- The type-abbreviation induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dtabbrev {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT) :
    NoEvalDecsAt es s env [.dtabbrev loc vars name typ] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluateDecs] at run
  cases run
  exact ⟨absent, by simp [evaluateDecs]⟩

/-- The exception-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dexn {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT) :
    NoEvalDecsAt es s env [.dexn loc name types] := by
  intro s' res ⟨run, absent, _⟩
  simp only [evaluateDecs] at run
  cases run
  exact ⟨absent, by simp [evaluateDecs]⟩

/-- The datatype-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dtype {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (types : TypeDef) : NoEvalDecsAt es s env [.dtype loc types] := by
  intro s' res ⟨run, absent, _⟩
  cases check : types.all checkDupCtors <;>
    simp [evaluateDecs, check, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;>
    exact ⟨absent, by simp [evaluateDecs, check, typeError]⟩

/-- The recursive-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dletrec {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    NoEvalDecsAt es s env [.dletrec loc funs] := by
  intro s' res ⟨run, absent, _⟩
  cases check : (decide (funs.map fun (name, _, _) => name).Nodup &&
      funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr)) <;>
    simp [evaluateDecs, check, typeError] at run <;>
    obtain ⟨rfl, rfl⟩ := run <;>
    exact ⟨absent, by simp [evaluateDecs, check, typeError]⟩

/-- The environment-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Denv {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : VarN) : NoEvalDecsAt es s env [.denv name] := by
  intro s' res ⟨run, absent, safe⟩
  simp [evaluateDecs, absent, declareEnv, typeError] at run
  obtain ⟨_, rfl⟩ := run
  exact (safe rfl).elim
/-- The raise induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Raise {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (expr : AstHOL.Exp) (ih : NoEvalExpsAt es s env [expr]) :
    NoEvalExpsAt es s env [.raise expr] := by
  intro s' res ⟨run, absent, safe⟩
  cases subRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | err error =>
      simp [evaluate, subRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.err error) ⟨subRun, absent, safe⟩
      exact ⟨target.1, by simp [evaluate, target.2]⟩
    | val values =>
      simp [evaluate, subRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.val values) ⟨subRun, absent, by simp⟩
      exact ⟨target.1, by simp [evaluate, target.2]⟩
/-- The expression-list sequencing induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_ExpsCons {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → NoEvalExpsAt es middle env (second :: rest)) ∧
      NoEvalExpsAt es s env [first]) : NoEvalExpsAt es s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluateConsSource] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluateConsSource, target.2]
    | val values =>
      simp only [firstRun] at run
      have firstTarget := firstIH middle (.val values) ⟨firstRun, absent, by simp⟩
      cases tailRun : evaluate middle env (second :: rest) with
      | mk last tailResult =>
        cases tailResult <;> simp only [tailRun] at run <;> cases run
        all_goals
          have tailTarget := tailIH middle (.val values) values ⟨firstRun, rfl⟩ s' _
            ⟨tailRun, firstTarget.1, by intro bad; apply safe; cases bad <;> rfl⟩
          refine ⟨tailTarget.1, ?_⟩
          rw [evaluateConsSource, firstTarget.2]
          simp only
          rw [tailTarget.2]
/-- The declaration-list sequencing induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_DecsCons {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → NoEvalDecsAt es middle (extendDecEnv inner env) (second :: rest)) ∧
      NoEvalDecsAt es s env [first]) : NoEvalDecsAt es s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluateDecsConsSource] at run
  cases firstRun : evaluateDecs s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluateDecsConsSource, target.2]
    | val inner =>
      simp only [firstRun] at run
      have firstTarget := firstIH middle (.val inner) ⟨firstRun, absent, by simp⟩
      cases tailRun : evaluateDecs middle (extendDecEnv inner env) (second :: rest) with
      | mk last tailResult =>
        cases tailResult <;> simp only [tailRun, combineDecResult] at run <;> cases run
        all_goals
          have tailTarget := tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' _
            ⟨tailRun, firstTarget.1, by intro bad; apply safe; cases bad <;> rfl⟩
          refine ⟨tailTarget.1, ?_⟩
          rw [evaluateDecsConsSource, firstTarget.2]
          simp only
          rw [tailTarget.2]
          rfl
/-- The recursive-binding induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Letrec {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : (funs.map fun (name, _, _) => name).Nodup →
      NoEvalExpsAt es s { env with v := buildRecEnv funs env env.v } [body]) :
    NoEvalExpsAt es s env [.letrec funs body] := by
  intro s' res ⟨run, absent, safe⟩
  by_cases distinct : (funs.map fun (name, _, _) => name).Nodup
  · have target := ih distinct s' res ⟨by simpa [evaluate, distinct] using run, absent, safe⟩
    simpa [evaluate, distinct] using target
  · simp [evaluate, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim

/-- The module-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dmod {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : ModN) (decs : List Dec) (ih : NoEvalDecsAt es s env decs) :
    NoEvalDecsAt es s env [.dmod name decs] := by
  intro s' res ⟨run, absent, safe⟩
  cases innerRun : evaluateDecs s env decs with
  | mk middle result =>
    cases result with
    | err error =>
      simp [evaluateDecs, innerRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.err error) ⟨innerRun, absent, safe⟩
      exact ⟨target.1, by simp [evaluateDecs, target.2]⟩
    | val inner =>
      simp [evaluateDecs, innerRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.val inner) ⟨innerRun, absent, by simp⟩
      exact ⟨target.1, by simp [evaluateDecs, target.2]⟩
/-- The nonempty match induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_MatchCons {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (x : Value) (pat : Pat) (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) (err : Value)
    (ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      NoEvalExpsAt es s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        NoEvalMatchAt es s env x rows err)) : NoEvalMatchAt es s env x ((pat, expr) :: rows) err := by
  obtain ⟨bodyIH, restIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  by_cases distinct : (patBindings pat).Nodup
  · cases matched : pmatch env.c s.refs pat x [] with
    | noMatch =>
      have target := restIH ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, absent, safe⟩
      simpa [evaluateMatch, distinct, matched] using target
    | typeError =>
      simp [evaluateMatch, distinct, matched, typeError] at run
      obtain ⟨_, rfl⟩ := run
      exact (safe rfl).elim
    | «match» bindings =>
      have target := bodyIH bindings ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, absent, safe⟩
      simpa [evaluateMatch, distinct, matched] using target
  · simp [evaluateMatch, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The constructor-expression induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Con {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : doConCheck env.c name args.length = true → NoEvalExpsAt es s env args.reverse) :
    NoEvalExpsAt es s env [.con name args] := by
  intro s' res ⟨run, absent, safe⟩
  by_cases check : doConCheck env.c name args.length = true
  · rw [evaluate] at run
    simp only [check, ↓reduceIte] at run
    cases subRun : evaluate s env args.reverse with
    | mk middle result =>
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        have target := ih check s' (.err error) ⟨subRun, absent, safe⟩
        exact ⟨target.1, by simp [evaluate, check, target.2]⟩
      | val values =>
        cases built : buildConv env.c name values.reverse with
        | none =>
          simp [subRun, built, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some value =>
          simp [subRun, built] at run
          obtain ⟨rfl, rfl⟩ := run
          have target := ih check middle (.val values) ⟨subRun, absent, by simp⟩
          exact ⟨target.1, by simp [evaluate, check, target.2, built]⟩
  · simp [evaluate, check, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim

/-- The value-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dlet {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      NoEvalExpsAt es s env [expr]) : NoEvalDecsAt es s env [.dlet loc pat expr] := by
  intro s' res ⟨run, absent, safe⟩
  by_cases guard : (decide (patBindings pat).Nodup && everyExp (oneConCheck env.c) expr) = true
  · have parts : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true := by simpa using guard
    rw [evaluateDecs] at run
    simp only [guard, ↓reduceIte] at run
    cases subRun : evaluate s env [expr] with
    | mk middle result =>
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        have target := ih parts s' (.err error) ⟨subRun, absent, by intro bad; apply safe; cases bad; rfl⟩
        exact ⟨target.1, by simp [evaluateDecs, guard, target.2]⟩
      | val values =>
        cases matched : pmatch env.c middle.refs pat (headValue values) [] <;>
          simp [subRun, matched, typeError] at run <;> obtain ⟨rfl, rfl⟩ := run
        all_goals
          have target := ih parts middle (.val values) ⟨subRun, absent, by simp⟩
          exact ⟨target.1, by simp [evaluateDecs, guard, target.2, matched, typeError]⟩
  · simp [evaluateDecs, guard, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The local-declaration induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Dlocal {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (locals decs : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env locals = (middle, outcome) ∧
      outcome = .val inner → NoEvalDecsAt es middle (extendDecEnv inner env) decs) ∧
      NoEvalDecsAt es s env locals) : NoEvalDecsAt es s env [.dlocal locals decs] := by
  obtain ⟨bodyIH, localsIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluateDecs, (fixClockEvaluate s env [] locals).2] at run
  cases localRun : evaluateDecs s env locals with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [localRun] at run
      cases run
      have target := localsIH s' (.err error) ⟨localRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, target.2]
    | val inner =>
      simp only [localRun] at run
      have firstTarget := localsIH middle (.val inner) ⟨localRun, absent, by simp⟩
      have bodyTarget := bodyIH middle (.val inner) inner ⟨localRun, rfl⟩ s' res
        ⟨run, firstTarget.1, safe⟩
      refine ⟨bodyTarget.1, ?_⟩
      rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, firstTarget.2]
      exact bodyTarget.2

/-- The let-expression induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Let {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (name : Option VarN) (bound body : AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      NoEvalExpsAt es middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      NoEvalExpsAt es s env [bound]) : NoEvalExpsAt es s env [.let_ name bound body] := by
  obtain ⟨bodyIH, boundIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env [bound] []).1] at run
  cases boundRun : evaluate s env [bound] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [boundRun] at run
      cases run
      have target := boundIH s' (.err error) ⟨boundRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, target.2]
    | val values =>
      simp only [boundRun] at run
      have firstTarget := boundIH middle (.val values) ⟨boundRun, absent, by simp⟩
      have bodyTarget := bodyIH middle (.val values) values ⟨boundRun, rfl⟩ s' res
        ⟨run, firstTarget.1, safe⟩
      refine ⟨bodyTarget.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, firstTarget.2]
      exact bodyTarget.2
end Flapjack.EvaluateProps
