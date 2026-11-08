import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForward

/-! Base cases of source evaluator oracle insertion correctness. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack infrastructure: update a source state with HOL's oracle insertion. -/
noncomputable abbrev insertOracleState {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) : State F :=
  { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState }

/-- Flapjack induction infrastructure: the expression conjunct at fixed input. -/
def ExpsInsertAt {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
      oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
    evaluate (insertOracleState ci oracle s) env exps = (insertOracleState ci oracle s', res)

/-- Flapjack induction infrastructure: the pattern-matching conjunct at fixed input. -/
def MatchInsertAt {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value),
    evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
      oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
    evaluateMatch (insertOracleState ci oracle s) env x rows err = (insertOracleState ci oracle s', res)

/-- Flapjack induction infrastructure: the declaration conjunct at fixed input. -/
def DecsInsertAt {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (s : State F) (env : SemEnv Value) (decs : List Dec) : Prop :=
  ∀ (s' : State F) (res : Result (SemEnv Value) Value),
    evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
      oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
    evaluateDecs (insertOracleState ci oracle s) env decs = (insertOracleState ci oracle s', res)

/-- The empty-expression induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_ExpsNil {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) : ExpsInsertAt ci oracle s env [] := by
  intro s' res ⟨run, _⟩
  simpa [evaluate] using congrArg (fun p : State F × Result (List Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The empty-pattern-match induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_MatchNil {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (x err : Value) :
    MatchInsertAt ci oracle s env x [] err := by
  intro s' res ⟨run, _⟩
  simpa [evaluateMatch] using congrArg (fun p : State F × Result (List Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The empty-declaration induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_DecsNil {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) : DecsInsertAt ci oracle s env [] := by
  intro s' res ⟨run, _⟩
  simpa [evaluateDecs] using congrArg (fun p : State F × Result (SemEnv Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The literal induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Lit {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (lit : Lit) :
    ExpsInsertAt ci oracle s env [.lit lit] := by
  intro s' res ⟨run, _⟩
  simpa [evaluate] using congrArg (fun p : State F × Result (List Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The function-value induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Fn {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    ExpsInsertAt ci oracle s env [.fn name body] := by
  intro s' res ⟨run, _⟩
  simpa [evaluate] using congrArg (fun p : State F × Result (List Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The variable induction case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Var {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (name : Ident ModN VarN) :
    ExpsInsertAt ci oracle s env [.var name] := by
  intro s' res ⟨run, _⟩
  cases found : nsLookup env.v name <;>
    simpa [evaluate, found, typeError, insertOracleState] using
      congrArg (fun p : State F × Result (List Value) Value => (insertOracleState ci oracle p.1, p.2)) run

/-- The type-abbreviation declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dtabbrev {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (vars : List TvarN) (name : TypeN) (typ : AstT) : DecsInsertAt ci oracle s env [.dtabbrev loc vars name typ] := by
  intro s' res ⟨run, _⟩
  simpa [evaluateDecs] using congrArg (fun p : State F × Result (SemEnv Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The datatype declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dtype {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (types : TypeDef) : DecsInsertAt ci oracle s env [.dtype loc types] := by
  intro s' res ⟨run, _⟩
  cases check : types.all checkDupCtors <;>
    simpa [evaluateDecs, check, typeError, insertOracleState] using
      congrArg (fun p : State F × Result (SemEnv Value) Value => (insertOracleState ci oracle p.1, p.2)) run

/-- The exception declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dexn {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (name : ConN) (types : List AstT) : DecsInsertAt ci oracle s env [.dexn loc name types] := by
  intro s' res ⟨run, _⟩
  simpa [evaluateDecs, insertOracleState] using congrArg (fun p : State F × Result (SemEnv Value) Value =>
    (insertOracleState ci oracle p.1, p.2)) run

/-- The recursive declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dletrec {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × AstHOL.Exp)) : DecsInsertAt ci oracle s env [.dletrec loc funs] := by
  intro s' res ⟨run, _⟩
  cases check : (decide (funs.map fun (name, _, _) => name).Nodup &&
      funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr)) <;>
    simpa [evaluateDecs, check, typeError, insertOracleState] using
      congrArg (fun p : State F × Result (SemEnv Value) Value => (insertOracleState ci oracle p.1, p.2)) run

/-- The environment declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Denv {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (name : VarN) :
    DecsInsertAt ci oracle s env [.denv name] := by
  intro s' res ⟨run, recorded, agrees, _, safe⟩
  cases declared : declareEnv s.evalState env with
  | none =>
    simp [evaluateDecs, declared, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simp [evaluateDecs, declared] at run
    obtain ⟨rfl, rfl⟩ := run
    have facts := insert_declareEnv s.evalState env value next ci oracle ⟨declared, recorded⟩
    have target := facts.2.2.1 agrees
    simp [evaluateDecs, insertOracleState, target]

/-- The type-annotation case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Tannot {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (typ : AstT)
    (ih : ExpsInsertAt ci oracle s env [expr]) : ExpsInsertAt ci oracle s env [.tannot expr typ] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  simpa [evaluate] using ih s' res ⟨by simpa [evaluate] using run, recorded, agrees, wf, safe⟩

/-- The location-annotation case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Lannot {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (loc : Flapjack.Misc.Location.Locs) (ih : ExpsInsertAt ci oracle s env [expr]) :
    ExpsInsertAt ci oracle s env [.lannot expr loc] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  simpa [evaluate] using ih s' res ⟨by simpa [evaluate] using run, recorded, agrees, wf, safe⟩

/-- The exception-raising case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Raise {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (ih : ExpsInsertAt ci oracle s env [expr]) : ExpsInsertAt ci oracle s env [.raise expr] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  cases subRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | err error =>
      simp [evaluate, subRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.err error) ⟨subRun, recorded, agrees, wf, safe⟩
      simp [evaluate, target]
    | val values =>
      simp [evaluate, subRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.val values) ⟨subRun, recorded, agrees, wf, by simp⟩
      simp [evaluate, target]

/-- The expression-list sequencing case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_ExpsCons {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → ExpsInsertAt ci oracle middle env (second :: rest)) ∧
      ExpsInsertAt ci oracle s env [first]) : ExpsInsertAt ci oracle s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluateConsSource] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, recorded, agrees, wf, safe⟩
      simp [evaluateConsSource, target]
    | val values =>
      simp only [firstRun] at run
      have firstRecorded := (evaluate_is_record_forward ci).1 s env [first] middle (.val values)
        ⟨firstRun, recorded⟩
      cases tailRun : evaluate middle env (second :: rest) with
      | mk last tailResult =>
        have tailRecorded := (evaluate_is_record_forward ci).1 middle env (second :: rest) last tailResult
          ⟨tailRun, firstRecorded.1⟩
        cases tailResult with
        | err error =>
          simp only [tailRun] at run
          cases run
          have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, tailRecorded.2.1⟩
          have targetFirst := firstIH middle (.val values) ⟨firstRun, recorded, agreesMiddle, wf, by simp⟩
          have targetTail := tailIH middle (.val values) values ⟨firstRun, rfl⟩ s' (.err error)
            ⟨tailRun, firstRecorded.1, agrees, wf, safe⟩
          simp [evaluateConsSource, targetFirst, targetTail]
        | val tailValues =>
          simp only [tailRun] at run
          cases run
          have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, tailRecorded.2.1⟩
          have targetFirst := firstIH middle (.val values) ⟨firstRun, recorded, agreesMiddle, wf, by simp⟩
          have targetTail := tailIH middle (.val values) values ⟨firstRun, rfl⟩ s' (.val tailValues)
            ⟨tailRun, firstRecorded.1, agrees, wf, by simp⟩
          simp [evaluateConsSource, targetFirst, targetTail]

/-- The declaration-list sequencing case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_DecsCons {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (first second : Dec) (rest : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → DecsInsertAt ci oracle middle (extendDecEnv inner env) (second :: rest)) ∧
      DecsInsertAt ci oracle s env [first]) : DecsInsertAt ci oracle s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluateDecsConsSource] at run
  cases firstRun : evaluateDecs s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, recorded, agrees, wf, safe⟩
      simp [evaluateDecsConsSource, target]
    | val inner =>
      simp only [firstRun] at run
      have firstRecorded := (evaluate_is_record_forward ci).2.2 s env [first] middle (.val inner)
        ⟨firstRun, recorded⟩
      cases tailRun : evaluateDecs middle (extendDecEnv inner env) (second :: rest) with
      | mk last tailResult =>
        have tailRecorded := (evaluate_is_record_forward ci).2.2 middle (extendDecEnv inner env)
          (second :: rest) last tailResult ⟨tailRun, firstRecorded.1⟩
        cases tailResult with
        | err error =>
          simp only [tailRun, combineDecResult] at run
          cases run
          have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, tailRecorded.2.1⟩
          have targetFirst := firstIH middle (.val inner) ⟨firstRun, recorded, agreesMiddle, wf, by simp⟩
          have targetTail := tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' (.err error)
            ⟨tailRun, firstRecorded.1, agrees, wf, safe⟩
          simp [evaluateDecsConsSource, targetFirst, targetTail, combineDecResult]

        | val tailEnv =>
          simp only [tailRun, combineDecResult] at run
          cases run
          have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, tailRecorded.2.1⟩
          have targetFirst := firstIH middle (.val inner) ⟨firstRun, recorded, agreesMiddle, wf, by simp⟩
          have targetTail := tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' (.val tailEnv)
            ⟨tailRun, firstRecorded.1, agrees, wf, by simp⟩
          simp [evaluateDecsConsSource, targetFirst, targetTail, combineDecResult]

/-- The module declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dmod {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (ih : DecsInsertAt ci oracle s env decs) : DecsInsertAt ci oracle s env [.dmod name decs] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  cases innerRun : evaluateDecs s env decs with
  | mk middle result =>
    cases result with
    | err error =>
      simp [evaluateDecs, innerRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.err error) ⟨innerRun, recorded, agrees, wf, safe⟩
      simp [evaluateDecs, target]
    | val inner =>
      simp [evaluateDecs, innerRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have target := ih middle (.val inner) ⟨innerRun, recorded, agrees, wf, by simp⟩
      simp [evaluateDecs, target]
/-- The recursive-binding case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Letrec {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : (funs.map fun (name, _, _) => name).Nodup →
      ExpsInsertAt ci oracle s { env with v := buildRecEnv funs env env.v } [body]) :
    ExpsInsertAt ci oracle s env [.letrec funs body] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  by_cases distinct : (funs.map fun (name, _, _) => name).Nodup
  · have target := ih distinct s' res ⟨by simpa [evaluate, distinct] using run, recorded, agrees, wf, safe⟩
    simpa [evaluate, distinct, insertOracleState] using target
  · simp [evaluate, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The constructor-expression case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Con {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : doConCheck env.c name args.length = true → ExpsInsertAt ci oracle s env args.reverse) :
    ExpsInsertAt ci oracle s env [.con name args] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  by_cases check : doConCheck env.c name args.length = true
  · rw [evaluate] at run
    simp only [check, ↓reduceIte] at run
    cases subRun : evaluate s env args.reverse with
    | mk middle result =>
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        have target := ih check s' (.err error) ⟨subRun, recorded, agrees, wf, safe⟩
        simp [evaluate, check, target]
      | val values =>
        cases built : buildConv env.c name values.reverse with
        | none =>
          simp [subRun, built, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some value =>
          simp [subRun, built] at run
          obtain ⟨rfl, rfl⟩ := run
          have target := ih check middle (.val values) ⟨subRun, recorded, agrees, wf, by simp⟩
          simp [evaluate, check, target, built]
  · simp [evaluate, check, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The nonempty pattern-match case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_MatchCons {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp)) (err : Value)
    (ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      ExpsInsertAt ci oracle s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        MatchInsertAt ci oracle s env x rows err)) : MatchInsertAt ci oracle s env x ((pat, expr) :: rows) err := by
  obtain ⟨bodyIH, restIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  by_cases distinct : (patBindings pat).Nodup
  · cases matched : pmatch env.c s.refs pat x [] with
    | noMatch =>
      have target := restIH ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded, agrees, wf, safe⟩
      simpa [evaluateMatch, distinct, matched, insertOracleState] using target
    | typeError =>
      simp [evaluateMatch, distinct, matched, typeError] at run
      obtain ⟨_, rfl⟩ := run
      exact (safe rfl).elim
    | «match» bindings =>
      have target := bodyIH bindings ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded, agrees, wf, safe⟩
      simpa [evaluateMatch, distinct, matched, insertOracleState] using target
  · simp [evaluateMatch, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The value declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dlet {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (pat : Pat) (expr : AstHOL.Exp)
    (ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      ExpsInsertAt ci oracle s env [expr]) : DecsInsertAt ci oracle s env [.dlet loc pat expr] := by
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
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
        have subSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro h; apply safe; cases h; rfl
        have target := ih parts s' (.err error) ⟨subRun, recorded, agrees, wf, subSafe⟩
        simp [evaluateDecs, guard, target]
      | val values =>
        cases matched : pmatch env.c middle.refs pat (headValue values) [] with
        | typeError =>
          simp [subRun, matched, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | noMatch =>
          simp [subRun, matched] at run
          obtain ⟨rfl, rfl⟩ := run
          have target := ih parts middle (.val values) ⟨subRun, recorded, agrees, wf, by simp⟩
          simp [evaluateDecs, guard, target, matched, insertOracleState]
        | «match» bindings =>
          simp [subRun, matched] at run
          obtain ⟨rfl, rfl⟩ := run
          have target := ih parts middle (.val values) ⟨subRun, recorded, agrees, wf, by simp⟩
          simp [evaluateDecs, guard, target, matched, insertOracleState]
  · simp [evaluateDecs, guard, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
/-- The local declaration case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Dlocal {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (locals decs : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env locals = (middle, outcome) ∧
      outcome = .val inner → DecsInsertAt ci oracle middle (extendDecEnv inner env) decs) ∧
      DecsInsertAt ci oracle s env locals) : DecsInsertAt ci oracle s env [.dlocal locals decs] := by
  obtain ⟨bodyIH, localsIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluateDecs, (fixClockEvaluate s env [] locals).2] at run
  cases localRun : evaluateDecs s env locals with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [localRun] at run
      cases run
      have target := localsIH s' (.err error) ⟨localRun, recorded, agrees, wf, safe⟩
      rw [evaluateDecs, (fixClockEvaluate (insertOracleState ci oracle s) env [] locals).2, target]
    | val inner =>
      simp only [localRun] at run
      have firstRecorded := (evaluate_is_record_forward ci).2.2 s env locals middle (.val inner)
        ⟨localRun, recorded⟩
      have lastRecorded := (evaluate_is_record_forward ci).2.2 middle (extendDecEnv inner env) decs s' res
        ⟨run, firstRecorded.1⟩
      have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
      have targetLocal := localsIH middle (.val inner) ⟨localRun, recorded, agreesMiddle, wf, by simp⟩
      have targetBody := bodyIH middle (.val inner) inner ⟨localRun, rfl⟩ s' res
        ⟨run, firstRecorded.1, agrees, wf, safe⟩
      rw [evaluateDecs, (fixClockEvaluate (insertOracleState ci oracle s) env [] locals).2, targetLocal]
      exact targetBody
end Flapjack.Compiler.Backend.SourceEval.Proofs
