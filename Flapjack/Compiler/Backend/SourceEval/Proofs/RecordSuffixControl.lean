import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffixBase

/-! Control cases of the source evaluator recording-oracle clock suffix theorem. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The recursive-binding case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Letrec {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : (funs.map fun (name, _, _) => name).Nodup →
      ExpsSuffixAt ci k s { env with v := buildRecEnv funs env env.v } [body]) :
    ExpsSuffixAt ci k s env [.letrec funs body] := by
  intro s' res ⟨run, recorded, bound⟩
  by_cases distinct : (funs.map fun (name, _, _) => name).Nodup
  · have suffix := ih distinct s' res ⟨by simpa [evaluate, distinct] using run, recorded, bound⟩
    simpa [evaluate, distinct] using suffix
  · simp [evaluate, distinct, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluate, distinct, typeError]⟩

/-- The nonempty pattern-match case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_MatchCons {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp)) (err : Value)
    (ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      ExpsSuffixAt ci k s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        MatchSuffixAt ci k s env x rows err)) : MatchSuffixAt ci k s env x ((pat, expr) :: rows) err := by
  obtain ⟨bodyIH, restIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  by_cases distinct : (patBindings pat).Nodup
  · cases matched : pmatch env.c s.refs pat x [] with
    | noMatch =>
      have suffix := restIH ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded, bound⟩
      simpa [evaluateMatch, distinct, matched] using suffix
    | typeError =>
      simp [evaluateMatch, distinct, matched, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      exact Or.inl ⟨bound, by simp [evaluateMatch, distinct, matched, typeError]⟩
    | «match» bindings =>
      have suffix := bodyIH bindings ⟨distinct, matched⟩ s' res
        ⟨by simpa [evaluateMatch, distinct, matched] using run, recorded, bound⟩
      simpa [evaluateMatch, distinct, matched] using suffix
  · simp [evaluateMatch, distinct, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluateMatch, distinct, typeError]⟩

/-- The module-declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dmod {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (ih : DecsSuffixAt ci k s env decs) : DecsSuffixAt ci k s env [.dmod name decs] := by
  intro s' res ⟨run, recorded, bound⟩
  cases innerRun : evaluateDecs s env decs with
  | mk middle result =>
    have suffix := ih middle result ⟨innerRun, recorded, bound⟩
    cases result <;> simp [evaluateDecs, innerRun] at run <;> obtain ⟨rfl, rfl⟩ := run
    all_goals
      rcases suffix with ⟨bound', eq⟩ | ⟨short, eq, forward⟩
      · left
        refine ⟨bound', ?_⟩
        simp [evaluateDecs, eq]
      · right
        refine ⟨short, ?_, forward⟩
        simp [evaluateDecs, eq]
/-- The local-declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dlocal {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (locals decs : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env locals = (middle, outcome) ∧
      outcome = .val inner → DecsSuffixAt ci k middle (extendDecEnv inner env) decs) ∧
      DecsSuffixAt ci k s env locals) : DecsSuffixAt ci k s env [.dlocal locals decs] := by
  obtain ⟨bodyIH, localsIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluateDecs, (fixClockEvaluate s env [] locals).2] at run
  cases localRun : evaluateDecs s env locals with
  | mk middle result =>
    have firstSuffix := localsIH middle result ⟨localRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).2.2 s env locals middle result ⟨localRun, recorded⟩
    cases result with
    | err error =>
      simp only [localRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, equal]
    | val inner =>
      simp only [localRun] at run
      have lastRecorded := (evaluate_is_record_forward ci).2.2 middle (extendDecEnv inner env) decs s' res
        ⟨run, firstRecorded.1⟩
      rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
      · have suffix := bodyIH middle (.val inner) inner ⟨localRun, rfl⟩ s' res ⟨run, firstRecorded.1, midBound⟩
        rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, firstEqual]
          exact equal
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, firstEqual]
          exact equal
      · right
        refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
        rw [evaluateDecs, (fixClockEvaluate _ _ [] locals).2, firstEqual]
/-- The let-expression case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Let {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : Option VarN) (bound body : AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      ExpsSuffixAt ci k middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      ExpsSuffixAt ci k s env [bound]) : ExpsSuffixAt ci k s env [.let_ name bound body] := by
  obtain ⟨bodyIH, boundIH⟩ := ih
  intro s' res ⟨run, recorded, clockBound⟩
  rw [evaluate, (fixClockEvaluate s env [bound] []).1] at run
  cases boundRun : evaluate s env [bound] with
  | mk middle result =>
    have firstSuffix := boundIH middle result ⟨boundRun, recorded, clockBound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [bound] middle result ⟨boundRun, recorded⟩
    cases result with
    | err error =>
      simp only [boundRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, equal]
    | val values =>
      simp only [boundRun] at run
      have lastRecorded := (evaluate_is_record_forward ci).1 middle
        { env with v := nsOptBind name (headValue values) env.v } [body] s' res ⟨run, firstRecorded.1⟩
      rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
      · have suffix := bodyIH middle (.val values) values ⟨boundRun, rfl⟩ s' res ⟨run, firstRecorded.1, midBound⟩
        rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, firstEqual]
          exact equal
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, firstEqual]
          exact equal
      · right
        refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
        rw [evaluate, (fixClockEvaluate _ _ [bound] []).1, firstEqual]
/-- The raise-expression case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Raise {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (ih : ExpsSuffixAt ci k s env [expr]) : ExpsSuffixAt ci k s env [.raise expr] := by
  intro s' res ⟨run, recorded, bound⟩
  cases subRun : evaluate s env [expr] with
  | mk middle result =>
    have suffix := ih middle result ⟨subRun, recorded, bound⟩
    cases result <;> simp [evaluate, subRun] at run <;> obtain ⟨rfl, rfl⟩ := run
    all_goals
      rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        simp [evaluate, equal]
      · right
        refine ⟨short, ?_, forward⟩
        simp [evaluate, equal]
/-- The constructor-expression case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Con {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : doConCheck env.c name args.length = true → ExpsSuffixAt ci k s env args.reverse) :
    ExpsSuffixAt ci k s env [.con name args] := by
  intro s' res ⟨run, recorded, bound⟩
  by_cases check : doConCheck env.c name args.length = true
  · rw [evaluate] at run
    simp only [check, ↓reduceIte] at run
    cases subRun : evaluate s env args.reverse with
    | mk middle result =>
      have suffix := ih check middle result ⟨subRun, recorded, bound⟩
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          simp [evaluate, check, equal]
        · right
          refine ⟨short, ?_, forward⟩
          simp [evaluate, check, equal]
      | val values =>
        cases built : buildConv env.c name values.reverse <;>
          simp [subRun, built, typeError] at run <;> obtain ⟨rfl, rfl⟩ := run
        all_goals
          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            simp [evaluate, check, equal, built, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            simp [evaluate, check, equal]
  · simp [evaluate, check, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluate, check, typeError]⟩
/-- The value-declaration case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Dlet {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      ExpsSuffixAt ci k s env [expr]) : DecsSuffixAt ci k s env [.dlet loc pat expr] := by
  intro s' res ⟨run, recorded, bound⟩
  by_cases guard : (decide (patBindings pat).Nodup && everyExp (oneConCheck env.c) expr) = true
  · have parts : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true := by simpa using guard
    rw [evaluateDecs] at run
    simp only [guard, ↓reduceIte] at run
    cases subRun : evaluate s env [expr] with
    | mk middle result =>
      have suffix := ih parts middle result ⟨subRun, recorded, bound⟩
      cases result with
      | err error =>
        simp only [subRun] at run
        cases run
        rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          simp [evaluateDecs, guard, equal]
        · right
          refine ⟨short, ?_, forward⟩
          simp [evaluateDecs, guard, equal]
      | val values =>
        cases matched : pmatch env.c middle.refs pat (headValue values) [] <;>
          simp [subRun, matched, typeError] at run <;> obtain ⟨rfl, rfl⟩ := run
        all_goals
          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            simp [evaluateDecs, guard, equal, matched, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            simp [evaluateDecs, guard, equal]
  · simp [evaluateDecs, guard, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl ⟨bound, by simp [evaluateDecs, guard, typeError]⟩
/-- The conditional-expression case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_If {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (cond yes no : AstHOL.Exp)
    (ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      ExpsSuffixAt ci k middle env [branch]) ∧ ExpsSuffixAt ci k s env [cond]) :
    ExpsSuffixAt ci k s env [.if_ cond yes no] := by
  obtain ⟨branchIH, condIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluate, (fixClockEvaluate s env [cond] []).1] at run
  cases condRun : evaluate s env [cond] with
  | mk middle result =>
    have firstSuffix := condIH middle result ⟨condRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [cond] middle result ⟨condRun, recorded⟩
    cases result with
    | err error =>
      simp only [condRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, equal]
    | val values =>
      simp only [condRun] at run
      split at run
      next chosen =>
        simp [typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, equal]
          dsimp only
          split <;> simp_all [typeError]
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, equal]
      next branch chosen =>
        have lastRecorded := (evaluate_is_record_forward ci).1 middle env [branch] s' res ⟨run, firstRecorded.1⟩
        rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
        · have suffix := branchIH middle (.val values) values branch ⟨condRun, rfl, chosen⟩ s' res
            ⟨run, firstRecorded.1, midBound⟩
          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, firstEqual]
            dsimp only
            split <;> simp_all
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, firstEqual]
            dsimp only
            split <;> simp_all
        · right
          refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
          rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, firstEqual]
/-- The match-expression case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Mat {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
      MatchSuffixAt ci k middle env (headValue values) rows bindExnV) ∧ ExpsSuffixAt ci k s env [expr]) :
    ExpsSuffixAt ci k s env [.mat expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    have firstSuffix := exprIH middle result ⟨exprRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [expr] middle result ⟨exprRun, recorded⟩
    cases result with
    | err error =>
      simp only [exprRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
    | val values =>
      simp only [exprRun] at run
      by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true
      · simp only [check, ↓reduceIte] at run
        have lastRecorded := (evaluate_is_record_forward ci).2.1 middle env (headValue values) rows bindExnV s' res
          ⟨run, firstRecorded.1⟩
        rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
        · have suffix := matchIH middle (.val values) values ⟨exprRun, rfl, check⟩ s' res
            ⟨run, firstRecorded.1, midBound⟩
          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
            simpa [check] using equal
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
            simpa [check] using equal
        · right
          refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
      · simp [check, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
          simp [check, typeError]
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
/-- The exception-handler case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Handle {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .err err ∧ err = .raise value ∧
      canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
      MatchSuffixAt ci k middle env value rows value) ∧ ExpsSuffixAt ci k s env [expr]) :
    ExpsSuffixAt ci k s env [.handle expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    have firstSuffix := exprIH middle result ⟨exprRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [expr] middle result ⟨exprRun, recorded⟩
    cases result with
    | val values =>
      simp only [exprRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
    | err error =>
      cases error with
      | abort error =>
        simp only [exprRun] at run
        cases run
        rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
      | raise value =>
        simp only [exprRun] at run
        by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true
        · simp only [check, ↓reduceIte] at run
          have lastRecorded := (evaluate_is_record_forward ci).2.1 middle env value rows value s' res
            ⟨run, firstRecorded.1⟩
          rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
          · have suffix := matchIH middle (.err (.raise value)) (.raise value) value
              ⟨exprRun, rfl, rfl, check⟩ s' res ⟨run, firstRecorded.1, midBound⟩
            rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
            · left
              refine ⟨bound', ?_⟩
              rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
              simpa [check] using equal
            · right
              refine ⟨short, ?_, forward⟩
              rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
              simpa [check] using equal
          · right
            refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
            rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, firstEqual]
        · simp [check, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
            simp [check, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, equal]
end Flapjack.Compiler.Backend.SourceEval.Proofs
