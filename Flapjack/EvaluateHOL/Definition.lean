import Flapjack.EvaluateHOL.Measure
import Flapjack.SemanticPrimitivesHOL.PatternMatch
import Flapjack.Misc.ListEl

/-! Clocked CakeML source evaluator. The three mutually recursive functions
follow the original expression, pattern-match and declaration clauses. Full
source and imported-carrier review is pending; floating-point evaluation
inherits the rational-cut assumption of the primitive dispatcher. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Specialize the existing HOL `HD` port to source values; this wrapper has no separate HOL declaration. -/
noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨.conv none []⟩ values

/-- Flapjack helper for the repeated source type-error result. -/
def typeError {σ α : Type} (st : State σ) : State σ × Result α Value :=
  (st, .err (.abort .typeError))

/-- Flapjack helper for the repeated source timeout result. -/
def timeoutError {σ α : Type} (st : State σ) : State σ × Result α Value :=
  (st, .err (.abort .timeoutError))

private def emptyEnv : SemEnv Value := { v := nsEmpty, c := nsEmpty }

mutual
@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_def" 54]
noncomputable def evaluate {σ : Type} (st : State σ) (env : SemEnv Value) (es : List AstHOL.Exp) :
    State σ × Result (List Value) Value :=
  match es with
  | [] => (st, .val [])
  | e1 :: e2 :: rest =>
    let first := fixClock st (evaluate st env [e1])
    match first.2 with
    | .err error => (first.1, .err error)
    | .val values =>
      let second := evaluate first.1 env (e2 :: rest)
      match second.2 with
      | .err error => (second.1, .err error)
      | .val tail => (second.1, .val (headValue values :: tail))
  | [expr] => match expr with
    | .lit lit => (st, .val [.litv lit])
    | .raise e =>
      let result := evaluate st env [e]
      match result.2 with
      | .val vs => (result.1, .err (.raise (headValue vs)))
      | .err err => (result.1, .err err)
    | .handle e clauses =>
      let result := fixClock st (evaluate st env [e])
      match result.2 with
      | .val vs => (result.1, .val vs)
      | .err (.abort err) => (result.1, .err (.abort err))
      | .err (.raise value) =>
        if canPmatchAll env.c result.1.refs (clauses.map Prod.fst) value then
          evaluateMatch result.1 env value clauses value
        else typeError result.1
    | .con name args =>
      if doConCheck env.c name args.length then
        let result := evaluate st env args.reverse
        match result.2 with
        | .err err => (result.1, .err err)
        | .val vs => match buildConv env.c name vs.reverse with
          | none => typeError result.1
          | some v => (result.1, .val [v])
      else typeError st
    | .var name => match nsLookup env.v name with
      | none => typeError st
      | some value => (st, .val [value])
    | .fn name body => (st, .val [.closure env name body])
    | .app op args =>
      let result := fixClock st (evaluate st env args.reverse)
      match result.2 with
      | .err err => (result.1, .err err)
      | .val reversed =>
        let vs := reversed.reverse
        match getOpClass op with
        | .funApp => match doOpApp vs with
          | none => typeError result.1
          | some (env', e) =>
            if result.1.clock = 0 then timeoutError result.1
            else evaluate (decClock result.1) env' [e]
        | .force => match destThunk vs result.1.refs with
          | .badRef | .notThunk => typeError result.1
          | .isThunk .evaluated v => (result.1, .val [v])
          | .isThunk .notEvaluated f => match doOpApp [f, .conv none []] with
            | none => typeError result.1
            | some (env', e) =>
              if result.1.clock = 0 then timeoutError result.1 else
              let next := evaluate (decClock result.1) env' [e]
              match next.2 with
              | .err err => (next.1, .err err)
              | .val newValues => match updateThunk vs next.1.refs newValues with
                | none => typeError next.1
                | some refs => ({ next.1 with refs }, .val newValues)
        | .evalOp =>
          let decoded := fixClock result.1 (doEvalRes vs result.1)
          match decoded.2 with
          | .err err => (decoded.1, .err err)
          | .val (evalEnv, decs) =>
            if decoded.1.clock = 0 then timeoutError decoded.1 else
            let next := fixClock (decClock decoded.1)
              (evaluateDecs (decClock decoded.1) evalEnv decs)
            match next.2 with
            | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
              | none => typeError next.1
              | some (value, evalState) =>
                ({ next.1 with evalState := resetEnvGeneration result.1.evalState evalState }, .val [value])
            | .err (.abort err) => (next.1, .err (.abort err))
            | .err err =>
              ({ next.1 with evalState := resetEnvGeneration result.1.evalState next.1.evalState }, .err err)
        | .simple => match doApp (result.1.refs, result.1.ffi) op vs with
          | none => typeError result.1
          | some ((refs, ffi), r) => ({ result.1 with refs, ffi }, listResult r)
    | .log op e1 e2 =>
      let result := fixClock st (evaluate st env [e1])
      match result.2 with
      | .err err => (result.1, .err err)
      | .val vs => match _hlog : doLog op (headValue vs) e2 with
        | none => typeError result.1
        | some (.val v) => (result.1, .val [v])
        | some (.exp e) => evaluate result.1 env [e]
    | .if_ e1 e2 e3 =>
      let result := fixClock st (evaluate st env [e1])
      match result.2 with
      | .err err => (result.1, .err err)
      | .val vs => match _hif : doIf (headValue vs) e2 e3 with
        | none => typeError result.1
        | some e => evaluate result.1 env [e]
    | .mat e clauses =>
      let result := fixClock st (evaluate st env [e])
      match result.2 with
      | .err err => (result.1, .err err)
      | .val vs =>
        if canPmatchAll env.c result.1.refs (clauses.map Prod.fst) (headValue vs) then
          evaluateMatch result.1 env (headValue vs) clauses bindExnV
        else typeError result.1
    | .let_ name e1 e2 =>
      let result := fixClock st (evaluate st env [e1])
      match result.2 with
      | .err err => (result.1, .err err)
      | .val vs => evaluate result.1 { env with v := nsOptBind name (headValue vs) env.v } [e2]
    | .letrec funs body =>
      if (funs.map (fun (name, _, _) => name)).Nodup then
        evaluate st { env with v := buildRecEnv funs env env.v } [body]
      else typeError st
    | .tannot e _ | .lannot e _ => evaluate st env [e]
termination_by (st.clock, sizeOf es)
decreasing_by
  all_goals simp_wf
  all_goals try simp_all only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, fixClock, decClock]
  all_goals try (have := expSize_pos e2)
  all_goals try (have := decSize_pos d2)
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try (have _h := doLog_selected _ _ _ _ (by assumption); subst_vars)
  all_goals try (have _h := doIf_selected _ _ _ _ (by assumption); rcases _h with _h | _h <;> subst_vars)
  all_goals try dsimp only [decoded] at *
  all_goals try dsimp only [result] at *
  all_goals try simp_all only [fixClock, Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_def" 54]
noncomputable def evaluateMatch {σ : Type} (st : State σ) (env : SemEnv Value) (value : Value)
    (clauses : List (Pat × AstHOL.Exp)) (errValue : Value) : State σ × Result (List Value) Value :=
  match clauses with
  | [] => (st, .err (.raise errValue))
  | (pat, expr) :: rest =>
    if (patBindings pat).Nodup then
      match pmatch env.c st.refs pat value [] with
      | .noMatch => evaluateMatch st env value rest errValue
      | .typeError => typeError st
      | .match bindings => evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    else typeError st
termination_by (st.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp_all only [listSize_reverse]
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := expSize_pos e2)
  all_goals try (have := decSize_pos d2)
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try (have _h := doLog_selected _ _ _ _ (by assumption); subst_vars)
  all_goals try (have _h := doIf_selected _ _ _ _ (by assumption); rcases _h with _h | _h <;> subst_vars)
  all_goals try dsimp only [decoded] at *
  all_goals try dsimp only [result] at *
  all_goals try simp_all only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_def" 54]
noncomputable def evaluateDecs {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec) :
    State σ × Result (SemEnv Value) Value :=
  match ds with
  | [] => (st, .val emptyEnv)
  | d1 :: d2 :: rest =>
    let first := fixClock st (evaluateDecs st env [d1])
    match first.2 with
    | .err err => (first.1, .err err)
    | .val newEnv =>
      let second := evaluateDecs first.1 (extendDecEnv newEnv env) (d2 :: rest)
      (second.1, combineDecResult newEnv second.2)
  | [decl] => match decl with
    | .dlet _ pat expr =>
      if (patBindings pat).Nodup && everyExp (oneConCheck env.c) expr then
        let result := evaluate st env [expr]
        match result.2 with
        | .err err => (result.1, .err err)
        | .val values => match pmatch env.c result.1.refs pat (headValue values) [] with
          | .noMatch => (result.1, .err (.raise bindExnV))
          | .typeError => typeError result.1
          | .match bindings => (result.1, .val { v := alistToNs bindings, c := nsEmpty })
      else typeError st
    | .dletrec _ funs =>
      if (funs.map (fun (name, _, _) => name)).Nodup &&
          funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr) then
        (st, .val { v := buildRecEnv funs env nsEmpty, c := nsEmpty })
      else typeError st
    | .dtype _ types =>
      if types.all checkDupCtors then
        ({ st with nextTypeStamp := st.nextTypeStamp + types.length },
          .val { v := nsEmpty, c := buildTdefs st.nextTypeStamp types })
      else typeError st
    | .dtabbrev _ _ _ _ => (st, .val emptyEnv)
    | .denv name => match declareEnv st.evalState env with
      | none => typeError st
      | some (value, evalState) => ({ st with evalState }, .val { v := nsSing name value, c := nsEmpty })
    | .dexn _ name types =>
      ({ st with nextExnStamp := st.nextExnStamp + 1 },
        .val { v := nsEmpty, c := nsSing name (types.length, .exnStamp st.nextExnStamp) })
    | .dmod name decs =>
      let result := evaluateDecs st env decs
      match result.2 with
      | .err err => (result.1, .err err)
      | .val inner => (result.1, .val { v := nsLift name inner.v, c := nsLift name inner.c })
    | .dlocal localDecs decs =>
      let first := fixClock st (evaluateDecs st env localDecs)
      match first.2 with
      | .err err => (first.1, .err err)
      | .val inner => evaluateDecs first.1 (extendDecEnv inner env) decs
termination_by (st.clock, sizeOf ds)
decreasing_by
  all_goals simp_wf
  all_goals try simp_all only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, fixClock]
  all_goals try (have := expSize_pos e2)
  all_goals try (have := decSize_pos d2)
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try (have _h := doLog_selected _ _ _ _ (by assumption); subst_vars)
  all_goals try (have _h := doIf_selected _ _ _ _ (by assumption); rcases _h with _h | _h <;> subst_vars)
  all_goals try dsimp only [decoded] at *
  all_goals try dsimp only [result] at *
  all_goals try simp_all only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega
end

end Flapjack.EvaluateHOL
