module

public import Flapjack.EvaluateHOL.ClockFull
public import Flapjack.HolRef

@[expose] public section

/-! The shared induction principle for source evaluation. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

private structure FullEvaluateCases {F : Type}
    (P0 : State F → SemEnv Value → List AstHOL.Exp → Prop)
    (P1 : State F → SemEnv Value → Value → List (Pat × AstHOL.Exp) → Value → Prop)
    (P2 : State F → SemEnv Value → List Dec → Prop) : Prop where
  ExpsNil : ∀ (s : State F) (env : SemEnv Value), P0 s env []
  ExpsCons : ∀ (s : State F) (env : SemEnv Value) (first second : Flapjack.AstHOL.Exp) (rest : List Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → P0 middle env (second :: rest)) ∧
      P0 s env [first]), P0 s env (first :: second :: rest)
  Lit : ∀ (s : State F) (env : SemEnv Value) (lit : Lit), P0 s env [.lit lit]
  Raise : ∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (_ih : P0 s env [expr]), P0 s env [.raise expr]
  Handle : ∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (_ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .err err ∧ err = .raise value ∧
       canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
       P1 middle env value rows value) ∧ P0 s env [expr]), P0 s env [.handle expr rows]
  Con : ∀ (s : State F) (env : SemEnv Value) (name : Option (Ident ModN ConN))
    (args : List Flapjack.AstHOL.Exp)
    (_ih : doConCheck env.c name args.length = true → P0 s env args.reverse), P0 s env [.con name args]
  Var : ∀ (s : State F) (env : SemEnv Value) (name : Flapjack.NamespaceHOL.Ident ModN VarN), P0 s env [.var name]
  Fn : ∀ (s : State F) (env : SemEnv Value) (name : VarN) (body : Flapjack.AstHOL.Exp), P0 s env [.fn name body]
  App : ∀ (s : State F) (env : SemEnv Value) (op : Op) (args : List Flapjack.AstHOL.Exp)
    (_ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × Flapjack.AstHOL.Exp) (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → P0 (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        P2 (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × Flapjack.AstHOL.Exp)
          (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → P0 (decClock middle) callEnv [body]) ∧
      P0 s env args.reverse), P0 s env [.app op args]
  Log : ∀ (s : State F) (env : SemEnv Value) (op : Lop) (first second : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      P0 middle env [branch]) ∧ P0 s env [first]), P0 s env [.log op first second]
  If : ∀ (s : State F) (env : SemEnv Value) (cond yes no : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      P0 middle env [branch]) ∧ P0 s env [cond]), P0 s env [.if_ cond yes no]
  Mat : ∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (_ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
       P1 middle env (headValue values) rows bindExnV) ∧ P0 s env [expr]), P0 s env [.mat expr rows]
  Let : ∀ (s : State F) (env : SemEnv Value) (name : Option VarN)
    (bound body : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      P0 middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      P0 s env [bound]), P0 s env [.let_ name bound body]
  Letrec : ∀ (s : State F) (env : SemEnv Value) (funs : List (VarN × VarN × Flapjack.AstHOL.Exp))
    (body : Flapjack.AstHOL.Exp)
    (_ih : (funs.map fun (name, _, _) => name).Nodup →
      P0 s { env with v := buildRecEnv funs env env.v } [body]), P0 s env [.letrec funs body]
  Tannot : ∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (typ : AstT)
    (_ih : P0 s env [expr]), P0 s env [.tannot expr typ]
  Lannot : ∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (_ih : P0 s env [expr]), P0 s env [.lannot expr loc]
  MatchNil : ∀ (s : State F) (env : SemEnv Value) (x err : Value), P1 s env x [] err
  MatchCons : ∀ (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp)) (err : Value)
    (_ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      P0 s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        P1 s env x rows err)), P1 s env x ((pat, expr) :: rows) err
  DecsNil : ∀ (s : State F) (env : SemEnv Value), P2 s env []
  DecsCons : ∀ (s : State F) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (_ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → P2 middle (extendDecEnv inner env) (second :: rest)) ∧
      P2 s env [first]), P2 s env (first :: second :: rest)
  Dlet : ∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (_ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      P0 s env [expr]), P2 s env [.dlet loc pat expr]
  Dletrec : ∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × Flapjack.AstHOL.Exp)), P2 s env [.dletrec loc funs]
  Dtype : ∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (types : TypeDef), P2 s env [.dtype loc types]
  Dtabbrev : ∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT), P2 s env [.dtabbrev loc vars name typ]
  Denv : ∀ (s : State F)
    (env : SemEnv Value) (name : VarN), P2 s env [.denv name]
  Dexn : ∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT), P2 s env [.dexn loc name types]
  Dmod : ∀ (s : State F)
    (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (_ih : P2 s env decs), P2 s env [.dmod name decs]
  Dlocal : ∀ (s : State F)
    (env : SemEnv Value) (localDecs decs : List Dec)
    (_ih : (∀ middle outcome inner, evaluateDecs s env localDecs = (middle, outcome) ∧
      outcome = .val inner → P2 middle (extendDecEnv inner env) decs) ∧
      P2 s env localDecs), P2 s env [.dlocal localDecs decs]

mutual
private theorem goExp {F : Type} {P0 : State F → SemEnv Value → List AstHOL.Exp → Prop} {P1 : State F → SemEnv Value → Value → List (Pat × AstHOL.Exp) → Value → Prop} {P2 : State F → SemEnv Value → List Dec → Prop} (H : FullEvaluateCases P0 P1 P2)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    P0 state env exprs := by
  cases exprs with
  | nil => exact H.ExpsNil state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply H.ExpsCons state env first second tail
      refine ⟨?_, goExp H state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact goExp H middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact H.Lit state env lit
      | var name => exact H.Var state env name
      | fn name body => exact H.Fn state env name body
      | raise expr => exact H.Raise state env expr (goExp H state env [expr])
      | tannot expr typ => exact H.Tannot state env expr typ (goExp H state env [expr])
      | lannot expr loc => exact H.Lannot state env expr loc (goExp H state env [expr])
      | con name args =>
        apply H.Con state env name args
        intro _
        exact goExp H state env args.reverse
      | letrec funs body =>
        apply H.Letrec state env funs body
        intro _
        exact goExp H state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply H.Let state env name bound body
        refine ⟨?_, goExp H state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact goExp H middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply H.If state env condition yes no
        refine ⟨?_, goExp H state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact goExp H middle env [yes]
        · subst branch; exact goExp H middle env [no]
      | log op first second =>
        apply H.Log state env op first second
        refine ⟨?_, goExp H state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact goExp H middle env [second]
      | mat expr clauses =>
        apply H.Mat state env expr clauses
        refine ⟨?_, goExp H state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact goMatch H middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply H.Handle state env expr clauses
        refine ⟨?_, goExp H state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact goMatch H middle env value clauses value
      | app op args =>
        apply H.App state env op args
        refine ⟨?_, ?_, ?_, goExp H state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact goExp H (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact goDec H (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact goExp H (decClock middle) callEnv [body]
termination_by (state.clock, sizeOf exprs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, decClock]
  all_goals try (have := expSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try dsimp only [decClock] at *
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

private theorem goMatch {F : Type} {P0 : State F → SemEnv Value → List AstHOL.Exp → Prop} {P1 : State F → SemEnv Value → Value → List (Pat × AstHOL.Exp) → Value → Prop} {P2 : State F → SemEnv Value → List Dec → Prop} (H : FullEvaluateCases P0 P1 P2)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    P1 state env value clauses err := by
  cases clauses with
  | nil => exact H.MatchNil state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply H.MatchCons state env value pat expr rest err
    constructor
    · intro bindings _
      exact goExp H state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact goMatch H state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

private theorem goDec {F : Type} {P0 : State F → SemEnv Value → List AstHOL.Exp → Prop} {P1 : State F → SemEnv Value → Value → List (Pat × AstHOL.Exp) → Value → Prop} {P2 : State F → SemEnv Value → List Dec → Prop} (H : FullEvaluateCases P0 P1 P2)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : P2 state env decs := by
  cases decs with
  | nil => exact H.DecsNil state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply H.DecsCons state env first second tail
      refine ⟨?_, goDec H state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact goDec H middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact H.Dtabbrev state env loc vars name typ
      | dexn loc name types => exact H.Dexn state env loc name types
      | dtype loc types => exact H.Dtype state env loc types
      | denv name => exact H.Denv state env name
      | dletrec loc funs => exact H.Dletrec state env loc funs
      | dmod name ds => exact H.Dmod state env name ds (goDec H state env ds)
      | dlet loc pat expr =>
        apply H.Dlet state env loc pat expr
        intro _
        exact goExp H state env [expr]
      | dlocal locals body =>
        apply H.Dlocal state env locals body
        refine ⟨?_, goDec H state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact goDec H middle (extendDecEnv inner env) body
termination_by (state.clock, sizeOf decs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := decSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try (have := patSize_pos pat)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega
end

/-- Mutual induction over expressions, match rows, and declarations. -/
@[hol "cakeml/semantics/evaluateScript.sml" "full_evaluate_ind"]
theorem fullEvaluateInd {F : Type}
    (P0 : State F → SemEnv Value → List AstHOL.Exp → Prop)
    (P1 : State F → SemEnv Value → Value → List (Pat × AstHOL.Exp) → Value → Prop)
    (P2 : State F → SemEnv Value → List Dec → Prop) :
    (∀ (s : State F) (env : SemEnv Value), P0 s env []) ∧
    (∀ (s : State F) (env : SemEnv Value) (first second : Flapjack.AstHOL.Exp) (rest : List Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → P0 middle env (second :: rest)) ∧
      P0 s env [first]), P0 s env (first :: second :: rest)) ∧
    (∀ (s : State F) (env : SemEnv Value) (lit : Lit), P0 s env [.lit lit]) ∧
    (∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (_ih : P0 s env [expr]), P0 s env [.raise expr]) ∧
    (∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (_ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .err err ∧ err = .raise value ∧
       canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
       P1 middle env value rows value) ∧ P0 s env [expr]), P0 s env [.handle expr rows]) ∧
    (∀ (s : State F) (env : SemEnv Value) (name : Option (Ident ModN ConN))
    (args : List Flapjack.AstHOL.Exp)
    (_ih : doConCheck env.c name args.length = true → P0 s env args.reverse), P0 s env [.con name args]) ∧
    (∀ (s : State F) (env : SemEnv Value) (name : Flapjack.NamespaceHOL.Ident ModN VarN), P0 s env [.var name]) ∧
    (∀ (s : State F) (env : SemEnv Value) (name : VarN) (body : Flapjack.AstHOL.Exp), P0 s env [.fn name body]) ∧
    (∀ (s : State F) (env : SemEnv Value) (op : Op) (args : List Flapjack.AstHOL.Exp)
    (_ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × Flapjack.AstHOL.Exp) (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → P0 (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        P2 (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × Flapjack.AstHOL.Exp)
          (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → P0 (decClock middle) callEnv [body]) ∧
      P0 s env args.reverse), P0 s env [.app op args]) ∧
    (∀ (s : State F) (env : SemEnv Value) (op : Lop) (first second : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      P0 middle env [branch]) ∧ P0 s env [first]), P0 s env [.log op first second]) ∧
    (∀ (s : State F) (env : SemEnv Value) (cond yes no : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      P0 middle env [branch]) ∧ P0 s env [cond]), P0 s env [.if_ cond yes no]) ∧
    (∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (_ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
       P1 middle env (headValue values) rows bindExnV) ∧ P0 s env [expr]), P0 s env [.mat expr rows]) ∧
    (∀ (s : State F) (env : SemEnv Value) (name : Option VarN)
    (bound body : Flapjack.AstHOL.Exp)
    (_ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      P0 middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      P0 s env [bound]), P0 s env [.let_ name bound body]) ∧
    (∀ (s : State F) (env : SemEnv Value) (funs : List (VarN × VarN × Flapjack.AstHOL.Exp))
    (body : Flapjack.AstHOL.Exp)
    (_ih : (funs.map fun (name, _, _) => name).Nodup →
      P0 s { env with v := buildRecEnv funs env env.v } [body]), P0 s env [.letrec funs body]) ∧
    (∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (typ : AstT)
    (_ih : P0 s env [expr]), P0 s env [.tannot expr typ]) ∧
    (∀ (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (_ih : P0 s env [expr]), P0 s env [.lannot expr loc]) ∧
    (∀ (s : State F) (env : SemEnv Value) (x err : Value), P1 s env x [] err) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp)) (err : Value)
    (_ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      P0 s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        P1 s env x rows err)), P1 s env x ((pat, expr) :: rows) err) ∧
    (∀ (s : State F) (env : SemEnv Value), P2 s env []) ∧
    (∀ (s : State F) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (_ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → P2 middle (extendDecEnv inner env) (second :: rest)) ∧
      P2 s env [first]), P2 s env (first :: second :: rest)) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (_ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      P0 s env [expr]), P2 s env [.dlet loc pat expr]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × Flapjack.AstHOL.Exp)), P2 s env [.dletrec loc funs]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (types : TypeDef), P2 s env [.dtype loc types]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT), P2 s env [.dtabbrev loc vars name typ]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (name : VarN), P2 s env [.denv name]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT), P2 s env [.dexn loc name types]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (_ih : P2 s env decs), P2 s env [.dmod name decs]) ∧
    (∀ (s : State F)
    (env : SemEnv Value) (localDecs decs : List Dec)
    (_ih : (∀ middle outcome inner, evaluateDecs s env localDecs = (middle, outcome) ∧
      outcome = .val inner → P2 middle (extendDecEnv inner env) decs) ∧
      P2 s env localDecs), P2 s env [.dlocal localDecs decs]) →
    (∀ s env es, P0 s env es) ∧
    (∀ s env v rows err, P1 s env v rows err) ∧
    (∀ s env ds, P2 s env ds) := by
  rintro ⟨hExpsNil, hExpsCons, hLit, hRaise, hHandle, hCon, hVar, hFn, hApp, hLog, hIf, hMat, hLet, hLetrec, hTannot, hLannot, hMatchNil, hMatchCons, hDecsNil, hDecsCons, hDlet, hDletrec, hDtype, hDtabbrev, hDenv, hDexn, hDmod, hDlocal⟩
  let H : FullEvaluateCases P0 P1 P2 := ⟨hExpsNil, hExpsCons, hLit, hRaise, hHandle, hCon, hVar, hFn, hApp, hLog, hIf, hMat, hLet, hLetrec, hTannot, hLannot, hMatchNil, hMatchCons, hDecsNil, hDecsCons, hDlet, hDletrec, hDtype, hDtabbrev, hDenv, hDexn, hDmod, hDlocal⟩
  exact ⟨goExp H, goMatch H, goDec H⟩

end Flapjack.EvaluateHOL
