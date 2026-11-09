import Flapjack.Compiler.Backend.SourceLet.Proofs
import Flapjack.EvaluateHOL.ClockFull
import Flapjack.SemanticPrimitivesProps.RecursiveFunctions

/-! Evaluation preservation for source let-lifting. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Extending an environment with recursive value bindings preserves its
constructor namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "env_c_lemma"]
theorem envC_lemma (funs : List (VarN × VarN × AstHOL.Exp)) (env : SemEnv Value)
    (env1 : Namespace ModN VarN Value) :
    (extendDecEnv { v := buildRecEnv funs env env1, c := nsEmpty } env).c = env.c := by
  exact (nsAppend_nsEmpty env.c).2

/-- Expanding a recursive function group checks every function body. This
Flapjack helper exposes the list traversal; it has no separate HOL theorem. -/
theorem everyExp_letrec (predicate : AstHOL.Exp → Bool)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp) :
    everyExp predicate (.letrec funs body) =
      (predicate (.letrec funs body) && everyExp predicate body &&
        funs.all (fun (_, _, expr) => everyExp predicate expr)) := by
  simp [everyExp, everyExpFuns_eq_all, Bool.and_assoc]

/-- Flapjack helper stating evaluation of an anonymous let as equality of the
two evaluator results. The result-shaped HOL case is proved below. -/
theorem evaluateLiftLet_anonymous {F : Type} (state : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (first body : AstHOL.Exp)
    (safe : (EvaluateHOL.evaluateDecs state env [.dlet loc pat (.let_ none first body)]).2 ≠
      .err (.abort .typeError)) :
    EvaluateHOL.evaluateDecs state env [.dlocal [.dlet loc .pany first] [.dlet loc pat body]] =
      EvaluateHOL.evaluateDecs state env [.dlet loc pat (.let_ none first body)] := by
  have hp : (patBindings pat).Nodup := by
    by_cases h : (patBindings pat).Nodup
    · exact h
    · simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hf : everyExp (oneConCheck env.c) first = true := by
    cases h : everyExp (oneConCheck env.c) first with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hb : everyExp (oneConCheck env.c) body = true := by
    cases h : everyExp (oneConCheck env.c) body with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have localEq : EvaluateHOL.evaluateDecs state env [.dlocal [.dlet loc .pany first] [.dlet loc pat body]] =
      (let result := EvaluateHOL.evaluateDecs state env [.dlet loc .pany first]
       match result.2 with
       | .err err => (result.1, .err err)
       | .val inner => EvaluateHOL.evaluateDecs result.1 (extendDecEnv inner env) [.dlet loc pat body]) := by
    conv =>
      lhs
      rw [EvaluateHOL.evaluateDecs, (EvaluateHOL.fixClockEvaluate state env [] [.dlet loc .pany first]).2]
    rfl
  rw [localEq]
  simp only [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, Bool.true_and, hp, decide_true,
    hf, hb, Bool.and_self, ↓reduceIte, patBindings, List.nodup_nil, pmatch]
  conv =>
    rhs
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate state env [first] []).1]
  cases run : EvaluateHOL.evaluate state env [first] with
  | mk next result =>
    cases result with
    | err error => simp
    | val values =>
      cases env with
      | mk variables constructors =>
        cases variables
        cases constructors
        simp_all [nsOptBind, extendDecEnv, alistToNs, nsAppend, nsEmpty]

/-- Flapjack equality helper for named lets, including shadowing of an
existing binding. The result-shaped HOL case is proved below. -/
theorem evaluateLiftLet_named {F : Type} (state : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (name : VarN) (first body : AstHOL.Exp)
    (safe : (EvaluateHOL.evaluateDecs state env [.dlet loc pat (.let_ (some name) first body)]).2 ≠
      .err (.abort .typeError)) :
    EvaluateHOL.evaluateDecs state env [.dlocal [.dlet loc (.pvar name) first] [.dlet loc pat body]] =
      EvaluateHOL.evaluateDecs state env [.dlet loc pat (.let_ (some name) first body)] := by
  have hp : (patBindings pat).Nodup := by
    by_cases h : (patBindings pat).Nodup
    · exact h
    · simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hf : everyExp (oneConCheck env.c) first = true := by
    cases h : everyExp (oneConCheck env.c) first with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hb : everyExp (oneConCheck env.c) body = true := by
    cases h : everyExp (oneConCheck env.c) body with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, h, EvaluateHOL.typeError] at safe
  have localEq : EvaluateHOL.evaluateDecs state env [.dlocal [.dlet loc (.pvar name) first] [.dlet loc pat body]] =
      (let result := EvaluateHOL.evaluateDecs state env [.dlet loc (.pvar name) first]
       match result.2 with
       | .err err => (result.1, .err err)
       | .val inner => EvaluateHOL.evaluateDecs result.1 (extendDecEnv inner env) [.dlet loc pat body]) := by
    conv =>
      lhs
      rw [EvaluateHOL.evaluateDecs, (EvaluateHOL.fixClockEvaluate state env [] [.dlet loc (.pvar name) first]).2]
    rfl
  rw [localEq]
  simp only [EvaluateHOL.evaluateDecs, everyExp, oneConCheck, Bool.true_and, hp, decide_true,
    hf, hb, Bool.and_self, ↓reduceIte, patBindings, List.nodup_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, pmatch]
  conv =>
    rhs
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate state env [first] []).1]
  cases run : EvaluateHOL.evaluate state env [first] with
  | mk next result =>
    cases result with
    | err error => simp
    | val values =>
      cases env with
      | mk variables constructors =>
        cases variables
        cases constructors
        simp_all [nsOptBind, nsBind, extendDecEnv, alistToNs, nsAppend, nsEmpty]

/-- Flapjack equality helper for lifting recursive bindings. The result-shaped
HOL case is proved below. -/
theorem evaluateLiftLet_letrec {F : Type} (state : State F) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (pat : Pat)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (safe : (EvaluateHOL.evaluateDecs state env [.dlet loc pat (.letrec funs body)]).2 ≠
      .err (.abort .typeError)) :
    EvaluateHOL.evaluateDecs state env [.dlocal [.dletrec loc funs] [.dlet loc pat body]] =
      EvaluateHOL.evaluateDecs state env [.dlet loc pat (.letrec funs body)] := by
  have hp : (patBindings pat).Nodup := by
    by_cases h : (patBindings pat).Nodup
    · exact h
    · simp [EvaluateHOL.evaluateDecs, everyExp_letrec, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hb : everyExp (oneConCheck env.c) body = true := by
    cases h : everyExp (oneConCheck env.c) body with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp_letrec, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hf : funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr) = true := by
    cases h : funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr) with
    | true => rfl
    | false => simp [EvaluateHOL.evaluateDecs, everyExp_letrec, oneConCheck, h, EvaluateHOL.typeError] at safe
  have hn : (funs.map (fun (name, _, _) => name)).Nodup := by
    by_cases h : (funs.map (fun (name, _, _) => name)).Nodup
    · exact h
    · simp [EvaluateHOL.evaluateDecs, everyExp_letrec, oneConCheck, hp, hb, hf,
        EvaluateHOL.evaluate, h, EvaluateHOL.typeError] at safe
  have localEq : EvaluateHOL.evaluateDecs state env [.dlocal [.dletrec loc funs] [.dlet loc pat body]] =
      (let result := EvaluateHOL.evaluateDecs state env [.dletrec loc funs]
       match result.2 with
       | .err err => (result.1, .err err)
       | .val inner => EvaluateHOL.evaluateDecs result.1 (extendDecEnv inner env) [.dlet loc pat body]) := by
    conv =>
      lhs
      rw [EvaluateHOL.evaluateDecs, (EvaluateHOL.fixClockEvaluate state env [] [.dletrec loc funs]).2]
    rfl
  rw [localEq]
  simp only [EvaluateHOL.evaluateDecs, everyExp_letrec, oneConCheck, Bool.true_and,
    hp, hn, hb, hf, decide_true, Bool.and_self, ↓reduceIte]
  conv =>
    rhs
    rw [EvaluateHOL.evaluate]
  simp only [hn, ↓reduceIte]
  have envEq : extendDecEnv { v := buildRecEnv funs env nsEmpty, c := nsEmpty } env =
      { env with v := buildRecEnv funs env env.v } := by
    unfold extendDecEnv
    simp only [Flapjack.SemanticPrimitivesProps.buildRecEnv_merge funs (), (nsAppend_nsEmpty _).1]
    cases env with
    | mk variables constructors =>
      cases constructors
      rfl
  rw [envEq]
  simp [hb]

/-- A successful single let-lifting step preserves the original declaration
evaluation whenever that evaluation does not produce a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "evaluate_lift_let"]
theorem evaluate_lift_let {F : Type} (state : State F) (env : SemEnv Value) (d : Dec)
    (next : State F) (result : Result (SemEnv Value) Value) (d1 d2 : Dec)
    (premises : EvaluateHOL.evaluateDecs state env [d] = (next, result) ∧
      result ≠ .err (.abort .typeError) ∧ liftLet d = some (d1, d2)) :
    EvaluateHOL.evaluateDecs state env [.dlocal [d1] [d2]] = (next, result) := by
  obtain ⟨source, safe, lifted⟩ := premises
  have safe' : (EvaluateHOL.evaluateDecs state env [d]).2 ≠ .err (.abort .typeError) := by
    rw [source]
    exact safe
  cases d with
  | dlet loc pat expr =>
    cases expr with
    | let_ name first body =>
      cases name with
      | none =>
        simp only [liftLet, Option.some.injEq, Prod.mk.injEq] at lifted
        obtain ⟨rfl, rfl⟩ := lifted
        rw [evaluateLiftLet_anonymous state env loc pat first body safe', source]
      | some name =>
        simp only [liftLet, Option.some.injEq, Prod.mk.injEq] at lifted
        obtain ⟨rfl, rfl⟩ := lifted
        rw [evaluateLiftLet_named state env loc pat name first body safe', source]
    | letrec funs body =>
      simp only [liftLet, Option.some.injEq, Prod.mk.injEq] at lifted
      obtain ⟨rfl, rfl⟩ := lifted
      rw [evaluateLiftLet_letrec state env loc pat funs body safe', source]
    | _ => simp [liftLet] at lifted
  | _ => simp [liftLet] at lifted

end Flapjack.Compiler.Backend.SourceLet
