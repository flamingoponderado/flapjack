import Flapjack.EvaluateHOL.Definition

/-! Cases of the original source evaluator clock theorem. The assembling
clock theorem remains open; these are individual constructor cases. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Flapjack helper used to remove a clock clamp after the corresponding
recursive clock hypothesis has established its bound. -/
private theorem fixClock_eq_of_bound {σ τ α : Type} (st : State σ) (output : State τ × α)
    (bound : output.1.clock ≤ st.clock) : fixClock st output = output := by
  cases output with
  | mk next value =>
    cases next
    simp_all [fixClock, Nat.min_eq_left]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (result : Result (List Value) Value) (h : evaluate st env [] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_lit {σ : Type} (st st' : State σ) (env : SemEnv Value) (lit : Lit)
    (result : Result (List Value) Value) (h : evaluate st env [.lit lit] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_fun {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : VarN) (body : Flapjack.AstHOL.Exp) (result : Result (List Value) Value)
    (h : evaluate st env [.fn name body] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_var {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : Ident ModN VarN) (result : Result (List Value) Value)
    (h : evaluate st env [.var name] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  split at hs <;> simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateMatchClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (value errorValue : Value) (result : Result (List Value) Value)
    (h : evaluateMatch st env value [] errorValue = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateMatch] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (result : Result (SemEnv Value) Value) (h : evaluateDecs st env [] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_tabbrev {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT)
    (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.dtabbrev loc vars name typ] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_raise {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.raise expr] = (st', result)) : st'.clock ≤ st.clock := by
  have bound := ih (evaluate st env [expr]).1 (evaluate st env [expr]).2 (by
    cases evaluate st env [expr]
    rfl)
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  cases hv : (evaluate st env [expr]).2 <;> simp_all

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_tannot {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (typ : AstT) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.tannot expr typ] = (st', result)) : st'.clock ≤ st.clock := by
  simp only [evaluate] at h
  exact ih st' result h

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_lannot {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.lannot expr loc] = (st', result)) : st'.clock ≤ st.clock := by
  simp only [evaluate] at h
  exact ih st' result h

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_con {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : Option (Ident ModN ConN)) (args : List Flapjack.AstHOL.Exp)
    (result : Result (List Value) Value)
    (ih : doConCheck env.c name args.length = true → ∀ next outcome,
      evaluate st env args.reverse = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.con name args] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  split at hs
  · rename_i valid
    have bound := ih valid (evaluate st env args.reverse).1 (evaluate st env args.reverse).2 (by
      cases evaluate st env args.reverse
      rfl)
    cases hv : (evaluate st env args.reverse).2 with
    | err err => simp_all
    | val vs =>
      cases hc : buildConv env.c name vs.reverse <;> simp_all [typeError]
  · simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_mod {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : ModN) (decs : List Dec) (result : Result (SemEnv Value) Value)
    (ih : ∀ next outcome, evaluateDecs st env decs = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluateDecs st env [.dmod name decs] = (st', result)) : st'.clock ≤ st.clock := by
  have bound := ih (evaluateDecs st env decs).1 (evaluateDecs st env decs).2 (by
    cases evaluateDecs st env decs
    rfl)
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  cases hv : (evaluateDecs st env decs).2 <;> simp_all

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_let {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (result : Result (SemEnv Value) Value)
    (ih : (patBindings pat).Nodup → everyExp (oneConCheck env.c) expr = true → ∀ next outcome,
      evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluateDecs st env [.dlet loc pat expr] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  split at hs
  · rename_i valid
    have guards : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using valid
    have bound := ih guards.1 guards.2 (evaluate st env [expr]).1 (evaluate st env [expr]).2 (by
      cases evaluate st env [expr]
      rfl)
    cases hv : (evaluate st env [expr]).2 with
    | err err => simp_all
    | val vs =>
      cases hp : pmatch env.c (evaluate st env [expr]).1.refs pat (headValue vs) [] <;> simp_all [typeError]
  · simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_exn {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT)
    (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.dexn loc name types] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg (fun pair => pair.1.clock) h
  simp only [evaluateDecs] at hs
  exact Nat.le_of_eq hs.symm

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_type {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (types : TypeDef) (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.dtype loc types] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg (fun pair => pair.1.clock) h
  simp only [evaluateDecs] at hs
  split at hs <;> simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_env {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : TvarN) (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.denv name] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg (fun pair => pair.1.clock) h
  simp only [evaluateDecs] at hs
  split at hs <;> simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_letrec {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × Flapjack.AstHOL.Exp))
    (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.dletrec loc funs] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg (fun pair => pair.1.clock) h
  simp only [evaluateDecs] at hs
  split at hs <;> simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_letrec {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (funs : List (VarN × VarN × Flapjack.AstHOL.Exp)) (body : Flapjack.AstHOL.Exp)
    (result : Result (List Value) Value)
    (ih : (funs.map (fun (name, _, _) => name)).Nodup → ∀ next outcome,
      evaluate st { env with v := buildRecEnv funs env env.v } [body] = (next, outcome) →
        next.clock ≤ st.clock)
    (h : evaluate st env [.letrec funs body] = (st', result)) : st'.clock ≤ st.clock := by
  simp only [evaluate] at h
  split at h
  · rename_i distinct
    exact ih distinct st' result h
  · simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateMatchClock_cons {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (value errorValue : Value) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (rest : List (Pat × Flapjack.AstHOL.Exp)) (result : Result (List Value) Value)
    (ihRest : (patBindings pat).Nodup → pmatch env.c st.refs pat value [] = .noMatch → ∀ next outcome,
      evaluateMatch st env value rest errorValue = (next, outcome) → next.clock ≤ st.clock)
    (ihBody : (patBindings pat).Nodup → ∀ bindings next outcome, pmatch env.c st.refs pat value [] = .match bindings →
      evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [expr] = (next, outcome) →
        next.clock ≤ st.clock)
    (h : evaluateMatch st env value ((pat, expr) :: rest) errorValue = (st', result)) :
    st'.clock ≤ st.clock := by
  simp only [evaluateMatch] at h
  split at h
  · rename_i distinct
    cases hp : pmatch env.c st.refs pat value [] with
    | noMatch => exact ihRest distinct hp st' result (by simpa only [hp] using h)
    | typeError => simp_all [typeError]
    | «match» bindings => exact ihBody distinct bindings st' result hp (by simpa only [hp] using h)
  · simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_local {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (localDecs decs : List Dec) (result : Result (SemEnv Value) Value)
    (ihFirst : ∀ next outcome, evaluateDecs st env localDecs = (next, outcome) → next.clock ≤ st.clock)
    (ihBody : ∀ middle inner next outcome,
      evaluateDecs st env localDecs = (middle, .val inner) →
      evaluateDecs middle (extendDecEnv inner env) decs = (next, outcome) → next.clock ≤ middle.clock)
    (h : evaluateDecs st env [.dlocal localDecs decs] = (st', result)) : st'.clock ≤ st.clock := by
  let first := evaluateDecs st env localDecs
  have firstBound := ihFirst first.1 first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first firstBound
  simp only [evaluateDecs] at h
  change (match (fixClock st first).2 with
    | .err err => ((fixClock st first).1, .err err)
    | .val inner => evaluateDecs (fixClock st first).1 (extendDecEnv inner env) decs) = (st', result) at h
  rw [clamp] at h
  cases hv : first.2 with
  | err err =>
    simp only [hv] at h
    have hs := congrArg (fun pair => pair.1.clock) h
    exact Nat.le_trans (Nat.le_of_eq hs.symm) firstBound
  | val inner =>
    simp only [hv] at h
    have firstEq : evaluateDecs st env localDecs = (first.1, .val inner) := by
      simpa only [hv] using (Prod.eta first).symm
    exact Nat.le_trans (ihBody first.1 inner st' result firstEq h) firstBound

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_cons {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec) (result : Result (SemEnv Value) Value)
    (ihFirst : ∀ next outcome, evaluateDecs st env [first] = (next, outcome) → next.clock ≤ st.clock)
    (ihTail : ∀ middle inner next outcome,
      evaluateDecs st env [first] = (middle, .val inner) →
      evaluateDecs middle (extendDecEnv inner env) (second :: rest) = (next, outcome) →
        next.clock ≤ middle.clock)
    (h : evaluateDecs st env (first :: second :: rest) = (st', result)) : st'.clock ≤ st.clock := by
  let firstResult := evaluateDecs st env [first]
  have firstBound := ihFirst firstResult.1 firstResult.2 (Prod.eta firstResult).symm
  have clamp := fixClock_eq_of_bound st firstResult firstBound
  simp only [evaluateDecs] at h
  change (match (fixClock st firstResult).2 with
    | .err err => ((fixClock st firstResult).1, .err err)
    | .val inner =>
      let tail := evaluateDecs (fixClock st firstResult).1 (extendDecEnv inner env) (second :: rest)
      (tail.1, combineDecResult inner tail.2)) = (st', result) at h
  rw [clamp] at h
  cases hv : firstResult.2 with
  | err err =>
    simp only [hv] at h
    have hs := congrArg (fun pair => pair.1.clock) h
    exact Nat.le_trans (Nat.le_of_eq hs.symm) firstBound
  | val inner =>
    simp only [hv] at h
    let tail := evaluateDecs firstResult.1 (extendDecEnv inner env) (second :: rest)
    have firstEq : evaluateDecs st env [first] = (firstResult.1, .val inner) := by
      simpa only [hv] using (Prod.eta firstResult).symm
    have tailBound := ihTail firstResult.1 inner tail.1 tail.2 firstEq (Prod.eta tail).symm
    have hs := congrArg (fun pair => pair.1.clock) h
    exact Nat.le_trans (Nat.le_of_eq hs.symm) (Nat.le_trans tailBound firstBound)

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_cons {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (first second : Flapjack.AstHOL.Exp) (rest : List Flapjack.AstHOL.Exp)
    (result : Result (List Value) Value)
    (ihFirst : ∀ next outcome, evaluate st env [first] = (next, outcome) → next.clock ≤ st.clock)
    (ihTail : ∀ middle values next outcome,
      evaluate st env [first] = (middle, .val values) →
      evaluate middle env (second :: rest) = (next, outcome) → next.clock ≤ middle.clock)
    (h : evaluate st env (first :: second :: rest) = (st', result)) : st'.clock ≤ st.clock := by
  let firstResult := evaluate st env [first]
  have firstBound := ihFirst firstResult.1 firstResult.2 (Prod.eta firstResult).symm
  have clamp := fixClock_eq_of_bound st firstResult firstBound
  simp only [evaluate] at h
  change (match (fixClock st firstResult).2 with
    | .err err => ((fixClock st firstResult).1, .err err)
    | .val values =>
      let tail := evaluate (fixClock st firstResult).1 env (second :: rest)
      match tail.2 with
      | .err err => (tail.1, .err err)
      | .val remaining => (tail.1, .val (headValue values :: remaining))) = (st', result) at h
  rw [clamp] at h
  cases hv : firstResult.2 with
  | err err =>
    simp only [hv] at h
    have hs := congrArg (fun pair => pair.1.clock) h
    exact Nat.le_trans (Nat.le_of_eq hs.symm) firstBound
  | val values =>
    simp only [hv] at h
    let tail := evaluate firstResult.1 env (second :: rest)
    have firstEq : evaluate st env [first] = (firstResult.1, .val values) := by
      simpa only [hv] using (Prod.eta firstResult).symm
    have tailBound := ihTail firstResult.1 values tail.1 tail.2 firstEq (Prod.eta tail).symm
    have hs := congrArg (fun pair => pair.1.clock) h
    change (match tail.2 with
      | .err err => (tail.1, Result.err (α := List Value) err)
      | .val remaining => (tail.1, Result.val (β := Value) (headValue values :: remaining))).1.clock = st'.clock at hs
    cases ht : tail.2 <;> simp only [ht] at hs
    all_goals exact Nat.le_trans (Nat.le_of_eq hs.symm) (Nat.le_trans tailBound firstBound)

end Flapjack.EvaluateHOL
