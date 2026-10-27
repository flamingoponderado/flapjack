import Flapjack.EvaluateProps.ClockIoSafe
import Flapjack.EvaluateProps.PrimitiveLength

/-! Constructor cases for the original mutual clock-and-I/O evaluator theorem.
The recursive assembly and remaining cases are open; source and carrier review
remain pending. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_nil {σ : Type} (st : State σ) (env : SemEnv Value) :
    isClockIoMono (fun state => evaluate state env []) st := by
  simpa only [evaluate] using isClockIoMono_return (β := Value) st ([] : List Value)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_lit {σ : Type} (st : State σ) (env : SemEnv Value) (lit : Lit) :
    isClockIoMono (fun state => evaluate state env [.lit lit]) st := by
  simpa only [evaluate] using isClockIoMono_return (β := Value) st [Value.litv lit]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_fn {σ : Type} (st : State σ) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    isClockIoMono (fun state => evaluate state env [.fn name body]) st := by
  simpa only [evaluate] using isClockIoMono_return (β := Value) st [Value.closure env name body]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_var {σ : Type} (st : State σ) (env : SemEnv Value) (name : Ident ModN VarN) :
    isClockIoMono (fun state => evaluate state env [.var name]) st := by
  cases lookup : nsLookup env.v name with
  | none => simpa only [evaluate, lookup, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)
  | some value => simpa only [evaluate, lookup] using isClockIoMono_return (β := Value) st [value]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoMatch_nil {σ : Type} (st : State σ) (env : SemEnv Value) (value errorValue : Value) :
    isClockIoMono (fun state => evaluateMatch state env value [] errorValue) st := by
  simpa only [evaluateMatch] using isClockIoMono_err (α := List Value) st (.raise errorValue)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_nil {σ : Type} (st : State σ) (env : SemEnv Value) :
    isClockIoMono (fun state => evaluateDecs state env []) st := by
  simp only [evaluateDecs]
  exact isClockIoMono_return _ _

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_tabbrev {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT) :
    isClockIoMono (fun state => evaluateDecs state env [.dtabbrev loc vars name typ]) st := by
  simp only [evaluateDecs]
  exact isClockIoMono_return _ _

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_tannot {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (typ : AstT) (ih : isClockIoMono (fun state => evaluate state env [expr]) st) :
    isClockIoMono (fun state => evaluate state env [.tannot expr typ]) st := by
  simpa only [evaluate] using ih

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_lannot {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (loc : Misc.Location.Locs) (ih : isClockIoMono (fun state => evaluate state env [expr]) st) :
    isClockIoMono (fun state => evaluate state env [.lannot expr loc]) st := by
  simpa only [evaluate] using ih

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_letrec {σ : Type} (st : State σ) (env : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : isClockIoMono (fun state => evaluate state { env with v := buildRecEnv funs env env.v } [body]) st) :
    isClockIoMono (fun state => evaluate state env [.letrec funs body]) st := by
  by_cases distinct : (funs.map (fun (name, _, _) => name)).Nodup
  · simpa only [evaluate, distinct, ↓reduceIte] using ih
  · simpa only [evaluate, distinct, ↓reduceIte, typeError] using
      isClockIoMono_err (α := List Value) st (.abort .typeError)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_raise {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (ih : isClockIoMono (fun state => evaluate state env [expr]) st) :
    isClockIoMono (fun state => evaluate state env [.raise expr]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .val values => (state, .err (.raise (headValue values)))
      | .err error => (state, .err error)
  have hcont : ∀ next result, evaluate st env [expr] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result _
    cases result with
    | val values => exact isClockIoMono_err (α := List Value) next (.raise (headValue values))
    | err error => exact isClockIoMono_err (α := List Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [expr]) continuation st
    ⟨ih, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [expr]; continuation result next) =
      (fun state => evaluate state env [.raise expr]) := by
    funext state
    simp only [evaluate]
    cases heval : evaluate state env [expr] with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_exn {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (name : ConN) (types : List AstT) :
    isClockIoMono (fun state => evaluateDecs state env [.dexn loc name types]) st := by
  simp [isClockIoMono, evaluateDecs, ioEventsMonoHOL]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_type {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (types : List (List TvarN × TypeN × List (ConN × List AstT))) :
    isClockIoMono (fun state => evaluateDecs state env [.dtype loc types]) st := by
  by_cases valid : types.all checkDupCtors = true
  · simp [isClockIoMono, evaluateDecs, valid, ioEventsMonoHOL]
  · simpa [evaluateDecs, valid, typeError] using
      isClockIoMono_err (α := SemEnv Value) st (.abort .typeError)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_letrec {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    isClockIoMono (fun state => evaluateDecs state env [.dletrec loc funs]) st := by
  by_cases distinct : (funs.map (fun (name, _, _) => name)).Nodup
  · by_cases checks : funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr) = true
    · simpa [evaluateDecs, distinct, checks] using
        isClockIoMono_return (β := Value) st ({ v := buildRecEnv funs env nsEmpty, c := nsEmpty } : SemEnv Value)
    · simpa [evaluateDecs, distinct, checks, typeError] using
        isClockIoMono_err (α := SemEnv Value) st (.abort .typeError)
  · simpa [evaluateDecs, distinct, typeError] using
      isClockIoMono_err (α := SemEnv Value) st (.abort .typeError)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_env {σ : Type} (st : State σ) (env : SemEnv Value) (name : TvarN) :
    isClockIoMono (fun state => evaluateDecs state env [.denv name]) st := by
  cases hdecl : declareEnv st.evalState env with
  | none =>
    simp [isClockIoMono, evaluateDecs, hdecl, typeError, ioEventsMonoHOL]
  | some output =>
    rcases output with ⟨value, evalState⟩
    simp [isClockIoMono, evaluateDecs, hdecl, ioEventsMonoHOL]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoMatch_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (value errorValue : Value) (pat : Pat) (expr : AstHOL.Exp) (rest : List (Pat × AstHOL.Exp))
    (ihRest : isClockIoMono (fun state => evaluateMatch state env value rest errorValue) st)
    (ihExpr : ∀ bindings, isClockIoMono
      (fun state => evaluate state { env with v := nsAppend (alistToNs bindings) env.v } [expr]) st) :
    isClockIoMono (fun state => evaluateMatch state env value ((pat, expr) :: rest) errorValue) st := by
  by_cases distinct : (patBindings pat).Nodup
  · let f : State σ → MatchResult (List (VarN × Value)) :=
      fun state => pmatch env.c state.refs pat value []
    let g : State σ → State σ × Result (List Value) Value :=
      fun state => evaluateMatch state env value rest errorValue
    let h : State σ → State σ × Result (List Value) Value := fun state => typeError state
    let j : List (VarN × Value) → State σ → State σ × Result (List Value) Value :=
      fun bindings state => evaluate state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    let choose : MatchResult (List (VarN × Value)) → State σ → State σ × Result (List Value) Value :=
      fun decision state => match decision with
        | .noMatch => g state | .typeError => h state | .match bindings => j bindings state
    have branch : isClockIoMono (fun state => choose (f st) state) st := by
      cases hmatch : f st with
      | noMatch => simpa only [hmatch, choose] using ihRest
      | typeError => simpa only [hmatch, choose, h, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)
      | «match» bindings => simpa only [hmatch, choose] using ihExpr bindings
    have independent : ∀ state clock, f { state with clock } = f state := by
      intro state clock
      rfl
    have result := isClockIoMono_accSafe f st .noMatch choose ⟨independent, Classical.em _, branch⟩
    have fnEq : (fun state => choose (f state) state) =
        (fun state => evaluateMatch state env value ((pat, expr) :: rest) errorValue) := by
      funext state
      simp only [evaluateMatch, distinct, ↓reduceIte, f, choose, g, h, j]
      cases pmatch env.c state.refs pat value [] <;> rfl
    rw [fnEq] at result
    exact result
  · simpa only [evaluateMatch, distinct, ↓reduceIte, typeError] using
      isClockIoMono_err (α := List Value) st (.abort .typeError)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_mod {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : ModN) (decs : List Dec)
    (ih : isClockIoMono (fun state => evaluateDecs state env decs) st) :
    isClockIoMono (fun state => evaluateDecs state env [.dmod name decs]) st := by
  let continuation : Result (SemEnv Value) Value → State σ → State σ × Result (SemEnv Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val inner => (state, .val { v := nsLift name inner.v, c := nsLift name inner.c })
  have hcont : ∀ next result, evaluateDecs st env decs = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result _
    cases result with
    | val inner => exact isClockIoMono_return (β := Value) next ({ v := nsLift name inner.v, c := nsLift name inner.c } : SemEnv Value)
    | err error => exact isClockIoMono_err (α := SemEnv Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluateDecs state env decs) continuation st
    ⟨ih, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluateDecs state env decs; continuation result next) =
      (fun state => evaluateDecs state env [.dmod name decs]) := by
    funext state
    simp only [evaluateDecs]
    cases heval : evaluateDecs state env decs with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_local {σ : Type} (st : State σ) (env : SemEnv Value)
    (localDecs decs : List Dec)
    (ihFirst : isClockIoMono (fun state => evaluateDecs state env localDecs) st)
    (ihBody : ∀ next inner, evaluateDecs st env localDecs = (next, .val inner) →
      isClockIoMono (fun state => evaluateDecs state (extendDecEnv inner env) decs) next) :
    isClockIoMono (fun state => evaluateDecs state env [.dlocal localDecs decs]) st := by
  let continuation : Result (SemEnv Value) Value → State σ → State σ × Result (SemEnv Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val inner => evaluateDecs state (extendDecEnv inner env) decs
  have hcont : ∀ next result, evaluateDecs st env localDecs = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | val inner => exact ihBody next inner heval
    | err error => exact isClockIoMono_err (α := SemEnv Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluateDecs state env localDecs) continuation st
    ⟨ihFirst, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluateDecs state env localDecs; continuation result next) =
      (fun state => evaluateDecs state env [.dlocal localDecs decs]) := by
    funext state
    simp only [evaluateDecs]
    rw [(fixClockEvaluate state env [] localDecs).2]
    cases heval : evaluateDecs state env localDecs with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

/-- Flapjack helper: combining a declaration environment preserves the invariant. -/
theorem clockIo_combineDecResult {σ : Type} (st : State σ) (env : SemEnv Value)
    (f : State σ → State σ × Result (SemEnv Value) Value) (ih : isClockIoMono f st) :
    isClockIoMono (fun state => let (next, result) := f state; (next, combineDecResult env result)) st := by
  let continuation : Result (SemEnv Value) Value → State σ → State σ × Result (SemEnv Value) Value :=
    fun result state => (state, combineDecResult env result)
  have hcont : ∀ next result, f st = (next, result) → isClockIoMono (continuation result) next := by
    intro next result _
    cases result with
    | val inner => exact isClockIoMono_return (β := Value) next _
    | err error => exact isClockIoMono_err (α := SemEnv Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  exact isClockIoMono_bind f continuation st ⟨ih, hcont, htimeout⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (ihFirst : isClockIoMono (fun state => evaluateDecs state env [first]) st)
    (ihTail : ∀ next inner, evaluateDecs st env [first] = (next, .val inner) →
      isClockIoMono (fun state => evaluateDecs state (extendDecEnv inner env) (second :: rest)) next) :
    isClockIoMono (fun state => evaluateDecs state env (first :: second :: rest)) st := by
  let continuation : Result (SemEnv Value) Value → State σ → State σ × Result (SemEnv Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val inner =>
        let tail := evaluateDecs state (extendDecEnv inner env) (second :: rest)
        (tail.1, combineDecResult inner tail.2)
  have hcont : ∀ next result, evaluateDecs st env [first] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | val inner =>
      exact clockIo_combineDecResult next inner
        (fun state => evaluateDecs state (extendDecEnv inner env) (second :: rest)) (ihTail next inner heval)
    | err error => exact isClockIoMono_err (α := SemEnv Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluateDecs state env [first]) continuation st
    ⟨ihFirst, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluateDecs state env [first]; continuation result next) =
      (fun state => evaluateDecs state env (first :: second :: rest)) := by
    funext state
    simp only [evaluateDecs]
    rw [(fixClockEvaluate state env [] [first]).2]
    cases heval : evaluateDecs state env [first] with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoDecs_let {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : isClockIoMono (fun state => evaluate state env [expr]) st) :
    isClockIoMono (fun state => evaluateDecs state env [.dlet loc pat expr]) st := by
  by_cases distinct : (patBindings pat).Nodup
  · by_cases valid : everyExp (oneConCheck env.c) expr = true
    · let continuation : Result (List Value) Value → State σ → State σ × Result (SemEnv Value) Value :=
        fun result state => match result with
          | .err error => (state, .err error)
          | .val values => (state, match pmatch env.c state.refs pat (headValue values) [] with
            | .noMatch => .err (.raise bindExnV)
            | .typeError => .err (.abort .typeError)
            | .match bindings => .val { v := alistToNs bindings, c := nsEmpty })
      have hcont : ∀ next result, evaluate st env [expr] = (next, result) →
          isClockIoMono (continuation result) next := by
        intro next result _
        cases result with
        | err error => exact isClockIoMono_err (α := SemEnv Value) next error
        | val values =>
          let f : State σ → MatchResult (List (VarN × Value)) :=
            fun state => pmatch env.c state.refs pat (headValue values) []
          let choose : MatchResult (List (VarN × Value)) → State σ → State σ × Result (SemEnv Value) Value :=
            fun decision state => (state, match decision with
              | .noMatch => .err (.raise bindExnV)
              | .typeError => .err (.abort .typeError)
              | .match bindings => .val { v := alistToNs bindings, c := nsEmpty })
          have fixed : isClockIoMono (fun state => choose (f next) state) next := by
            cases hmatch : f next with
            | noMatch => simpa only [hmatch, choose] using isClockIoMono_err (α := SemEnv Value) next (.raise bindExnV)
            | typeError => simpa only [hmatch, choose] using isClockIoMono_err (α := SemEnv Value) next (.abort .typeError)
            | «match» bindings =>
              simpa only [hmatch, choose] using isClockIoMono_return (β := Value) next
                ({ v := alistToNs bindings, c := nsEmpty } : SemEnv Value)
          have independent : ∀ state clock, f { state with clock } = f state := by
            intro state clock
            rfl
          have branch := isClockIoMono_accSafe f next .noMatch choose ⟨independent, Classical.em _, fixed⟩
          have fnEq : (fun state => choose (f state) state) = continuation (.val values) := by
            funext state
            dsimp only [choose, f, continuation]
          rw [fnEq] at branch
          exact branch
      have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
          (next, .err (.abort .timeoutError)) := by
        intro next
        rfl
      have bound := isClockIoMono_bind (fun state => evaluate state env [expr]) continuation st ⟨ih, hcont, htimeout⟩
      have fnEq : (fun state => let (next, result) := evaluate state env [expr]; continuation result next) =
          (fun state => evaluateDecs state env [.dlet loc pat expr]) := by
        funext state
        simp only [evaluateDecs, distinct, valid]
        cases heval : evaluate state env [expr] with
        | mk next result =>
          cases result with
          | err error => rfl
          | val values =>
            dsimp only [continuation]
            cases pmatch env.c next.refs pat (headValue values) [] <;> rfl
      rw [fnEq] at bound
      exact bound
    · simpa [evaluateDecs, distinct, valid, typeError] using
        isClockIoMono_err (α := SemEnv Value) st (.abort .typeError)
  · simpa [evaluateDecs, distinct, typeError] using
      isClockIoMono_err (α := SemEnv Value) st (.abort .typeError)

end Flapjack.EvaluateProps
