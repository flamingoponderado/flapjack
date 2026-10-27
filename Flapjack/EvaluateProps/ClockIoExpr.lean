import Flapjack.EvaluateProps.ClockIoDecs

/-! Recursive expression cases of the source clock-and-I/O invariant.
The mutual evaluator theorem and full source/carrier review remain open. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_let {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : Option VarN) (first body : AstHOL.Exp)
    (ihFirst : isClockIoMono (fun state => evaluate state env [first]) st)
    (ihBody : ∀ next values, evaluate st env [first] = (next, .val values) →
      isClockIoMono (fun state => evaluate state { env with v := nsOptBind name (headValue values) env.v } [body]) next) :
    isClockIoMono (fun state => evaluate state env [.let_ name first body]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values => evaluate state { env with v := nsOptBind name (headValue values) env.v } [body]
  have hcont : ∀ next result, evaluate st env [first] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | val values => exact ihBody next values heval
    | err error => exact isClockIoMono_err (α := List Value) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [first]) continuation st
    ⟨ihFirst, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [first]; continuation result next) =
      (fun state => evaluate state env [.let_ name first body]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [first] []).1]
    cases heval : evaluate state env [first] with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

/-- Flapjack helper: mapping results preserves the invariant when it preserves timeout. -/
theorem clockIo_mapResult {σ α β γ δ : Type} (st : State σ)
    (f : State σ → State σ × Result α β) (mapResult : Result α β → Result γ δ)
    (ih : isClockIoMono f st)
    (timeout : mapResult (.err (.abort .timeoutError)) = .err (.abort .timeoutError)) :
    isClockIoMono (fun state => let (next, result) := f state; (next, mapResult result)) st := by
  let continuation : Result α β → State σ → State σ × Result γ δ :=
    fun result state => (state, mapResult result)
  have hcont : ∀ next result, f st = (next, result) → isClockIoMono (continuation result) next := by
    intro next result _
    cases hmap : mapResult result with
    | val value => simpa only [continuation, hmap] using isClockIoMono_return (β := δ) next value
    | err error => simpa only [continuation, hmap] using isClockIoMono_err (α := γ) next error
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    simp only [continuation, timeout]
  exact isClockIoMono_bind f continuation st ⟨ih, hcont, htimeout⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ihFirst : isClockIoMono (fun state => evaluate state env [first]) st)
    (ihTail : ∀ next values, evaluate st env [first] = (next, .val values) →
      isClockIoMono (fun state => evaluate state env (second :: rest)) next) :
    isClockIoMono (fun state => evaluate state env (first :: second :: rest)) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values =>
        let tail := evaluate state env (second :: rest)
        (tail.1, match tail.2 with
          | .err error => .err error
          | .val remaining => .val (headValue values :: remaining))
  have hcont : ∀ next result, evaluate st env [first] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val values =>
      let mapResult : Result (List Value) Value → Result (List Value) Value := fun result => match result with
        | .err error => .err error
        | .val remaining => .val (headValue values :: remaining)
      have mapped := clockIo_mapResult next (fun state => evaluate state env (second :: rest)) mapResult
        (ihTail next values heval) rfl
      have fnEq : (fun state => let (tail, result) := evaluate state env (second :: rest); (tail, mapResult result)) =
          continuation (.val values) := by
        funext state
        cases hevalTail : evaluate state env (second :: rest) with
        | mk tail result => cases result <;> simp [continuation, hevalTail, mapResult]
      rw [fnEq] at mapped
      exact mapped
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [first]) continuation st
    ⟨ihFirst, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [first]; continuation result next) =
      (fun state => evaluate state env (first :: second :: rest)) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [first] []).1]
    cases heval : evaluate state env [first] with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only [continuation]
        cases hevalTail : evaluate next env (second :: rest) with
        | mk tail result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_con {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : isClockIoMono (fun state => evaluate state env args.reverse) st) :
    isClockIoMono (fun state => evaluate state env [.con name args]) st := by
  by_cases valid : doConCheck env.c name args.length = true
  · let mapResult : Result (List Value) Value → Result (List Value) Value := fun result => match result with
      | .err error => .err error
      | .val values => match buildConv env.c name values.reverse with
        | none => .err (.abort .typeError)
        | some value => .val [value]
    have mapped := clockIo_mapResult st (fun state => evaluate state env args.reverse) mapResult ih rfl
    have fnEq : (fun (state : State σ) => let (next, result) := evaluate state env args.reverse; (next, mapResult result)) =
        (fun state => evaluate state env [.con name args]) := by
      funext state
      simp only [evaluate, valid, ↓reduceIte]
      cases heval : evaluate state env args.reverse with
      | mk next result =>
        cases result with
        | err error => rfl
        | val values =>
          dsimp only [mapResult]
          cases buildConv env.c name values.reverse <;> rfl
    rw [fnEq] at mapped
    exact mapped
  · simpa [evaluate, valid, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_if {σ : Type} (st : State σ) (env : SemEnv Value)
    (test yes no : AstHOL.Exp)
    (ihTest : isClockIoMono (fun state => evaluate state env [test]) st)
    (ihBranch : ∀ next values chosen, evaluate st env [test] = (next, .val values) →
      doIf (headValue values) yes no = some chosen → isClockIoMono (fun state => evaluate state env [chosen]) next) :
    isClockIoMono (fun state => evaluate state env [.if_ test yes no]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values => match doIf (headValue values) yes no with
        | none => typeError state
        | some chosen => evaluate state env [chosen]
  have hcont : ∀ next result, evaluate st env [test] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val values =>
      cases hif : doIf (headValue values) yes no with
      | none => simpa only [continuation, hif, typeError] using isClockIoMono_err (α := List Value) next (.abort .typeError)
      | some chosen => simpa only [continuation, hif] using ihBranch next values chosen heval hif
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [test]) continuation st
    ⟨ihTest, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [test]; continuation result next) =
      (fun state => evaluate state env [.if_ test yes no]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [test] []).1]
    cases heval : evaluate state env [test] with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only [continuation]
        cases doIf (headValue values) yes no <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_log {σ : Type} (st : State σ) (env : SemEnv Value)
    (op : Lop) (first second : AstHOL.Exp)
    (ihFirst : isClockIoMono (fun state => evaluate state env [first]) st)
    (ihBranch : ∀ next values chosen, evaluate st env [first] = (next, .val values) →
      doLog op (headValue values) second = some (.exp chosen) →
      isClockIoMono (fun state => evaluate state env [chosen]) next) :
    isClockIoMono (fun state => evaluate state env [.log op first second]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values => match doLog op (headValue values) second with
        | none => typeError state
        | some (.val value) => (state, .val [value])
        | some (.exp chosen) => evaluate state env [chosen]
  have hcont : ∀ next result, evaluate st env [first] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val values =>
      cases hlog : doLog op (headValue values) second with
      | none => simpa only [continuation, hlog, typeError] using isClockIoMono_err (α := List Value) next (.abort .typeError)
      | some choice =>
        cases choice with
        | val value => simpa only [continuation, hlog] using isClockIoMono_return (β := Value) next [value]
        | exp chosen => simpa only [continuation, hlog] using ihBranch next values chosen heval hlog
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [first]) continuation st
    ⟨ihFirst, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [first]; continuation result next) =
      (fun state => evaluate state env [.log op first second]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [first] []).1]
    cases heval : evaluate state env [first] with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only [continuation]
        cases hlog : doLog op (headValue values) second with
        | none => rfl
        | some choice => cases choice <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_mat {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (ihExpr : isClockIoMono (fun state => evaluate state env [expr]) st)
    (ihMatch : ∀ next values, evaluate st env [expr] = (next, .val values) →
      canPmatchAll env.c next.refs (clauses.map Prod.fst) (headValue values) = true →
      isClockIoMono (fun state => evaluateMatch state env (headValue values) clauses bindExnV) next) :
    isClockIoMono (fun state => evaluate state env [.mat expr clauses]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values =>
        if canPmatchAll env.c state.refs (clauses.map Prod.fst) (headValue values) then
          evaluateMatch state env (headValue values) clauses bindExnV
        else typeError state
  have hcont : ∀ next result, evaluate st env [expr] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val values =>
      let f : State σ → Bool := fun state => canPmatchAll env.c state.refs (clauses.map Prod.fst) (headValue values)
      let j : State σ → State σ × Result (List Value) Value := fun state => evaluateMatch state env (headValue values) clauses bindExnV
      let k : State σ → State σ × Result (List Value) Value := fun state => typeError state
      have fixed : isClockIoMono (fun state => if f next then j state else k state) next := by
        cases hmatch : f next with
        | false => simpa [hmatch, k, typeError] using isClockIoMono_err (α := List Value) next (.abort .typeError)
        | true =>
          have condition : canPmatchAll env.c next.refs (clauses.map Prod.fst) (headValue values) = true := hmatch
          simpa only [hmatch, ↓reduceIte, j] using ihMatch next values heval condition
      have independent : ∀ state clock, f { state with clock } = f state := by
        intro state clock
        rfl
      have branch := isClockIoMono_ifSafe f j k next ⟨independent, fixed⟩
      simpa only [f, j, k, continuation] using branch
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [expr]) continuation st
    ⟨ihExpr, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [expr]; continuation result next) =
      (fun state => evaluate state env [.mat expr clauses]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [expr] []).1]
    cases heval : evaluate state env [expr] with
    | mk next result => cases result <;> rfl
  rw [fnEq] at bound
  exact bound

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_handle {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (ihExpr : isClockIoMono (fun state => evaluate state env [expr]) st)
    (ihMatch : ∀ next value, evaluate st env [expr] = (next, .err (.raise value)) →
      canPmatchAll env.c next.refs (clauses.map Prod.fst) value = true →
      isClockIoMono (fun state => evaluateMatch state env value clauses value) next) :
    isClockIoMono (fun state => evaluate state env [.handle expr clauses]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .val values => (state, .val values)
      | .err (.abort error) => (state, .err (.abort error))
      | .err (.raise value) =>
        if canPmatchAll env.c state.refs (clauses.map Prod.fst) value then
          evaluateMatch state env value clauses value
        else typeError state
  have hcont : ∀ next result, evaluate st env [expr] = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | val values => exact isClockIoMono_return (β := Value) next values
    | err error =>
      cases error with
      | abort error => exact isClockIoMono_err (α := List Value) next (.abort error)
      | raise value =>
        let f : State σ → Bool := fun state => canPmatchAll env.c state.refs (clauses.map Prod.fst) value
        let j : State σ → State σ × Result (List Value) Value := fun state => evaluateMatch state env value clauses value
        let k : State σ → State σ × Result (List Value) Value := fun state => typeError state
        have fixed : isClockIoMono (fun state => if f next then j state else k state) next := by
          cases hmatch : f next with
          | false => simpa [hmatch, k, typeError] using isClockIoMono_err (α := List Value) next (.abort .typeError)
          | true =>
            have condition : canPmatchAll env.c next.refs (clauses.map Prod.fst) value = true := hmatch
            simpa only [hmatch, ↓reduceIte, j] using ihMatch next value heval condition
        have independent : ∀ state clock, f { state with clock } = f state := by
          intro state clock
          rfl
        have branch := isClockIoMono_ifSafe f j k next ⟨independent, fixed⟩
        simpa only [f, j, k, continuation] using branch
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env [expr]) continuation st
    ⟨ihExpr, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env [expr]; continuation result next) =
      (fun state => evaluate state env [.handle expr clauses]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env [expr] []).1]
    cases heval : evaluate state env [expr] with
    | mk next result =>
      cases result with
      | val values => rfl
      | err error => cases error <;> rfl
  rw [fnEq] at bound
  exact bound

end Flapjack.EvaluateProps
