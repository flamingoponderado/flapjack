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

end Flapjack.EvaluateProps
