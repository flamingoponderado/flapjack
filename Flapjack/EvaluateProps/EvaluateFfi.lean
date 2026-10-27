import Flapjack.EvaluateHOL.ClockFull
import Flapjack.EvaluateProps.DoApp

/-! Constructor cases of the original mutual source evaluator FFI theorem.
The general mutual induction and remaining expression/declaration cases are open.
These cases inherit the evaluator's pending carrier review and floating-point
rational-cut assumption. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_nil {σ : Type} (st : State σ) (env : SemEnv Value) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env []).1.ffi := by
  simp only [evaluate]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_lit {σ : Type} (st : State σ) (env : SemEnv Value) (lit : Lit) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.lit lit]).1.ffi := by
  simp only [evaluate]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_fun {σ : Type} (st : State σ) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.fn name body]).1.ffi := by
  simp only [evaluate]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_var {σ : Type} (st : State σ) (env : SemEnv Value) (name : Ident ModN VarN) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.var name]).1.ffi := by
  simp only [evaluate]
  split <;> simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateMatchFfi_nil {σ : Type} (st : State σ) (env : SemEnv Value) (value errorValue : Value) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateMatch st env value [] errorValue).1.ffi := by
  simp only [evaluateMatch]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_nil {σ : Type} (st : State σ) (env : SemEnv Value) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env []).1.ffi := by
  simp only [evaluateDecs]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_raise {σ : Type} (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.raise expr]).1.ffi := by
  simp only [evaluate]
  cases h : (evaluate st env [expr]).2 <;> simp_all

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_tannot {σ : Type} (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp) (typ : AstT)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.tannot expr typ]).1.ffi := by
  simpa only [evaluate] using ih

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_lannot {σ : Type} (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp) (loc : Misc.Location.Locs)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.lannot expr loc]).1.ffi := by
  simpa only [evaluate] using ih

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ihFirst : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [first]).1.ffi)
    (ihTail : ∀ middle values, evaluate st env [first] = (middle, .val values) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluate middle env (second :: rest)).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env (first :: second :: rest)).1.ffi := by
  let firstResult := evaluate st env [first]
  have firstBound := evaluateClockFull st firstResult.1 env [first] firstResult.2 (Prod.eta firstResult).symm
  have clamp := fixClock_eq_of_bound st firstResult firstBound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st firstResult).2 with
      | .err err => ((fixClock st firstResult).1, Result.err (α := List Value) err)
      | .val values =>
        let tail := evaluate (fixClock st firstResult).1 env (second :: rest)
        match tail.2 with
        | .err err => (tail.1, Result.err (α := List Value) err)
        | .val remaining => (tail.1, Result.val (β := Value) (headValue values :: remaining))).1.ffi
  rw [clamp]
  cases hv : firstResult.2 with
  | err err => simpa only [hv] using ihFirst
  | val values =>
    have firstEq : evaluate st env [first] = (firstResult.1, .val values) := by
      simpa only [hv] using (Prod.eta firstResult).symm
    have tailRel := ihTail firstResult.1 values firstEq
    cases ht : (evaluate firstResult.1 env (second :: rest)).2 <;>
      simpa only [hv, ht] using ihFirst.trans tailRel

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateMatchFfi_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (value errorValue : Value) (pat : Pat) (expr : AstHOL.Exp) (rest : List (Pat × AstHOL.Exp))
    (ihRest : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateMatch st env value rest errorValue).1.ffi)
    (ihExpr : ∀ bindings, Relation.ReflTransGen callFFIRelHOL st.ffi
      (evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [expr]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi
      (evaluateMatch st env value ((pat, expr) :: rest) errorValue).1.ffi := by
  simp only [evaluateMatch]
  split
  · split <;> simp_all [typeError, Relation.ReflTransGen.refl]
  · simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_tabbrev {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dtabbrev loc vars name typ]).1.ffi := by
  simp only [evaluateDecs]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_exn {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (name : ConN) (types : List AstT) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dexn loc name types]).1.ffi := by
  simp only [evaluateDecs]
  exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_type {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (types : List (List TvarN × TypeN × List (ConN × List AstT))) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dtype loc types]).1.ffi := by
  simp only [evaluateDecs]
  split <;> simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_mod {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : ModN) (decs : List Dec)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env decs).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dmod name decs]).1.ffi := by
  simp only [evaluateDecs]
  cases h : (evaluateDecs st env decs).2 <;> simpa only [h] using ih

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_cons {σ : Type} (st : State σ) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (ihFirst : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [first]).1.ffi)
    (ihTail : ∀ middle inner, evaluateDecs st env [first] = (middle, .val inner) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi
        (evaluateDecs middle (extendDecEnv inner env) (second :: rest)).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env (first :: second :: rest)).1.ffi := by
  let firstResult := evaluateDecs st env [first]
  have firstBound := evaluateDecsClockFull st firstResult.1 env [first] firstResult.2 (Prod.eta firstResult).symm
  have clamp := fixClock_eq_of_bound st firstResult firstBound
  simp only [evaluateDecs]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st firstResult).2 with
      | .err err => ((fixClock st firstResult).1, Result.err (α := SemEnv Value) err)
      | .val inner =>
        let tail := evaluateDecs (fixClock st firstResult).1 (extendDecEnv inner env) (second :: rest)
        (tail.1, combineDecResult inner tail.2)).1.ffi
  rw [clamp]
  cases hv : firstResult.2 with
  | err err => simpa only [hv] using ihFirst
  | val inner =>
    have firstEq : evaluateDecs st env [first] = (firstResult.1, .val inner) := by
      simpa only [hv] using (Prod.eta firstResult).symm
    have tailRel := ihTail firstResult.1 inner firstEq
    simpa only [hv] using ihFirst.trans tailRel

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_local {σ : Type} (st : State σ) (env : SemEnv Value)
    (localDecs decs : List Dec)
    (ihLocal : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env localDecs).1.ffi)
    (ihBody : ∀ middle inner, evaluateDecs st env localDecs = (middle, .val inner) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluateDecs middle (extendDecEnv inner env) decs).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dlocal localDecs decs]).1.ffi := by
  let first := evaluateDecs st env localDecs
  have bound := evaluateDecsClockFull st first.1 env localDecs first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first bound
  simp only [evaluateDecs]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st first).2 with
      | .err err => ((fixClock st first).1, Result.err (α := SemEnv Value) err)
      | .val inner => evaluateDecs (fixClock st first).1 (extendDecEnv inner env) decs).1.ffi
  rw [clamp]
  cases hv : first.2 with
  | err err => simpa only [hv] using ihLocal
  | val inner =>
    have firstEq : evaluateDecs st env localDecs = (first.1, .val inner) := by
      simpa only [hv] using (Prod.eta first).symm
    simpa only [hv] using ihLocal.trans (ihBody first.1 inner firstEq)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_let {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dlet loc pat expr]).1.ffi := by
  simp only [evaluateDecs]
  split
  · cases hv : (evaluate st env [expr]).2 with
    | err err => simpa only [hv] using ih
    | val values =>
      simp only
      split <;> simpa only [typeError] using ih
  · simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_con {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env args.reverse).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.con name args]).1.ffi := by
  simp only [evaluate]
  split
  · cases hv : (evaluate st env args.reverse).2 with
    | err err => simpa only [hv] using ih
    | val values =>
      simp only
      split <;> simpa only [typeError] using ih
  · simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_env {σ : Type} (st : State σ) (env : SemEnv Value) (name : TvarN) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.denv name]).1.ffi := by
  simp only [evaluateDecs]
  split <;> simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateDecsFfi_letrec {σ : Type} (st : State σ) (env : SemEnv Value)
    (loc : Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env [.dletrec loc funs]).1.ffi := by
  simp only [evaluateDecs]
  split <;> simp [typeError, Relation.ReflTransGen.refl]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_letrec {σ : Type} (st : State σ) (env : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : Relation.ReflTransGen callFFIRelHOL st.ffi
      (evaluate st { env with v := buildRecEnv funs env env.v } [body]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.letrec funs body]).1.ffi := by
  simp only [evaluate]
  split
  · exact ih
  · simp [typeError, Relation.ReflTransGen.refl]

end Flapjack.EvaluateProps
