import Flapjack.EvaluateHOL.ClockFull
import Flapjack.EvaluateProps.DoApp

/-! Constructor cases of the original mutual source evaluator FFI theorem.
The mutual induction is assembled in `EvaluateFfiFull`.
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

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_let {σ : Type} (st : State σ) (env : SemEnv Value)
    (name : Option VarN) (first body : AstHOL.Exp)
    (ihFirst : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [first]).1.ffi)
    (ihBody : ∀ middle values, evaluate st env [first] = (middle, .val values) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi
        (evaluate middle { env with v := nsOptBind name (headValue values) env.v } [body]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.let_ name first body]).1.ffi := by
  let firstResult := evaluate st env [first]
  have bound := evaluateClockFull st firstResult.1 env [first] firstResult.2 (Prod.eta firstResult).symm
  have clamp := fixClock_eq_of_bound st firstResult bound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st firstResult).2 with
      | .err err => ((fixClock st firstResult).1, Result.err (α := List Value) err)
      | .val values => evaluate (fixClock st firstResult).1
        { env with v := nsOptBind name (headValue values) env.v } [body]).1.ffi
  rw [clamp]
  cases hv : firstResult.2 with
  | err err => simpa only [hv] using ihFirst
  | val values =>
    have firstEq : evaluate st env [first] = (firstResult.1, .val values) := by
      simpa only [hv] using (Prod.eta firstResult).symm
    simpa only [hv] using ihFirst.trans (ihBody firstResult.1 values firstEq)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_if {σ : Type} (st : State σ) (env : SemEnv Value)
    (test yes no : AstHOL.Exp)
    (ihTest : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [test]).1.ffi)
    (ihBranch : ∀ middle values chosen, evaluate st env [test] = (middle, .val values) →
      doIf (headValue values) yes no = some chosen →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluate middle env [chosen]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.if_ test yes no]).1.ffi := by
  let first := evaluate st env [test]
  have bound := evaluateClockFull st first.1 env [test] first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first bound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st first).2 with
      | .err err => ((fixClock st first).1, Result.err (α := List Value) err)
      | .val values => match _hif : doIf (headValue values) yes no with
        | none => typeError (fixClock st first).1
        | some chosen => evaluate (fixClock st first).1 env [chosen]).1.ffi
  rw [clamp]
  cases hv : first.2 with
  | err err => simpa only [hv] using ihTest
  | val values =>
    have firstEq : evaluate st env [test] = (first.1, .val values) := by
      simpa only [hv] using (Prod.eta first).symm
    simp only
    cases hc : doIf (headValue values) yes no with
    | none => simpa only [hc, typeError] using ihTest
    | some chosen => simpa only [hc] using ihTest.trans (ihBranch first.1 values chosen firstEq hc)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_log {σ : Type} (st : State σ) (env : SemEnv Value)
    (op : Lop) (firstExpr second : AstHOL.Exp)
    (ihFirst : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [firstExpr]).1.ffi)
    (ihBranch : ∀ middle values chosen, evaluate st env [firstExpr] = (middle, .val values) →
      doLog op (headValue values) second = some (.exp chosen) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluate middle env [chosen]).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.log op firstExpr second]).1.ffi := by
  let first := evaluate st env [firstExpr]
  have bound := evaluateClockFull st first.1 env [firstExpr] first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first bound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st first).2 with
      | .err err => ((fixClock st first).1, Result.err (α := List Value) err)
      | .val values => match _hlog : doLog op (headValue values) second with
        | none => typeError (fixClock st first).1
        | some (.val v) => ((fixClock st first).1, Result.val (β := Value) [v])
        | some (.exp chosen) => evaluate (fixClock st first).1 env [chosen]).1.ffi
  rw [clamp]
  cases hv : first.2 with
  | err err => simpa only [hv] using ihFirst
  | val values =>
    have firstEq : evaluate st env [firstExpr] = (first.1, .val values) := by
      simpa only [hv] using (Prod.eta first).symm
    simp only
    cases hc : doLog op (headValue values) second with
    | none => simpa only [hc, typeError] using ihFirst
    | some choice =>
      cases choice with
      | val v => simpa only [hc] using ihFirst
      | exp chosen => simpa only [hc] using ihFirst.trans (ihBranch first.1 values chosen firstEq hc)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_mat {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (ihExpr : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi)
    (ihMatch : ∀ middle values, evaluate st env [expr] = (middle, .val values) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi
        (evaluateMatch middle env (headValue values) clauses bindExnV).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.mat expr clauses]).1.ffi := by
  let first := evaluate st env [expr]
  have bound := evaluateClockFull st first.1 env [expr] first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first bound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st first).2 with
      | .err err => ((fixClock st first).1, Result.err (α := List Value) err)
      | .val values =>
        if canPmatchAll env.c (fixClock st first).1.refs (clauses.map Prod.fst) (headValue values) then
          evaluateMatch (fixClock st first).1 env (headValue values) clauses bindExnV
        else typeError (fixClock st first).1).1.ffi
  rw [clamp]
  cases hv : first.2 with
  | err err => simpa only [hv] using ihExpr
  | val values =>
    have firstEq : evaluate st env [expr] = (first.1, .val values) := by
      simpa only [hv] using (Prod.eta first).symm
    simp only
    split
    · exact ihExpr.trans (ihMatch first.1 values firstEq)
    · simpa only [typeError] using ihExpr

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_handle {σ : Type} (st : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (ihExpr : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [expr]).1.ffi)
    (ihMatch : ∀ middle value, evaluate st env [expr] = (middle, .err (.raise value)) →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluateMatch middle env value clauses value).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.handle expr clauses]).1.ffi := by
  let first := evaluate st env [expr]
  have bound := evaluateClockFull st first.1 env [expr] first.2 (Prod.eta first).symm
  have clamp := fixClock_eq_of_bound st first bound
  simp only [evaluate]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match (fixClock st first).2 with
      | .val values => ((fixClock st first).1, Result.val (β := Value) values)
      | .err (.abort err) => ((fixClock st first).1, Result.err (α := List Value) (.abort err))
      | .err (.raise value) =>
        if canPmatchAll env.c (fixClock st first).1.refs (clauses.map Prod.fst) value then
          evaluateMatch (fixClock st first).1 env value clauses value
        else typeError (fixClock st first).1).1.ffi
  rw [clamp]
  cases hv : first.2 with
  | val values => simpa only [hv] using ihExpr
  | err error =>
    cases error with
    | abort error => simpa only [hv] using ihExpr
    | raise value =>
      have firstEq : evaluate st env [expr] = (first.1, .err (.raise value)) := by
        simpa only [hv] using (Prod.eta first).symm
      simp only
      split
      · exact ihExpr.trans (ihMatch first.1 value firstEq)
      · simpa only [typeError] using ihExpr

/-- Flapjack helper: dynamic evaluation bookkeeping does not change the FFI. -/
theorem doEvalRes_ffi {σ β : Type} (values : List Value) (st : State σ) :
    (doEvalRes (β := β) values st).1.ffi = st.ffi := by
  unfold doEvalRes
  split <;> rfl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateFfi_app {σ : Type} (st : State σ) (env : SemEnv Value)
    (op : AstHOL.Op) (args : List AstHOL.Exp)
    (ihArgs : Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env args.reverse).1.ffi)
    (ihFun : ∀ middle values callEnv body,
      evaluate st env args.reverse = (middle, .val values) → getOpClass op = .funApp →
      doOpApp values.reverse = some (callEnv, body) → middle.clock ≠ 0 →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluate (decClock middle) callEnv [body]).1.ffi)
    (ihForce : ∀ middle values thunk callEnv body,
      evaluate st env args.reverse = (middle, .val values) → getOpClass op = .force →
      destThunk values.reverse middle.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → middle.clock ≠ 0 →
      Relation.ReflTransGen callFFIRelHOL middle.ffi (evaluate (decClock middle) callEnv [body]).1.ffi)
    (ihEval : ∀ middle values decoded evalEnv decs,
      evaluate st env args.reverse = (middle, .val values) → getOpClass op = .evalOp →
      doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)) → decoded.clock ≠ 0 →
      Relation.ReflTransGen callFFIRelHOL decoded.ffi (evaluateDecs (decClock decoded) evalEnv decs).1.ffi) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env [.app op args]).1.ffi := by
  let first := evaluate st env args.reverse
  have firstBound := evaluateClockFull st first.1 env args.reverse first.2 (Prod.eta first).symm
  have clamp : fixClock st (evaluate st env args.reverse) = evaluate st env args.reverse :=
    fixClock_eq_of_bound st first firstBound
  simp only [evaluate, clamp]
  change Relation.ReflTransGen callFFIRelHOL st.ffi
    (match first.2 with | .err err => (first.1, Result.err (α := List Value) err) | .val _ => _).1.ffi
  cases hv : first.2 with
  | err err => simpa only [hv] using ihArgs
  | val values =>
    have firstEq : evaluate st env args.reverse = (first.1, .val values) := by
      simpa only [hv] using (Prod.eta first).symm
    simp only
    cases hc : getOpClass op with
    | funApp =>
      simp only
      cases happ : doOpApp values.reverse with
      | none => simpa only [happ, typeError] using ihArgs
      | some call =>
        rcases call with ⟨callEnv, body⟩
        simp only
        split
        · simpa only [timeoutError] using ihArgs
        · rename_i nonzero
          simpa only [decClock] using ihArgs.trans (ihFun first.1 values callEnv body firstEq hc happ nonzero)
    | force =>
      simp only
      change Relation.ReflTransGen callFFIRelHOL st.ffi
        (match destThunk values.reverse first.1.refs with
          | .badRef | .notThunk => typeError first.1
          | .isThunk .evaluated v => (first.1, Result.val (β := Value) [v])
          | .isThunk .notEvaluated thunk => match doOpApp [thunk, .conv none []] with
            | none => typeError first.1
            | some (callEnv, body) =>
              if first.1.clock = 0 then timeoutError first.1 else
              let next := evaluate (decClock first.1) callEnv [body]
              match next.2 with
              | .err err => (next.1, Result.err (α := List Value) err)
              | .val newValues => match updateThunk values.reverse next.1.refs newValues with
                | none => typeError next.1
                | some refs => ({ next.1 with refs }, Result.val (β := Value) newValues)).1.ffi
      cases hd : destThunk values.reverse first.1.refs with
      | badRef => simpa only [hd, typeError] using ihArgs
      | notThunk => simpa only [hd, typeError] using ihArgs
      | isThunk mode thunk =>
        cases mode with
        | evaluated => simpa only [hd] using ihArgs
        | notEvaluated =>
          simp only
          cases happ : doOpApp [thunk, .conv none []] with
          | none => simpa only [happ, typeError] using ihArgs
          | some call =>
            rcases call with ⟨callEnv, body⟩
            simp only
            split
            · simpa only [timeoutError] using ihArgs
            · rename_i nonzero
              let next := evaluate (decClock first.1) callEnv [body]
              have nextRel := ihForce first.1 values thunk callEnv body firstEq hc hd happ nonzero
              have total := ihArgs.trans nextRel
              change Relation.ReflTransGen callFFIRelHOL st.ffi
                (match next.2 with
                  | .err err => (next.1, Result.err (α := List Value) err)
                  | .val newValues => match updateThunk values.reverse next.1.refs newValues with
                    | none => typeError next.1
                    | some refs => ({ next.1 with refs }, Result.val (β := Value) newValues)).1.ffi
              cases hn : next.2 with
              | err err => simpa only [hn] using total
              | val newValues =>
                simp only
                cases hu : updateThunk values.reverse next.1.refs newValues with
                | none => simpa only [hu, typeError] using total
                | some refs => simpa only [hu] using total
    | simple =>
      simp only
      cases ha : doApp (first.1.refs, first.1.ffi) op values.reverse with
      | none => simpa only [ha, typeError] using ihArgs
      | some output =>
        rcases output with ⟨⟨refs, ffi⟩, outcome⟩
        have step := doApp_callFFIRel first.1.refs refs first.1.ffi ffi op values.reverse outcome ha
        simpa only [ha] using ihArgs.trans step
    | evalOp =>
      simp only [fixClockDoEvalRes]
      let decoded := doEvalRes (β := Value) values.reverse first.1
      have decodedFfi : decoded.1.ffi = first.1.ffi := doEvalRes_ffi _ _
      change Relation.ReflTransGen callFFIRelHOL st.ffi
        (match decoded.2 with
          | .err err => (decoded.1, Result.err (α := List Value) err)
          | .val (evalEnv, decs) => _).1.ffi
      cases hd : decoded.2 with
      | err err => simpa only [hd, decodedFfi] using ihArgs
      | val info =>
        rcases info with ⟨evalEnv, decs⟩
        simp only
        split
        · simpa only [timeoutError, doEvalRes_ffi] using ihArgs
        · rename_i nonzero
          let next := evaluateDecs (decClock decoded.1) evalEnv decs
          have nextBound := evaluateDecsClockFull (decClock decoded.1) next.1 evalEnv decs next.2 (Prod.eta next).symm
          have clampNext : fixClock (decClock decoded.1) next = next :=
            fixClock_eq_of_bound (decClock decoded.1) next nextBound
          rw [clampNext]
          have decodedEq : doEvalRes (β := Value) values.reverse first.1 =
              (decoded.1, .val (evalEnv, decs)) := by
            simpa only [hd] using (Prod.eta decoded).symm
          have nextRel := ihEval first.1 values decoded.1 evalEnv decs firstEq hc decodedEq nonzero
          have total := ihArgs.trans (by simpa only [decodedFfi] using nextRel)
          change Relation.ReflTransGen callFFIRelHOL st.ffi
            (match next.2 with
              | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
                | none => typeError next.1
                | some (value, evalState) =>
                  ({ next.1 with evalState := resetEnvGeneration first.1.evalState evalState }, Result.val (β := Value) [value])
              | .err (.abort err) => (next.1, Result.err (α := List Value) (.abort err))
              | .err err => ({ next.1 with evalState := resetEnvGeneration first.1.evalState next.1.evalState },
                  Result.err (α := List Value) err)).1.ffi
          cases hn : next.2 with
          | val newEnv =>
            simp only
            cases he : declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
            | none => simpa only [he, typeError] using total
            | some output =>
              rcases output with ⟨value, evalState⟩
              simpa only [he] using total
          | err err =>
            cases err with
            | abort err => simpa only [hn] using total
            | raise value => simpa only [hn] using total

end Flapjack.EvaluateProps
