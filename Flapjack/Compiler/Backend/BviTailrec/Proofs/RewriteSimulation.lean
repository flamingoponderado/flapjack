import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth

/-! Cases of the source tail-recursion rewrite simulation. The evaluator,
source scan and compilation carriers remain subject to HOL review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- A scan never selects the non-optimizing operator. This is untagged until
its scan and expression carriers have completed source review. -/
theorem scanSing_ne_noop (ctx : List ValueType) (loc : Nat) (e : Bvi.Exp) :
    (scanSing ctx loc e).2.2.2 ≠ some .noop := by
  cases e with
  | var n => simp [scanSing.eq_def]
  | force a n => simp [scanSing.eq_def]
  | tick body =>
    rw [scanSing.eq_def]
    exact scanSing_ne_noop ctx loc body
  | «let» bindings body =>
    rw [scanSing.eq_def]
    dsimp only
    exact scanSing_ne_noop _ loc body
  | ifThenElse cond yes no =>
    rw [scanSing.eq_def]
    dsimp only
    cases hy : scanSing (scanSing ctx loc cond).1 loc yes with
    | mk cy resty =>
      rcases resty with ⟨ty, branchy, opy⟩
      cases hn : scanSing (scanSing ctx loc cond).1 loc no with
      | mk cn restn =>
        rcases restn with ⟨tn, branchn, opn⟩
        have iy := scanSing_ne_noop (scanSing ctx loc cond).1 loc yes
        have ineg := scanSing_ne_noop (scanSing ctx loc cond).1 loc no
        simp only [hy] at iy
        simp only [hn] at ineg
        cases opy <;> cases opn <;> simp_all
  | op op args =>
    rw [scanSing.eq_def]
    dsimp only
    split <;> split
    · split <;> split <;> simp_all
    · split <;> simp_all
    · intro impossible
      cases h : fromOp op <;> simp_all [BEq.beq, instBEqAssocOp.beq]
    · split
      · split <;> simp_all
      · simp
  | raise body => simp [scanSing.eq_def]
  | «return» args => simp [scanSing.eq_def]
  | call ticks dest args handler => simp [scanSing.eq_def]
  | letCall rets ticks dest args body => simp [scanSing.eq_def]
termination_by sizeOf e

/-- A successful optimization check identifies a non-noop accumulator and
a matching, non-`any` result type in the singleton scan. -/
theorem checkExpOriginal_scan (loc arity : Nat) (e : Bvi.Exp) (op : AssocOp)
    (check : checkExpOriginal loc arity e = some op) :
    ∃ ctx ty branch, scanExpr (List.replicate arity .any) loc [e] = [(ctx, ty, branch, some op)] ∧
      ty = opType op ∧ ty ≠ .any ∧ op ≠ .noop := by
  rw [checkExpOriginal, scanExpr_single] at check
  cases hrec : hasRec1 loc e <;> simp [hrec] at check
  rcases hscan : scanSing (List.replicate arity .any) loc e with ⟨ctx, ty, branch, found⟩
  rw [hscan] at check
  dsimp only at check
  cases found with
  | none => simp at check
  | some foundOp =>
    simp only at check
    split at check
    · simp only [Option.some.injEq] at check
      subst foundOp
      have notNoop := scanSing_ne_noop (List.replicate arity .any) loc e
      rw [hscan] at notNoop
      have notOp : op ≠ .noop := by simpa using notNoop
      have sameType : ty = opType op := by
        cases ty <;> cases op <;> simp_all [opType, BEq.beq, instBEqValueType.beq, ValueType.ctorIdx]
      have notAny : ty ≠ .any := by
        rw [sameType]
        cases op <;> simp_all [opType]
      exact ⟨ctx, ty, branch, by rw [scanExpr_single, hscan], sameType, notAny, notOp⟩
    · simp at check

/-- Every environment satisfies the all-unknown context used when checking a
function body. -/
theorem tyRel_replicate_any (values : List Value) :
    tyRel values (List.replicate values.length .any) := by
  induction values with
  | nil => simp [tyRel]
  | cons value rest ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact .cons (by simp) ih

/-- A successful checked function body returns a value satisfying the
selected accumulator operator's type. -/
theorem checkExpOriginal_result_type {C F : Type} (loc arity : Nat) (body : Bvi.Exp)
    (op : AssocOp) (env : List Value) (state next : BviSem.BviState C F) (value : Value)
    (lengthEq : env.length = arity) (check : checkExpOriginal loc arity body = some op)
    (run : BviSem.evaluate [body] env state = (.val [value], next)) :
    valueMatchesType value (opType op) := by
  obtain ⟨ctx, ty, branch, scan, sameType, _, _⟩ := checkExpOriginal_scan loc arity body op check
  have envType : tyRel env (List.replicate arity .any) := by
    simpa [lengthEq] using tyRel_replicate_any env
  have sound := scanSound_list (List.replicate arity .any) loc [body] env state next [value] envType run
  rw [scan] at sound
  simp only [List.map_cons, List.map_nil] at sound
  subst ty
  cases sound.2 with
  | cons head tail => exact head

/-- The source-shaped postcondition for the tail-rewrite simulation. The
default list head is unreachable when the optimization premise holds, since
the corresponding source hypothesis requires a singleton expression list. -/
def rewriteTailPost {C F : Type} (xs : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F)
    (_env1 : List Value) (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType) : Prop :=
  ∃ targetNext, BviSem.evaluate xs env2 target = (result, targetNext) ∧
    stateRel sourceNext targetNext ∧
    (optimized = true → ∀ op workerLoc body arity,
      sptLookup loc source.code = some (arity, body) ∧
      optimizedCode loc arity body workerLoc target.code op ∧
      opType op = ty ∧
      (∃ op1 tt resultTy branch,
        scanExpr ts loc [xs.headD (.var 0)] = [(tt, resultTy, branch, some op1)] ∧
        resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) →
      let rewritten := (rewriteSource loc workerLoc op acc ts (xs.headD (.var 0))).2
      ∃ rewrittenResult t1 t2,
        BviSem.evaluate [rewritten] env2 target = (rewrittenResult, t1) ∧
        BviSem.evaluate [applyOp op (.var acc) (xs.headD (.var 0))] env2 target = (rewrittenResult, t2) ∧
        stateRel sourceNext t1 ∧ stateRel sourceNext t2)

/-- The hypotheses of the source-shaped rewrite simulation. -/
def rewriteTailHyp {C F : Type} (xs : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F)
    (env1 : List Value) (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (_loc : Nat) (ts : List ValueType) (ty : ValueType) : Prop :=
  BviSem.evaluate xs env1 source = (result, sourceNext) ∧
  envRel ty optimized acc env1 env2 ∧ stateRel source target ∧ tyRel env1 ts ∧
  (optimized = true → xs.length = 1) ∧ result ≠ .err (.abort .typeError)

/-- The full source-shaped simulation property for an expression list. -/
def rewriteTailProperty {C F : Type} (xs : List Bvi.Exp) : Prop :=
  ∀ (source : BviSem.BviState (Nat × C) F) env1 result sourceNext optimized
    (target : BviSem.BviState C F) acc env2 loc ts ty,
    rewriteTailHyp xs source env1 result sourceNext optimized target acc env2 loc ts ty →
    rewriteTailPost xs source env1 result sourceNext optimized target acc env2 loc ts ty

/-- Disabling optimization keeps the environment-prefix part of the source
environment relation. -/
theorem envRel_disable (ty : ValueType) (optimized : Bool) (acc : Nat)
    (env1 env2 : List Value) (h : envRel ty optimized acc env1 env2) :
    envRel ty false acc env1 env2 := by
  exact ⟨h.1, by simp⟩

/-- Prepending the same evaluated bindings to both environments shifts the
accumulator index by their length while preserving its value and type. -/
theorem envRel_prepend (ty : ValueType) (optimized : Bool) (acc : Nat)
    (env1 env2 bindings : List Value) (h : envRel ty optimized acc env1 env2) :
    envRel ty optimized (bindings.length + acc) (bindings ++ env1) (bindings ++ env2) := by
  obtain ⟨⟨suffix, pref⟩, optimizedRel⟩ := h
  refine ⟨⟨suffix, by simp [pref, List.append_assoc]⟩, ?_⟩
  intro enabled
  obtain ⟨lengthEq, bound, typed⟩ := optimizedRel enabled
  refine ⟨by simp [lengthEq], by simp [bound], ?_⟩
  cases ty <;> simp_all

/-- The context inferred for a let body is sound after its bindings
successfully evaluate. -/
theorem tyRel_letBindings {C F : Type} (ts : List ValueType) (loc : Nat)
    (bindings : List Bvi.Exp) (env values : List Value)
    (state next : BviSem.BviState C F) (related : tyRel env ts)
    (run : BviSem.evaluate bindings env state = (.val values, next)) :
    let scans := scanExpr ts loc bindings
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ts
    tyRel (values ++ env) (types ++ last) := by
  have sound := scanSound_list ts loc bindings env state next values related run
  let scans := scanExpr ts loc bindings
  let types := scans.map fun (_, ty, _, _) => ty
  let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ts
  have lastSound : tyRel env last := by
    cases hlast : scans.getLast? with
    | none => simpa [last, hlast] using related
    | some entry =>
      have entrySound := sound.1 entry (List.mem_of_getLast? hlast)
      obtain ⟨a, b, c, d⟩ := entry
      simpa [last, hlast] using entrySound
  exact tyRel_append env last types values ⟨lastSound, sound.2⟩

/-- Optimized wrapper and worker entries persist when evaluation extends the
code tree without changing existing entries. -/
theorem optimizedCode_subspt (loc arity : Nat) (body : Bvi.Exp) (workerLoc : Nat)
    (code extended : Spt (Nat × Bvi.Exp)) (op : AssocOp)
    (optimized : optimizedCode loc arity body workerLoc code op)
    (growth : sptSubspt code extended) : optimizedCode loc arity body workerLoc extended op := by
  obtain ⟨wrapper, worker, compiled, check, wrapperFound, workerFound⟩ := optimized
  have wrapperMem := (sptMem_iff_lookup loc code).mpr ⟨_, wrapperFound⟩
  have workerMem := (sptMem_iff_lookup workerLoc code).mpr ⟨_, workerFound⟩
  exact ⟨wrapper, worker, compiled, check, (growth loc wrapperMem).2.trans wrapperFound,
    (growth workerLoc workerMem).2.trans workerFound⟩

/-- Evaluation preserves a previously installed function at its location. -/
theorem evaluate_lookup_preserved {C F : Type} (xs : List Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (result : BviSem.BviResult)
    (loc arity : Nat) (body : Bvi.Exp)
    (run : BviSem.evaluate xs env state = (result, next))
    (found : sptLookup loc state.code = some (arity, body)) :
    sptLookup loc next.code = some (arity, body) := by
  have growth := BviProps.evaluate_code_mono xs env state next result run
  have member := (sptMem_iff_lookup loc state.code).mpr ⟨_, found⟩
  exact (growth loc member).2.trans found

/-- Decrementing both related clocks by the same amount preserves the state
relation. -/
theorem stateRel_decClock {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (amount : Nat) (h : stateRel source target) :
    stateRel (BviSem.decClock amount source) (BviSem.decClock amount target) := by
  have clocks := (stateRel_const source target h).2.1
  simpa [BviSem.decClock, clocks] using stateRel_withClock source target (source.clock - amount) h

/-- A lookup into an environment prefix returns the same value in the
extended environment. -/
theorem lookup_of_envRel (ty : ValueType) (optimized : Bool) (acc n : Nat)
    (env1 env2 : List Value) (h : envRel ty optimized acc env1 env2)
    (value : Value) (lookup : env1[n]? = some value) : env2[n]? = some value := by
  have bound : n < env1.length := (List.getElem?_eq_some_iff.mp lookup).1
  obtain ⟨suffix, rfl⟩ := h.1
  rw [List.getElem?_append_left bound]
  exact lookup

/-- Empty-list case of the source rewrite simulation. The source singleton
condition excludes optimization for an empty expression list. -/
theorem rewriteTail_nil {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (env1 : List Value) (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (hyp : BviSem.evaluate [] env1 source = (result, sourceNext) ∧
      envRel ty optimized acc env1 env2 ∧ stateRel source target ∧ tyRel env1 ts ∧
      (optimized = true → ([] : List Bvi.Exp).length = 1) ∧
      result ≠ .err (.abort .typeError)) :
    rewriteTailPost [] source env1 result sourceNext optimized target acc env2 loc ts ty := by
  obtain ⟨run, _, stateRelated, _, singleton, _⟩ := hyp
  have same : (result, sourceNext) = (.val [], source) := by simpa [BviSem.evaluate] using run.symm
  cases same
  refine ⟨target, by simp [BviSem.evaluate], stateRelated, ?_⟩
  intro enabled
  have impossible := singleton enabled
  simp at impossible

/-- Variable case of the source rewrite simulation. No optimization can be
selected by a variable scan. This is untagged until the evaluator and source
compilation definitions have completed source review. -/
theorem rewriteTail_var {C F : Type} (n : Nat) (source : BviSem.BviState (Nat × C) F)
    (env1 : List Value) (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (hyp : BviSem.evaluate [.var n] env1 source = (result, sourceNext) ∧
      envRel ty optimized acc env1 env2 ∧ stateRel source target ∧ tyRel env1 ts ∧
      (optimized = true → ([.var n] : List Bvi.Exp).length = 1) ∧
      result ≠ .err (.abort .typeError)) :
    rewriteTailPost [.var n] source env1 result sourceNext optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, stateRelated, _, _, notTypeError⟩ := hyp
  cases lookup : env1[n]? with
  | none =>
    simp [BviSem.evaluate, lookup] at run
    exact (notTypeError run.1.symm).elim
  | some value =>
    have targetLookup := lookup_of_envRel ty optimized acc n env1 env2 envRelated value lookup
    have same : (result, sourceNext) = (.val [value], source) := by
      simpa [BviSem.evaluate, lookup] using run.symm
    cases same
    refine ⟨target, ?_, stateRelated, ?_⟩
    · simp [BviSem.evaluate, targetLookup]
    · intro _ op workerLoc body arity required
      obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
      rw [scanExpr_single, scanSing.eq_def] at scan
      simp at scan

/-- The source-shaped simulation property holds for an empty list. -/
theorem rewriteTailProperty_nil {C F : Type} : rewriteTailProperty (C := C) (F := F) [] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  exact rewriteTail_nil source env1 result sourceNext optimized target acc env2 loc ts ty hyp

/-- The source-shaped simulation property holds for a single variable. -/
theorem rewriteTailProperty_var {C F : Type} (n : Nat) :
    rewriteTailProperty (C := C) (F := F) [.var n] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  exact rewriteTail_var n source env1 result sourceNext optimized target acc env2 loc ts ty hyp

/-- With a known accumulator, applying an operator first evaluates its other
operand and dispatches on the resulting values. -/
theorem evaluate_applyOp_var {C F : Type} (op : AssocOp) (acc : Nat)
    (body : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (value : Value) (lookup : env[acc]? = some value) :
    BviSem.evaluate [applyOp op (.var acc) body] env state =
      match BviSem.evaluate [body] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match BviSem.doApp (toOp op) (values.reverse ++ [value]) next with
        | .err error => (.err error, next)
        | .val (result, last) => (.val [result], last) := by
  have varRun : BviSem.evaluate [.var acc] env state = (.val [value], state) := by
    simp [BviSem.evaluate, lookup]
  have listRun : BviSem.evaluate [.var acc, body] env state =
      match BviSem.evaluate [body] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => (.val (value :: values), next) := by
    have h := BviSem.evaluateConsCons (.var acc) body [] env state
    simp only [BviSem.evaluateTuple, varRun, Flapjack.holHd] at h
    cases run : BviSem.evaluate [body] env state with
    | mk result last => cases result <;> simpa [run] using h
  simp only [applyOp]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, listRun]
  cases run : BviSem.evaluate [body] env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      simp only [List.reverse_cons]
      cases h : BviSem.doApp (toOp op) (values.reverse ++ [value]) next with
      | err error => rfl
      | val output => cases output; rfl

/-- Adding the accumulator identity to a well-typed body result preserves its
result and final state, including propagated errors. -/
theorem evaluate_applyOp_identity {C F : Type} (op : AssocOp) (acc : Nat)
    (body : Bvi.Exp) (env : List Value) (state next : BviSem.BviState C F)
    (result : BviSem.BviResult) (notNoop : op ≠ .noop)
    (lookup : env[acc]? = some (opIdValue op))
    (run : BviSem.evaluate [body] env state = (result, next))
    (typed : ∀ value, result = .val [value] → valueMatchesType value (opType op)) :
    BviSem.evaluate [applyOp op (.var acc) body] env state = (result, next) := by
  rw [evaluate_applyOp_var op acc body env state (opIdValue op) lookup, run]
  cases result with
  | err error => rfl
  | val values =>
    obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton body env state next values run
    have identity := accumulator_identity_right op value notNoop (typed value rfl)
    simp [doApp_toOp_pure, identity]

/-- A let binding can be moved outside an accumulator operation by shifting
the accumulator index past the values bound by the let. -/
theorem evaluate_applyOp_let {C F : Type} (op : AssocOp) (acc : Nat)
    (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state : BviSem.BviState C F) (value : Value) (lookup : env[acc]? = some value) :
    BviSem.evaluate [applyOp op (.var acc) (.let bindings body)] env state =
      BviSem.evaluate [.let bindings (applyOp op (.var (bindings.length + acc)) body)] env state := by
  have letEval (e : Bvi.Exp) : BviSem.evaluate [.let bindings e] env state =
      match BviSem.evaluate bindings env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => BviSem.evaluate [e] (values ++ env) next := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate]
    cases BviSem.evaluate bindings env state with
    | mk result next => cases result <;> rfl
  rw [evaluate_applyOp_var op acc (.let bindings body) env state value lookup]
  rw [letEval, letEval]
  cases bindRun : BviSem.evaluate bindings env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      have lengthEq := BviSem.evaluate_length bindings env state next values bindRun
      have shifted : (values ++ env)[bindings.length + acc]? = some value := by
        rw [← lengthEq, List.getElem?_append_right (by omega)]
        simpa using lookup
      dsimp only
      rw [evaluate_applyOp_var op (bindings.length + acc) body (values ++ env) next value shifted]

/-- A related code entry executes the same body result after compilation.
The recursive simulation hypothesis is the one used for the called body. -/
theorem evaluate_related_callee {C F : Type} (loc arity : Nat) (body : Bvi.Exp)
    (env : List Value) (source sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (result : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] source env result sourceNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] source env result sourceNext optimized target acc env2 loc ts ty)
    (related : stateRel source target) (lengthEq : env.length = arity)
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (run : BviSem.evaluate [body] env source = (result, sourceNext))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ compiled targetNext, sptLookup loc target.code = some (arity, compiled) ∧
      BviSem.evaluate [compiled] env target = (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  have types : tyRel env (List.replicate arity .any) := by
    simpa [lengthEq] using tyRel_replicate_any env
  have codeRelated := stateRel_codeRel source target related
  cases check : checkExpOriginal loc arity body with
  | none =>
    have found := (codeRelated loc arity body .noop sourceCode).1 check
    have envRelated : envRel .any false arity env env := ⟨⟨[], by simp⟩, by simp⟩
    have hyp : rewriteTailHyp [body] source env result sourceNext false target arity env loc
        (List.replicate arity .any) .any :=
      ⟨run, envRelated, related, types, by simp, notTypeError⟩
    obtain ⟨targetNext, targetRun, finalRelated, _⟩ :=
      bodyIH false target arity env loc (List.replicate arity .any) .any hyp
    exact ⟨body, targetNext, found, targetRun, finalRelated⟩
  | some op =>
    obtain ⟨scanCtx, scanTy, scanBranch, scan, sameType, notAny, notNoop⟩ :=
      checkExpOriginal_scan loc arity body op check
    obtain ⟨workerLoc, codeLookup⟩ := (codeRelated loc arity body op sourceCode).2 check
    let worker := (rewriteSource loc workerLoc op arity (List.replicate arity .any) body).2
    let wrapper := letWrap arity (identity op) worker
    have compiled : compileExpSource loc workerLoc arity body = some (wrapper, worker) := by
      simp [compileExpSource, check, wrapper, worker]
    obtain ⟨wrapperFound, workerFound⟩ := codeLookup wrapper worker compiled
    have optimized : optimizedCode loc arity body workerLoc target.code op :=
      ⟨wrapper, worker, compiled, check, wrapperFound, workerFound⟩
    let extended := env ++ [opIdValue op] ++ env
    have envRelated : envRel (opType op) true arity env extended := by
      simpa [extended, lengthEq] using envRel_initial op env notNoop
    have hyp : rewriteTailHyp [body] source env result sourceNext true target arity extended loc
        (List.replicate arity .any) (opType op) :=
      ⟨run, envRelated, related, types, by simp, notTypeError⟩
    obtain ⟨ordinaryNext, ordinaryRun, _, optimizedRun⟩ :=
      bodyIH true target arity extended loc
        (List.replicate arity .any) (opType op) hyp
    have req : sptLookup loc source.code = some (arity, body) ∧
        optimizedCode loc arity body workerLoc target.code op ∧ opType op = opType op ∧
        (∃ op1 tt resultTy branch,
          scanExpr (List.replicate arity .any) loc [body] = [(tt, resultTy, branch, some op1)] ∧
          resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) :=
      ⟨sourceCode, optimized, rfl, op, scanCtx, scanTy, scanBranch, scan, notAny, notNoop, rfl⟩
    obtain ⟨r, t1, t2, workerRun, appliedRun, finalRelated, _⟩ :=
      optimizedRun rfl op workerLoc body arity (by simpa only [List.headD_cons] using req)
    have lookup : extended[arity]? = some (opIdValue op) := by simp [extended, ← lengthEq]
    have typed : ∀ value, result = .val [value] → valueMatchesType value (opType op) := by
      intro value eq
      have sourceRun : BviSem.evaluate [body] env source = (.val [value], sourceNext) := by simpa [eq] using run
      exact checkExpOriginal_result_type loc arity body op env source sourceNext value lengthEq check sourceRun
    have identityRun := evaluate_applyOp_identity op arity body extended target ordinaryNext result notNoop
      lookup ordinaryRun typed
    simp only [List.headD_cons] at appliedRun workerRun
    rw [identityRun] at appliedRun
    have resultEq : r = result := (congrArg Prod.fst appliedRun).symm
    subst r
    refine ⟨wrapper, t1, wrapperFound, ?_, finalRelated⟩
    change BviSem.evaluate [letWrap arity (identity op) worker] env target = _
    rw [← lengthEq, evaluate_letWrap worker op env target notNoop]
    exact workerRun

/-- A known accumulator lookup commutes with a tick around its second operand.
The timeout still occurs before any accumulator operation is dispatched. -/
theorem evaluate_applyOp_tick {C F : Type} (op : AssocOp) (acc : Nat)
    (body : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (value : Value) (lookup : env[acc]? = some value) :
    BviSem.evaluate [applyOp op (.var acc) (.tick body)] env state =
      BviSem.evaluate [.tick (applyOp op (.var acc) body)] env state := by
  have varRun (s : BviSem.BviState C F) :
      BviSem.evaluate [.var acc] env s = (.val [value], s) := by
    simp [BviSem.evaluate, lookup]
  have listRun (e : Bvi.Exp) (s : BviSem.BviState C F) :
      BviSem.evaluate [.var acc, e] env s =
        match BviSem.evaluate [e] env s with
        | (.err err, last) => (.err err, last)
        | (.val values, last) => (.val (value :: values), last) := by
    have h := BviSem.evaluateConsCons (.var acc) e [] env s
    simp only [BviSem.evaluateTuple, varRun, Flapjack.holHd] at h
    cases run : BviSem.evaluate [e] env s with
    | mk result last => cases result <;> simpa [run] using h
  by_cases zero : state.clock = 0
  · simp [applyOp, BviSem.evaluate, listRun, zero, BviSem.fixClock]
    cases state; simp_all
  · have bound := BviSem.evaluate_clock_le [body] env (BviSem.decClock 1 state)
    cases run : BviSem.evaluate [body] env (BviSem.decClock 1 state) with
    | mk result last =>
      rw [run] at bound
      have clocks : last.clock ≤ state.clock - 1 := by simpa [BviSem.decClock] using bound
      simp only [BviSem.decClock] at run
      cases result <;>
        simp [applyOp, BviSem.evaluate, listRun, zero, run, BviSem.fixClock,
          BviSem.decClock, Nat.min_eq_right (by omega : last.clock ≤ state.clock),
          Nat.min_eq_right clocks]

/-- Tick case of the source-shaped simulation. The recursive call receives
both states after decrementing their related clocks. -/
theorem rewriteTail_tick {C F : Type} (body : Bvi.Exp)
    (ih : rewriteTailProperty (C := C) (F := F) [body]) :
    rewriteTailProperty (C := C) (F := F) [.tick body] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  obtain ⟨run, envRelated, stateRelated, types, _, notTypeError⟩ := hyp
  have clocks := (stateRel_const source target stateRelated).2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have same : (result, sourceNext) = (.err (.abort .timeoutError), source) := by
      simpa [BviSem.evaluate, zero] using run.symm
    cases same
    refine ⟨target, by simp [BviSem.evaluate, targetZero], stateRelated, ?_⟩
    intro enabled op workerLoc code arity required
    simp only [List.headD_cons] at required ⊢
    have accBound := (envRelated.2 enabled).2.1
    have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
    refine ⟨.err (.abort .timeoutError), target, target, ?_, ?_, stateRelated, stateRelated⟩
    · cases eqn : rewriteSource loc workerLoc op acc ts body with
      | mk flag rewritten =>
        rw [rewriteSource.eq_def]
        dsimp only
        rw [eqn]
        simp [BviSem.evaluate, targetZero]
    · rw [evaluate_applyOp_tick op acc body env2 target env2[acc] lookup]
      simp [BviSem.evaluate, targetZero]
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : BviSem.evaluate [body] env1 (BviSem.decClock 1 source) = (result, sourceNext) := by
      simpa [BviSem.evaluate, zero] using run
    have nextRelated := stateRel_decClock source target 1 stateRelated
    have bodyHyp : rewriteTailHyp [body] (BviSem.decClock 1 source) env1 result sourceNext
        optimized (BviSem.decClock 1 target) acc env2 loc ts ty :=
      ⟨bodyRun, envRelated, nextRelated, types, by simp, notTypeError⟩
    obtain ⟨targetNext, targetRun, targetRelated, optRun⟩ :=
      ih (BviSem.decClock 1 source) env1 result sourceNext optimized
        (BviSem.decClock 1 target) acc env2 loc ts ty bodyHyp
    refine ⟨targetNext, by simpa [BviSem.evaluate, targetNonzero] using targetRun, targetRelated, ?_⟩
    intro enabled op workerLoc code arity required
    simp only [List.headD_cons] at required ⊢
    have accBound := (envRelated.2 enabled).2.1
    have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
    have requiredBody :
        sptLookup loc (BviSem.decClock 1 source).code = some (arity, code) ∧
        optimizedCode loc arity code workerLoc (BviSem.decClock 1 target).code op ∧
        opType op = ty ∧
        (∃ op1 tt resultTy branch,
          scanExpr ts loc [body] = [(tt, resultTy, branch, some op1)] ∧
          resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) := by
      have scanEq : scanExpr ts loc [.tick body] = scanExpr ts loc [body] := by
        rw [scanExpr_single, scanExpr_single, scanSing.eq_def]
      simpa only [BviSem.decClock, scanEq] using required
    obtain ⟨r, t1, t2, rewritten, applied, rel1, rel2⟩ := optRun enabled op workerLoc code arity requiredBody
    refine ⟨r, t1, t2, ?_, ?_, rel1, rel2⟩
    · cases eqn : rewriteSource loc workerLoc op acc ts body with
      | mk flag rewrittenBody =>
        simp only [List.headD_cons, eqn] at rewritten
        rw [rewriteSource.eq_def]
        dsimp only
        rw [eqn]
        simpa [BviSem.evaluate, targetNonzero] using rewritten
    · rw [evaluate_applyOp_tick op acc body env2 target env2[acc] lookup]
      simpa [BviSem.evaluate, targetNonzero] using applied

/-- The local-binding case of the tail-rewrite simulation. -/
theorem rewriteTail_let {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (bindingsIH : rewriteTailProperty (C := C) (F := F) bindings)
    (bodyIH : rewriteTailProperty (C := C) (F := F) [body]) :
    rewriteTailProperty (C := C) (F := F) [.let bindings body] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  obtain ⟨run, envRelated, stateRelated, types, _, notTypeError⟩ := hyp
  have disabled := envRel_disable ty optimized acc env1 env2 envRelated
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases bindingRun : BviSem.evaluate bindings env1 source with
  | mk bindingResult middle =>
    cases bindingResult with
    | err error =>
      simp only [bindingRun] at run
      have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have bindingHyp : rewriteTailHyp bindings source env1 (.err error) middle false
          target acc env2 loc ts ty := ⟨bindingRun, disabled, stateRelated, types, by simp, ok⟩
      obtain ⟨targetMiddle, targetBindings, middleRelated, _⟩ :=
        bindingsIH source env1 (.err error) middle false target acc env2 loc ts ty bindingHyp
      have same : (.err error, middle) = (result, sourceNext) := by simpa [bindingRun] using run
      cases same
      refine ⟨targetMiddle, ?_, middleRelated, ?_⟩
      · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
      · intro enabled op workerLoc code arity required
        simp only [List.headD_cons] at required ⊢
        have accBound := (envRelated.2 enabled).2.1
        have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
        refine ⟨.err error, targetMiddle, targetMiddle, ?_, ?_, middleRelated, middleRelated⟩
        · rw [rewriteSource.eq_def]
          dsimp only
          cases eqn : rewriteSource loc workerLoc op (acc + bindings.length)
            ((scanExpr ts loc bindings).map (fun (_, t, _, _) => t) ++
              (match (scanExpr ts loc bindings).getLast? with | some (cs, _, _, _) => cs | none => ts)) body with
          | mk flag rewritten =>
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
        · rw [evaluate_applyOp_let op acc bindings body env2 target env2[acc] lookup]
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
    | val values =>
      have bindingHyp : rewriteTailHyp bindings source env1 (.val values) middle false
          target acc env2 loc ts ty := ⟨bindingRun, disabled, stateRelated, types, by simp, by simp⟩
      obtain ⟨targetMiddle, targetBindings, middleRelated, _⟩ :=
        bindingsIH source env1 (.val values) middle false target acc env2 loc ts ty bindingHyp
      have bodyRun : BviSem.evaluate [body] (values ++ env1) middle = (result, sourceNext) := by
        simpa [bindingRun] using run
      let scans := scanExpr ts loc bindings
      let bodyTypes := scans.map (fun (_, t, _, _) => t) ++
        (match scans.getLast? with | some (cs, _, _, _) => cs | none => ts)
      have extendedTypes : tyRel (values ++ env1) bodyTypes :=
        tyRel_letBindings ts loc bindings env1 values source middle types bindingRun
      have extendedEnv := envRel_prepend ty optimized acc env1 env2 values envRelated
      have lenEq := BviSem.evaluate_length bindings env1 source middle values bindingRun
      have bodyHyp : rewriteTailHyp [body] middle (values ++ env1) result sourceNext optimized
          targetMiddle (bindings.length + acc) (values ++ env2) loc bodyTypes ty := by
        refine ⟨bodyRun, ?_, middleRelated, extendedTypes, by simp, notTypeError⟩
        simpa [lenEq] using extendedEnv
      obtain ⟨targetNext, targetBody, targetRelated, optRun⟩ :=
        bodyIH middle (values ++ env1) result sourceNext optimized targetMiddle
          (bindings.length + acc) (values ++ env2) loc bodyTypes ty bodyHyp
      refine ⟨targetNext, ?_, targetRelated, ?_⟩
      · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
        exact targetBody
      · intro enabled op workerLoc code arity required
        simp only [List.headD_cons] at required ⊢
        obtain ⟨sourceCode, optCode, sameType, op1, tt, resultTy, branch,
          scan, notAny, notNoop, sameOp⟩ := required
        have sourceCodeNext := evaluate_lookup_preserved bindings env1 source middle (.val values)
          loc arity code bindingRun sourceCode
        have targetGrowth := BviProps.evaluate_code_mono bindings env2 target targetMiddle (.val values) targetBindings
        have targetCodeNext := optimizedCode_subspt loc arity code workerLoc target.code targetMiddle.code
          op optCode targetGrowth
        have bodyScan : ∃ out branch2,
            scanExpr bodyTypes loc [body] = [(out, resultTy, branch2, some op1)] := by
          rw [scanExpr_single, scanSing.eq_def] at scan
          dsimp only at scan
          rcases hscan : scanSing bodyTypes loc body with ⟨out, foundType, foundBranch, foundOp⟩
          rw [← scanExpr_list] at scan
          change [((scanSing bodyTypes loc body).1.drop scans.length,
            (scanSing bodyTypes loc body).2.1, false,
            (scanSing bodyTypes loc body).2.2.2)] = _ at scan
          rw [hscan] at scan
          simp only [List.cons.injEq, and_true, Prod.mk.injEq] at scan
          obtain ⟨_, rfl, _, rfl⟩ := scan
          refine ⟨out, foundBranch, ?_⟩
          rw [scanExpr_single, hscan]
        obtain ⟨bodyOut, bodyBranch, bodyScan⟩ := bodyScan
        have requiredBody : sptLookup loc middle.code = some (arity, code) ∧
            optimizedCode loc arity code workerLoc targetMiddle.code op ∧ opType op = ty ∧
            (∃ op1 tt resultTy branch,
              scanExpr bodyTypes loc [body] = [(tt, resultTy, branch, some op1)] ∧
              resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) :=
          ⟨sourceCodeNext, targetCodeNext, sameType,
            op1, bodyOut, resultTy, bodyBranch, bodyScan, notAny, notNoop, sameOp⟩
        obtain ⟨r, t1, t2, rewritten, applied, rel1, rel2⟩ :=
          optRun enabled op workerLoc code arity (by simpa only [List.headD_cons] using requiredBody)
        have accBound := (envRelated.2 enabled).2.1
        have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
        refine ⟨r, t1, t2, ?_, ?_, rel1, rel2⟩
        · rw [rewriteSource.eq_def]
          dsimp only
          have eqIndices : acc + bindings.length = bindings.length + acc := Nat.add_comm _ _
          rw [eqIndices]
          change BviSem.evaluate [.let bindings (rewriteSource loc workerLoc op
            (bindings.length + acc) bodyTypes body).2] env2 target = (r, t1)
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
          simpa only [List.headD_cons] using rewritten
        · rw [evaluate_applyOp_let op acc bindings body env2 target env2[acc] lookup]
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetBindings]
          simpa only [List.headD_cons] using applied

/-- A successful direct or indirect call identifies an original code entry.
Any replacement at that location and arity resolves to the same arguments. -/
theorem findCode_replacement (dest : Option Nat) (args actual : List Value)
    (source : Spt (Nat × Bvi.Exp)) (body : Bvi.Exp)
    (run : findCode dest args source = some (actual, body)) :
    ∃ loc, sptLookup loc source = some (actual.length, body) ∧
      ∀ (target : Spt (Nat × Bvi.Exp)) (replacement : Bvi.Exp),
        sptLookup loc target = some (actual.length, replacement) →
        findCode dest args target = some (actual, replacement) := by
  cases dest with
  | some loc =>
    cases found : sptLookup loc source with
    | none => simp [findCode, found] at run
    | some entry =>
      obtain ⟨arity, code⟩ := entry
      by_cases length : args.length = arity
      · simp [findCode, found, length] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨loc, by simpa [length] using found, fun target replacement lookup => by
          simp [findCode, lookup]⟩
      · simp [findCode, found, length] at run
  | none =>
    cases empty : args.isEmpty with
    | true => simp [findCode, empty] at run
    | false =>
      cases last : Flapjack.holLast args with
      | codePtr loc =>
        cases found : sptLookup loc source with
        | none => simp [findCode, empty, last, found] at run
        | some entry =>
          obtain ⟨arity, code⟩ := entry
          by_cases length : args.length = arity + 1
          · simp [findCode, empty, last, found, length] at run
            obtain ⟨rfl, rfl⟩ := run
            have dropLength : args.dropLast.length = arity := by simp [List.length_dropLast, length]
            refine ⟨loc, by simpa [dropLength] using found, ?_⟩
            intro target replacement lookup
            simp [findCode, empty, last, dropLength, lookup, length]
          · simp [findCode, empty, last, found, length] at run
      | _ => simp [findCode, empty, last] at run

/-- A related code tree resolves a successful call to the same arguments,
with the original body replaced by its compiled counterpart. -/
theorem codeRel_findCode_replacement (dest : Option Nat) (args actual : List Value)
    (source target : Spt (Nat × Bvi.Exp)) (body : Bvi.Exp)
    (related : codeRel source target)
    (resolved : findCode dest args source = some (actual, body)) :
    ∃ compiled, findCode dest args target = some (actual, compiled) := by
  obtain ⟨loc, sourceLookup, resolveReplacement⟩ := findCode_replacement dest args actual source body resolved
  obtain ⟨compiled, targetLookup⟩ := codeRel_lookup_arity source target related loc actual.length body sourceLookup
  exact ⟨compiled, resolveReplacement target compiled targetLookup⟩

/-- A resolved direct or indirect call runs the related compiled callee with
the same arguments after decrementing both related clocks. -/
theorem evaluate_related_resolved_callee {C F : Type} (dest : Option Nat)
    (args actual : List Value) (body : Bvi.Exp) (amount : Nat)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] (BviSem.decClock amount source) actual result sourceNext
        optimized target acc env2 loc ts ty →
      rewriteTailPost [body] (BviSem.decClock amount source) actual result sourceNext
        optimized target acc env2 loc ts ty)
    (related : stateRel source target)
    (resolved : findCode dest args source.code = some (actual, body))
    (run : BviSem.evaluate [body] actual (BviSem.decClock amount source) = (result, sourceNext))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ compiled targetNext, findCode dest args target.code = some (actual, compiled) ∧
      BviSem.evaluate [compiled] actual (BviSem.decClock amount target) = (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  obtain ⟨loc, sourceLookup, resolveReplacement⟩ := findCode_replacement dest args actual source.code body resolved
  have relatedNext := stateRel_decClock source target amount related
  have sourceNextLookup : sptLookup loc (BviSem.decClock amount source).code =
      some (actual.length, body) := by simpa [BviSem.decClock] using sourceLookup
  obtain ⟨compiled, targetNext, targetLookup, targetRun, finalRelated⟩ :=
    evaluate_related_callee loc actual.length body actual (BviSem.decClock amount source)
      sourceNext (BviSem.decClock amount target) result bodyIH relatedNext rfl sourceNextLookup run notTypeError
  have lookup : sptLookup loc target.code = some (actual.length, compiled) := by
    simpa [BviSem.decClock] using targetLookup
  exact ⟨compiled, targetNext, resolveReplacement target.code compiled lookup, targetRun, finalRelated⟩

/-- Force case of the rewrite simulation. The induction hypothesis applies
to any called body at a strictly smaller clock, as in the source induction. -/
theorem rewriteTail_force {C F : Type} (place index : Nat)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (args : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called args r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called args r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.force place index] source env1 result sourceNext optimized target acc env2 loc ts ty) :
    rewriteTailPost [.force place index] source env1 result sourceNext optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, stateRelated, types, _, notTypeError⟩ := hyp
  have constants := stateRel_const source target stateRelated
  have noOptimization : optimized = true → ∀ op workerLoc code arity,
      sptLookup loc source.code = some (arity, code) ∧
      optimizedCode loc arity code workerLoc target.code op ∧ opType op = ty ∧
      (∃ op1 tt resultTy branch,
        scanExpr ts loc [([.force place index] : List Bvi.Exp).headD (.var 0)] =
          [(tt, resultTy, branch, some op1)] ∧ resultTy ≠ .any ∧
          op1 ≠ .noop ∧ opType op1 = opType op) →
      let rewritten := (rewriteSource loc workerLoc op acc ts
        (([.force place index] : List Bvi.Exp).headD (.var 0))).2
      ∃ rewrittenResult t1 t2,
        BviSem.evaluate [rewritten] env2 target = (rewrittenResult, t1) ∧
        BviSem.evaluate [applyOp op (.var acc) (([.force place index] : List Bvi.Exp).headD (.var 0))]
          env2 target = (rewrittenResult, t2) ∧ stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
    intro _ op workerLoc code arity required
    obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
    rw [scanExpr_single, scanSing.eq_def] at scan
    simp at scan
  cases lookup : env1[index]? with
  | none =>
    simp [BviSem.evaluate, lookup] at run
    exact (notTypeError run.1.symm).elim
  | some thunk =>
    have targetLookup := lookup_of_envRel ty optimized acc index env1 env2 envRelated thunk lookup
    cases thunkRun : BviSem.destThunk thunk source.refs with
    | badRef =>
      simp [BviSem.evaluate, lookup, thunkRun] at run
      exact (notTypeError run.1.symm).elim
    | notThunk =>
      simp [BviSem.evaluate, lookup, thunkRun] at run
      exact (notTypeError run.1.symm).elim
    | isThunk mode value =>
      have targetThunk : BviSem.destThunk thunk target.refs = .isThunk mode value := by
        simpa [constants.1] using thunkRun
      cases mode with
      | evaluated =>
        have same : (result, sourceNext) = (.val [value], source) := by
          simpa [BviSem.evaluate, lookup, thunkRun] using run.symm
        cases same
        exact ⟨target, by simp [BviSem.evaluate, targetLookup, targetThunk], stateRelated, noOptimization⟩
      | notEvaluated =>
        cases codeLookup : sptLookup place source.code with
        | none =>
          simp [BviSem.evaluate, lookup, thunkRun, findCode, codeLookup] at run
          exact (notTypeError run.1.symm).elim
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          by_cases arityEq : arity = 2
          · subst arity
            have relatedCode := stateRel_codeRel source target stateRelated
            obtain ⟨compiled, targetCode⟩ := codeRel_lookup_arity source.code target.code relatedCode
              place 2 body codeLookup
            by_cases zero : source.clock = 0
            · have targetZero : target.clock = 0 := by omega
              have same : (result, sourceNext) = (.err (.abort .timeoutError), { source with clock := 0 }) := by
                simpa [BviSem.evaluate, lookup, thunkRun, findCode, codeLookup, zero] using run.symm
              cases same
              have relatedZero := stateRel_withClock source target 0 stateRelated
              refine ⟨{ target with clock := 0 }, ?_, relatedZero, noOptimization⟩
              simp [BviSem.evaluate, targetLookup, targetThunk, findCode, targetCode, targetZero]
            · have targetNonzero : target.clock ≠ 0 := by omega
              have nextRelated := stateRel_decClock source target 1 stateRelated
              have small : (BviSem.decClock 1 source).clock < source.clock := by
                simp only [BviSem.decClock]
                omega
              cases bodyRun : BviSem.evaluate [body] [thunk, value] (BviSem.decClock 1 source) with
              | mk inner last =>
                simp only [BviSem.evaluate, lookup, thunkRun, findCode, codeLookup,
                  List.length_cons, List.length_nil, Nat.reduceAdd, ↓reduceIte, zero, bodyRun] at run
                have same : (inner, last) = (result, sourceNext) := by
                  cases inner with
                  | val values => exact run
                  | err error =>
                    cases error with
                    | abort reason => exact run
                    | raise payload =>
                      cases payload with
                      | exn exception => exact run
                      | ret values =>
                        simp at run
                        exact (notTypeError run.1.symm).elim
                have notReturn : ∀ values, inner ≠ .err (.raise (.ret values)) := by
                  intro values eq
                  rw [eq] at run
                  simp at run
                  exact notTypeError run.1.symm
                cases same
                obtain ⟨targetBody, targetNext, targetBodyCode, targetBodyRun, finalRelated⟩ :=
                  evaluate_related_callee place 2 body [thunk, value]
                    (BviSem.decClock 1 source) sourceNext (BviSem.decClock 1 target) result
                    (clockIH body (BviSem.decClock 1 source) [thunk, value] result sourceNext small)
                    nextRelated (by simp) (by simpa [BviSem.decClock] using codeLookup) bodyRun notTypeError
                have targetLookupCode : sptLookup place target.code = some (2, targetBody) := by
                  simpa [BviSem.decClock] using targetBodyCode
                refine ⟨targetNext, ?_, finalRelated, noOptimization⟩
                simp only [BviSem.evaluate, targetLookup, targetThunk, findCode, targetLookupCode,
                  List.length_cons, List.length_nil, Nat.reduceAdd, ↓reduceIte, targetNonzero, targetBodyRun]
                cases result with
                | val values => rfl
                | err error =>
                  cases error with
                  | abort reason => rfl
                  | raise payload =>
                    cases payload with
                    | exn exception => rfl
                    | ret values => exact (notReturn values rfl).elim
          · have arityNe : 2 ≠ arity := Ne.symm arityEq
            simp [BviSem.evaluate, lookup, thunkRun, findCode, codeLookup, arityNe] at run
            exact (notTypeError run.1.symm).elim

/-- The raise case simulates the raised expression under the same state and
an environment with optimization disabled. The source scan cannot select a
raise as an optimization candidate. -/
theorem rewriteTail_raise {C F : Type} (body : Bvi.Exp)
    (ih : rewriteTailProperty (C := C) (F := F) [body]) :
    rewriteTailProperty (C := C) (F := F) [.raise body] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  obtain ⟨run, envRelated, stateRelated, types, _, notTypeError⟩ := hyp
  have disabled := envRel_disable ty optimized acc env1 env2 envRelated
  rw [BviSem.evaluate] at run
  cases innerRun : BviSem.evaluate [body] env1 source with
  | mk inner middle =>
    cases inner with
    | err error =>
      simp only [innerRun] at run
      have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have innerHyp : rewriteTailHyp [body] source env1 (.err error) middle false target acc env2 loc ts ty :=
        ⟨innerRun, disabled, stateRelated, types, by simp, ok⟩
      obtain ⟨targetNext, targetRun, targetRelated, _⟩ :=
        ih source env1 (.err error) middle false target acc env2 loc ts ty innerHyp
      have same : (.err error, middle) = (result, sourceNext) := by simpa [innerRun] using run
      cases same
      refine ⟨targetNext, ?_, targetRelated, ?_⟩
      · rw [BviSem.evaluate, targetRun]
      · intro _ op workerLoc code arity required
        obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
        rw [scanExpr_single, scanSing.eq_def] at scan
        simp at scan
    | val values =>
      have innerHyp : rewriteTailHyp [body] source env1 (.val values) middle false target acc env2 loc ts ty :=
        ⟨innerRun, disabled, stateRelated, types, by simp, by simp⟩
      obtain ⟨targetNext, targetRun, targetRelated, _⟩ :=
        ih source env1 (.val values) middle false target acc env2 loc ts ty innerHyp
      refine ⟨targetNext, ?_, ?_, ?_⟩
      · rw [BviSem.evaluate, targetRun]
        simpa [innerRun] using congrArg Prod.fst run
      · have same : middle = sourceNext := by simpa [innerRun] using congrArg Prod.snd run
        simpa [same] using targetRelated
      · intro _ op workerLoc code arity required
        obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
        rw [scanExpr_single, scanSing.eq_def] at scan
        simp at scan

/-- The return case simulates its argument list under the same state and
an environment with optimization disabled. The source scan cannot select a
return as an optimization candidate. -/
theorem rewriteTail_return {C F : Type} (args : List Bvi.Exp)
    (ih : rewriteTailProperty (C := C) (F := F) args) :
    rewriteTailProperty (C := C) (F := F) [.return args] := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  obtain ⟨run, envRelated, stateRelated, types, _, notTypeError⟩ := hyp
  have disabled := envRel_disable ty optimized acc env1 env2 envRelated
  rw [BviSem.evaluate] at run
  cases innerRun : BviSem.evaluate args env1 source with
  | mk inner middle =>
    cases inner with
    | err error =>
      simp only [innerRun] at run
      have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have innerHyp : rewriteTailHyp args source env1 (.err error) middle false target acc env2 loc ts ty :=
        ⟨innerRun, disabled, stateRelated, types, by simp, ok⟩
      obtain ⟨targetNext, targetRun, targetRelated, _⟩ :=
        ih source env1 (.err error) middle false target acc env2 loc ts ty innerHyp
      have same : (.err error, middle) = (result, sourceNext) := by simpa [innerRun] using run
      cases same
      refine ⟨targetNext, ?_, targetRelated, ?_⟩
      · rw [BviSem.evaluate, targetRun]
      · intro _ op workerLoc code arity required
        obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
        rw [scanExpr_single, scanSing.eq_def] at scan
        simp at scan
    | val values =>
      have innerHyp : rewriteTailHyp args source env1 (.val values) middle false target acc env2 loc ts ty :=
        ⟨innerRun, disabled, stateRelated, types, by simp, by simp⟩
      obtain ⟨targetNext, targetRun, targetRelated, _⟩ :=
        ih source env1 (.val values) middle false target acc env2 loc ts ty innerHyp
      refine ⟨targetNext, ?_, ?_, ?_⟩
      · rw [BviSem.evaluate, targetRun]
        simpa [innerRun] using congrArg Prod.fst run
      · have same : middle = sourceNext := by simpa [innerRun] using congrArg Prod.snd run
        simpa [same] using targetRelated
      · intro _ op workerLoc code arity required
        obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
        rw [scanExpr_single, scanSing.eq_def] at scan
        simp at scan

/-- Sequential non-singleton case of the source rewrite simulation. The
singleton optimization condition forces this case to use ordinary simulation
of the head followed by the tail. -/
theorem rewriteTail_cons {C F : Type} (x y : Bvi.Exp) (xs : List Bvi.Exp)
    (headIH : rewriteTailProperty (C := C) (F := F) [x])
    (tailIH : rewriteTailProperty (C := C) (F := F) (y :: xs)) :
    rewriteTailProperty (C := C) (F := F) (x :: y :: xs) := by
  intro source env1 result sourceNext optimized target acc env2 loc ts ty hyp
  obtain ⟨run, envRelated, stateRelated, types, singleton, notTypeError⟩ := hyp
  have disabled : optimized = false := by
    cases optimized with
    | false => rfl
    | true => have impossible := singleton rfl; simp at impossible
  subst optimized
  change BviSem.evaluateTuple (x :: y :: xs, env1, source) = _ at run
  rw [BviSem.evaluateConsCons] at run
  cases headRun : BviSem.evaluate [x] env1 source with
  | mk headResult middle =>
    cases headResult with
    | err error =>
      simp only [BviSem.evaluateTuple, headRun, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have headHyp : rewriteTailHyp [x] source env1 (.err error) middle false target acc env2 loc ts ty :=
        ⟨headRun, envRelated, stateRelated, types, by simp, notTypeError⟩
      obtain ⟨targetNext, targetRun, targetRelated, _⟩ :=
        headIH source env1 (.err error) middle false target acc env2 loc ts ty headHyp
      refine ⟨targetNext, ?_, targetRelated, by simp⟩
      change BviSem.evaluateTuple (x :: y :: xs, env2, target) = _
      rw [BviSem.evaluateConsCons]
      simp [BviSem.evaluateTuple, targetRun]
    | val headValues =>
      obtain ⟨headValue, rfl⟩ := BviSem.evaluate_singleton x env1 source middle headValues headRun
      have headHyp : rewriteTailHyp [x] source env1 (.val [headValue]) middle false target acc env2 loc ts ty :=
        ⟨headRun, envRelated, stateRelated, types, by simp, by simp⟩
      obtain ⟨targetMiddle, targetHead, middleRelated, _⟩ :=
        headIH source env1 (.val [headValue]) middle false target acc env2 loc ts ty headHyp
      cases tailRun : BviSem.evaluate (y :: xs) env1 middle with
      | mk tailResult last =>
        cases tailResult with
        | err error =>
          simp only [BviSem.evaluateTuple, headRun, tailRun, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have tailHyp : rewriteTailHyp (y :: xs) middle env1 (.err error) last false
              targetMiddle acc env2 loc ts ty :=
            ⟨tailRun, envRelated, middleRelated, types, by simp, notTypeError⟩
          obtain ⟨targetNext, targetTail, targetRelated, _⟩ :=
            tailIH middle env1 (.err error) last false targetMiddle acc env2 loc ts ty tailHyp
          refine ⟨targetNext, ?_, targetRelated, by simp⟩
          change BviSem.evaluateTuple (x :: y :: xs, env2, target) = _
          rw [BviSem.evaluateConsCons]
          simp [BviSem.evaluateTuple, targetHead, targetTail]
        | val tailValues =>
          simp only [BviSem.evaluateTuple, headRun, tailRun, Flapjack.holHd,
            Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have tailHyp : rewriteTailHyp (y :: xs) middle env1 (.val tailValues) last false
              targetMiddle acc env2 loc ts ty :=
            ⟨tailRun, envRelated, middleRelated, types, by simp, by simp⟩
          obtain ⟨targetNext, targetTail, targetRelated, _⟩ :=
            tailIH middle env1 (.val tailValues) last false targetMiddle acc env2 loc ts ty tailHyp
          refine ⟨targetNext, ?_, targetRelated, by simp⟩
          change BviSem.evaluateTuple (x :: y :: xs, env2, target) = _
          rw [BviSem.evaluateConsCons]
          simp [BviSem.evaluateTuple, targetHead, targetTail, Flapjack.holHd]

/-- Lists consisting of variables satisfy the complete source-shaped rewrite
simulation, including the original non-type-error condition. -/
theorem rewriteTail_variables {C F : Type} (names : List Nat) :
    rewriteTailProperty (C := C) (F := F) (names.map Bvi.Exp.var) := by
  induction names with
  | nil => exact rewriteTailProperty_nil
  | cons n ns ih =>
    cases ns with
    | nil => exact rewriteTailProperty_var n
    | cons m ms =>
      exact rewriteTail_cons (.var n) (.var m) (ms.map Bvi.Exp.var) (rewriteTailProperty_var n) ih

end Flapjack.Compiler.Backend.BviTailrec
