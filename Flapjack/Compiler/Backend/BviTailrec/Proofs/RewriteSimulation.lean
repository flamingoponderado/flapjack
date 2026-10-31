import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth

/-! Cases of the source tail-recursion rewrite simulation. The evaluator,
source scan and compilation carriers remain subject to HOL review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

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
