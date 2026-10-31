import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation
import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteScan
import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermExtension
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

/-- An accepted pure term has the same value in prefix-related environments
and leaves each related state unchanged. The recursive simulation hypothesis
is the source induction hypothesis for the term expression. -/
theorem term_prefix_simulation {C F : Type} (e : Bvi.Exp) (ctx : List ValueType) (termTy : ValueType)
    (env1 env2 : List Value) (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (loc : Nat) (termIH : rewriteTailProperty (C := C) (F := F) [e])
    (accepted : term ctx termTy e = true) (types : tyRel env1 ctx)
    (prefixRel : env1 <+: env2) (related : stateRel source target) :
    ∃ value, (match termTy with
      | .int => ∃ integer, value = .number integer
      | .list => ∃ ys, valueToList value = some ys
      | .any => True) ∧
      BviSem.evaluate [e] env1 source = (.val [value], source) ∧
      BviSem.evaluate [e] env2 target = (.val [value], target) := by
  obtain ⟨suffix, rfl⟩ := prefixRel
  have extTypes := tyRel_prefix_extend env1 ctx suffix types
  have extAccepted := term_extend e ctx (List.replicate suffix.length .any) termTy accepted
  obtain ⟨value, typed, sourceRun⟩ := term_total (C := Nat × C) (F := F) ctx termTy e env1 accepted types
  obtain ⟨targetValue, _, targetRun⟩ := term_total (C := C) (F := F)
    (ctx ++ List.replicate suffix.length .any) termTy e (env1 ++ suffix) extAccepted extTypes
  have envRelated : envRel .any false 0 env1 (env1 ++ suffix) := ⟨⟨suffix, rfl⟩, by simp⟩
  have hyp : rewriteTailHyp [e] source env1 (.val [value]) source false target 0 (env1 ++ suffix)
      loc ctx .any := ⟨sourceRun source, envRelated, related, types, by simp, by simp⟩
  obtain ⟨targetNext, simulated, _, _⟩ :=
    termIH source env1 (.val [value]) source false target 0 (env1 ++ suffix) loc ctx .any hyp
  have same : ((.val [value] : BviSem.BviResult), targetNext) = (.val [targetValue], target) :=
    simulated.symm.trans (targetRun target)
  cases same
  exact ⟨value, typed, sourceRun source, targetRun target⟩

/-- A scanned term has one common value in prefix-related environments and
leaves every source and target state unchanged. -/
theorem term_prefix_simulation_all {C F : Type} (e : Bvi.Exp) (ctx : List ValueType) (termTy : ValueType)
    (env1 env2 : List Value) (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (loc : Nat) (termIH : rewriteTailProperty (C := C) (F := F) [e])
    (accepted : term ctx termTy e = true) (types : tyRel env1 ctx)
    (prefixRel : env1 <+: env2) (related : stateRel source target) :
    ∃ value, valueMatchesType value termTy ∧
      (∀ s : BviSem.BviState (Nat × C) F, BviSem.evaluate [e] env1 s = (.val [value], s)) ∧
      (∀ s : BviSem.BviState C F, BviSem.evaluate [e] env2 s = (.val [value], s)) := by
  obtain ⟨value, typed, sourceRun, targetRun⟩ :=
    term_prefix_simulation e ctx termTy env1 env2 source target loc termIH accepted types prefixRel related
  obtain ⟨sourceValue, _, sourceAll⟩ := term_total (C := Nat × C) (F := F) ctx termTy e env1 accepted types
  obtain ⟨suffix, rfl⟩ := prefixRel
  have extTypes := tyRel_prefix_extend env1 ctx suffix types
  have extAccepted := term_extend e ctx (List.replicate suffix.length .any) termTy accepted
  obtain ⟨targetValue, _, targetAll⟩ := term_total (C := C) (F := F)
    (ctx ++ List.replicate suffix.length .any) termTy e (env1 ++ suffix) extAccepted extTypes
  have sourceEq : sourceValue = value := by
    have same := (sourceAll source).symm.trans sourceRun
    injection same with valuesEq _
    injection valuesEq with heads
    exact (List.cons.inj heads).1
  have targetEq : targetValue = value := by
    have same := (targetAll target).symm.trans targetRun
    injection same with valuesEq _
    injection valuesEq with heads
    exact (List.cons.inj heads).1
  refine ⟨value, ?_, ?_, ?_⟩
  · cases termTy <;> simp_all [valueMatchesType]
  · simpa [sourceEq] using sourceAll
  · simpa [targetEq] using targetAll

/-- An enabled environment relation supplies a well-typed accumulator value. -/
theorem envRel_accumulator (ty : ValueType) (acc : Nat) (env1 env2 : List Value)
    (related : envRel ty true acc env1 env2) :
    ∃ value, env2[acc]? = some value ∧ valueMatchesType value ty := by
  obtain ⟨_, _, typed⟩ := related.2 rfl
  cases ty with
  | int =>
    obtain ⟨integer, lookup⟩ := typed
    exact ⟨.number integer, lookup, by simp [valueMatchesType]⟩
  | list =>
    obtain ⟨value, values, lookup, decode⟩ := typed
    exact ⟨value, lookup, by simp [valueMatchesType, decode]⟩
  | any => exact typed.elim

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

/-- Applying an operator with a state-preserving left operand first evaluates
the other operand and dispatches on the resulting values. -/
theorem evaluate_applyOp_pureLeft {C F : Type} (op : AssocOp) (pure : Bvi.Exp)
    (body : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (value : Value) (pureRun : BviSem.evaluate [pure] env state = (.val [value], state)) :
    BviSem.evaluate [applyOp op pure body] env state =
      match BviSem.evaluate [body] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match BviSem.doApp (toOp op) (values.reverse ++ [value]) next with
        | .err error => (.err error, next)
        | .val (result, last) => (.val [result], last) := by
  have listRun : BviSem.evaluate [pure, body] env state =
      match BviSem.evaluate [body] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => (.val (value :: values), next) := by
    have h := BviSem.evaluateConsCons pure body [] env state
    simp only [BviSem.evaluateTuple, pureRun, Flapjack.holHd] at h
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
  apply evaluate_applyOp_pureLeft op (.var acc) body env state value
  simp [BviSem.evaluate, lookup]

/-- Evaluating a checked pure operand and the current accumulator yields the
same updated, well-typed accumulator used by the worker call. -/
theorem evaluate_accumulator_update {C F : Type} (op : AssocOp) (pure : Bvi.Exp)
    (ctx : List ValueType) (loc acc : Nat) (env1 env2 : List Value)
    (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (termIH : rewriteTailProperty (C := C) (F := F) [pure])
    (notNoop : op ≠ .noop) (accepted : term ctx (opType op) pure = true)
    (types : tyRel env1 ctx) (envRelated : envRel (opType op) true acc env1 env2)
    (related : stateRel source target) :
    ∃ pureValue oldValue newValue,
      BviSem.evaluate [pure] env1 source = (.val [pureValue], source) ∧
      BviSem.evaluate [pure] env2 target = (.val [pureValue], target) ∧
      env2[acc]? = some oldValue ∧
      accumulatorApply op [pureValue, oldValue] = some newValue ∧
      valueMatchesType newValue (opType op) ∧
      BviSem.evaluate [applyOp op (.var acc) pure] env2 target = (.val [newValue], target) := by
  obtain ⟨pureValue, pureTyped, sourceRun, targetRun⟩ :=
    term_prefix_simulation pure ctx (opType op) env1 env2 source target loc termIH accepted types envRelated.1 related
  obtain ⟨oldValue, lookup, oldTyped⟩ := envRel_accumulator (opType op) acc env1 env2 envRelated
  have pureTyped' : valueMatchesType pureValue (opType op) := by
    cases op <;> simp_all [opType, valueMatchesType]
  obtain ⟨newValue, applied, newTyped⟩ := accumulator_typed op pureValue oldValue notNoop pureTyped' oldTyped
  refine ⟨pureValue, oldValue, newValue, sourceRun, targetRun, lookup, applied, newTyped, ?_⟩
  rw [evaluate_applyOp_var op acc pure env2 target oldValue lookup, targetRun]
  simp [doApp_toOp_pure, applied]

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

/-- Swapping a pure operand across another expression preserves evaluation
for the commutative accumulator operators, including propagated errors. -/
theorem evaluate_applyOp_swap_pure {C F : Type} (op : AssocOp) (pure other : Bvi.Exp)
    (env : List Value) (state : BviSem.BviState C F) (value : Value)
    (notNoop : op ≠ .noop) (notAppend : op ≠ .append)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [value], s)) :
    BviSem.evaluate [applyOp op pure other] env state =
      BviSem.evaluate [applyOp op other pure] env state := by
  have leftList := BviSem.evaluateConsCons pure other [] env state
  simp only [BviSem.evaluateTuple, pureRun state, Flapjack.holHd] at leftList
  have rightList := BviSem.evaluateConsCons other pure [] env state
  simp only [BviSem.evaluateTuple] at rightList
  cases otherRun : BviSem.evaluate [other] env state with
  | mk result middle =>
    cases result with
    | err error =>
      simp only [otherRun] at leftList rightList
      simp only [applyOp]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, leftList]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, rightList]
    | val values =>
      obtain ⟨otherValue, rfl⟩ := BviSem.evaluate_singleton other env state middle values otherRun
      simp only [otherRun, pureRun middle, Flapjack.holHd] at leftList rightList
      simp only [applyOp]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, leftList]
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, rightList]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [doApp_toOp_pure, doApp_toOp_pure]
      rw [accumulator_commutative_all op value otherValue notNoop notAppend]

/-- The source candidate check preserves evaluation: its only possible
change swaps a pure operand with a recursive call for a commutative operator. -/
theorem checkOp_evaluate {C F : Type} (ctx : List ValueType) (op : AssocOp) (loc : Nat)
    (e checked : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (types : tyRel env ctx) (check : checkOp ctx op loc e = some checked) :
    BviSem.evaluate [e] env state = BviSem.evaluate [checked] env state := by
  obtain ⟨recursive, pure, _, termOk, checkedShape, notNoop, original⟩ :=
    checkOp_candidate ctx op loc e checked check
  obtain ⟨value, _, pureRun⟩ := term_total (C := C) (F := F) ctx (opType op) pure env termOk types
  rw [checkedShape]
  rcases original with direct | ⟨notAppend, swapped⟩
  · rw [direct]
  · rw [swapped]
    exact (evaluate_applyOp_swap_pure op pure recursive env state value notNoop notAppend pureRun).symm

/-- Reassociate a typed pure operand into the current accumulator before
evaluating the recursive operand. Errors and state changes of that operand
are preserved. -/
theorem evaluate_applyOp_reassociate {C F : Type} (op : AssocOp) (acc : Nat)
    (pure other : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (pureValue oldValue : Value) (notNoop : op ≠ .noop)
    (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op))
    (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s)) :
    BviSem.evaluate [applyOp op (.var acc) (applyOp op pure other)] env state =
      BviSem.evaluate [applyOp op (applyOp op (.var acc) pure) other] env state := by
  obtain ⟨newValue, update, _⟩ := accumulator_typed op pureValue oldValue notNoop pureTyped oldTyped
  have updateRun : BviSem.evaluate [applyOp op (.var acc) pure] env state = (.val [newValue], state) := by
    rw [evaluate_applyOp_var op acc pure env state oldValue lookup, pureRun state]
    simp [doApp_toOp_pure, update]
  rw [evaluate_applyOp_var op acc (applyOp op pure other) env state oldValue lookup]
  rw [evaluate_applyOp_pureLeft op pure other env state pureValue (pureRun state)]
  rw [evaluate_applyOp_pureLeft op (applyOp op (.var acc) pure) other env state newValue updateRun]
  cases otherRun : BviSem.evaluate [other] env state with
  | mk result middle =>
    cases result with
    | err error => rfl
    | val values =>
      obtain ⟨otherValue, rfl⟩ := BviSem.evaluate_singleton other env state middle values otherRun
      obtain ⟨combined, combinedEq, assoc⟩ :=
        accumulator_associative_partial op otherValue pureValue oldValue notNoop pureTyped oldTyped
      have sameUpdate : combined = newValue := by rw [update] at combinedEq; simpa using combinedEq.symm
      subst combined
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, doApp_toOp_pure]
      cases first : accumulatorApply op [otherValue, pureValue] with
      | none =>
        simp only [first] at assoc
        rw [← assoc]
        rfl
      | some firstValue =>
        simp only [first] at assoc
        rw [← assoc]
        cases final : accumulatorApply op [firstValue, oldValue] <;> rfl

/-- Appending the accumulator update to worker arguments preserves argument
errors and appends the same well-typed value after successful evaluation. -/
theorem evaluate_worker_arguments {C F : Type} (op : AssocOp) (acc : Nat)
    (pure : Bvi.Exp) (args : List Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (pureValue oldValue : Value) (notNoop : op ≠ .noop)
    (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op))
    (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s)) :
    ∃ newValue, accumulatorApply op [pureValue, oldValue] = some newValue ∧
      valueMatchesType newValue (opType op) ∧
      BviSem.evaluate (args ++ [applyOp op (.var acc) pure]) env state =
        match BviSem.evaluate args env state with
        | (.err error, next) => (.err error, next)
        | (.val values, next) => (.val (values ++ [newValue]), next) := by
  obtain ⟨newValue, update, typed⟩ := accumulator_typed op pureValue oldValue notNoop pureTyped oldTyped
  have updateRun (s : BviSem.BviState C F) :
      BviSem.evaluate [applyOp op (.var acc) pure] env s = (.val [newValue], s) := by
    rw [evaluate_applyOp_var op acc pure env s oldValue lookup, pureRun s]
    simp [doApp_toOp_pure, update]
  refine ⟨newValue, update, typed, ?_⟩
  have append := BviSem.evaluateAppend args env state [applyOp op (.var acc) pure]
  simp only [BviSem.evaluateTuple] at append
  rw [append]
  cases run : BviSem.evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values => simp [updateRun]

/-- Applying an accumulator cannot introduce a return exception that was
absent from the evaluated body. -/
theorem evaluate_applyOp_noReturn {C F : Type} (op : AssocOp) (acc : Nat) (body : Bvi.Exp)
    (env : List Value) (state bodyNext next : BviSem.BviState C F)
    (value : Value) (bodyResult result : BviSem.BviResult)
    (lookup : env[acc]? = some value)
    (bodyRun : BviSem.evaluate [body] env state = (bodyResult, bodyNext))
    (noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)))
    (run : BviSem.evaluate [applyOp op (.var acc) body] env state = (result, next)) :
    ∀ values, result ≠ .err (.raise (.ret values)) := by
  rw [evaluate_applyOp_var op acc body env state value lookup, bodyRun] at run
  cases bodyResult with
  | err error =>
    simp only at run
    have same : result = .err error := (congrArg Prod.fst run).symm
    simpa [same] using noReturn
  | val values =>
    simp only [doApp_toOp_pure] at run
    cases found : accumulatorApply op (values.reverse ++ [value]) with
    | none =>
      simp [found] at run
      intro returned bad
      rw [← run.1] at bad
      cases bad
    | some output =>
      simp [found] at run
      intro returned bad
      rw [← run.1] at bad
      cases bad

/-- Applying the same accumulator to equal expression results yields the
same result in either state and leaves each expression's final state intact. -/
theorem evaluate_applyOp_matching {C F D G : Type} (op : AssocOp)
    (pure1 body1 pure2 body2 : Bvi.Exp) (env1 env2 : List Value)
    (state1 next1 : BviSem.BviState C F) (state2 next2 : BviSem.BviState D G)
    (value : Value) (bodyResult : BviSem.BviResult)
    (pureRun1 : BviSem.evaluate [pure1] env1 state1 = (.val [value], state1))
    (pureRun2 : BviSem.evaluate [pure2] env2 state2 = (.val [value], state2))
    (bodyRun1 : BviSem.evaluate [body1] env1 state1 = (bodyResult, next1))
    (bodyRun2 : BviSem.evaluate [body2] env2 state2 = (bodyResult, next2)) :
    ∃ result, BviSem.evaluate [applyOp op pure1 body1] env1 state1 = (result, next1) ∧
      BviSem.evaluate [applyOp op pure2 body2] env2 state2 = (result, next2) := by
  rw [evaluate_applyOp_pureLeft op pure1 body1 env1 state1 value pureRun1, bodyRun1]
  rw [evaluate_applyOp_pureLeft op pure2 body2 env2 state2 value pureRun2, bodyRun2]
  cases bodyResult with
  | err error => exact ⟨.err error, rfl, rfl⟩
  | val values =>
    cases found : accumulatorApply op (values.reverse ++ [value]) with
    | none => exact ⟨.err (.abort .typeError), by simp [doApp_toOp_pure, found],
        by simp [doApp_toOp_pure, found]⟩
    | some output => exact ⟨.val [output], by simp [doApp_toOp_pure, found],
        by simp [doApp_toOp_pure, found]⟩

/-- An accumulator operation with a pure first operand leaves the final state
at the state produced by its second operand, even on primitive failure. -/
theorem evaluate_applyOp_pure_state {C F : Type} (op : AssocOp) (pure body : Bvi.Exp)
    (env : List Value) (state bodyNext final : BviSem.BviState C F)
    (value : Value) (bodyResult result : BviSem.BviResult)
    (pureRun : BviSem.evaluate [pure] env state = (.val [value], state))
    (bodyRun : BviSem.evaluate [body] env state = (bodyResult, bodyNext))
    (run : BviSem.evaluate [applyOp op pure body] env state = (result, final)) : final = bodyNext := by
  rw [evaluate_applyOp_pureLeft op pure body env state value pureRun, bodyRun] at run
  cases bodyResult with
  | err error => exact (congrArg Prod.snd run).symm
  | val values =>
    simp only [doApp_toOp_pure] at run
    cases found : accumulatorApply op (values.reverse ++ [value]) with
    | none => simpa [found] using (congrArg Prod.snd run).symm
    | some output => simpa [found] using (congrArg Prod.snd run).symm

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

/-- A known accumulator can be applied after the selected conditional branch.
Condition errors and non-boolean values are propagated unchanged. -/
theorem evaluate_applyOp_if {C F : Type} (op : AssocOp) (acc : Nat)
    (cond yes no : Bvi.Exp) (env : List Value) (state : BviSem.BviState C F)
    (value : Value) (lookup : env[acc]? = some value) :
    BviSem.evaluate [applyOp op (.var acc) (.ifThenElse cond yes no)] env state =
      BviSem.evaluate [.ifThenElse cond (applyOp op (.var acc) yes)
        (applyOp op (.var acc) no)] env state := by
  rw [evaluate_applyOp_var op acc (.ifThenElse cond yes no) env state value lookup]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate]
  cases guardRun : BviSem.evaluate [cond] env state with
  | mk guardResult middle =>
    cases guardResult with
    | err error => simp
    | val values =>
      obtain ⟨guardValue, rfl⟩ := BviSem.evaluate_singleton cond env state middle values guardRun
      change (match (match asBool guardValue with
          | none => ((.err (.abort .typeError) : BviSem.BviResult), middle)
          | some true => BviSem.evaluate [yes] env middle
          | some false => BviSem.evaluate [no] env middle) with
        | (.err error, next) => (.err error, next)
        | (.val values, next) =>
          match BviSem.doApp (toOp op) (values.reverse ++ [value]) next with
          | .err error => (.err error, next)
          | .val (result, last) => (.val [result], last)) =
        (match asBool guardValue with
          | none => ((.err (.abort .typeError) : BviSem.BviResult), middle)
          | some true => BviSem.evaluate [applyOp op (.var acc) yes] env middle
          | some false => BviSem.evaluate [applyOp op (.var acc) no] env middle)
      cases truth : asBool guardValue with
      | none => rfl
      | some flag =>
        cases flag with
        | false => exact (evaluate_applyOp_var op acc no env middle value lookup).symm
        | true => exact (evaluate_applyOp_var op acc yes env middle value lookup).symm

/-- If recursive-call argument evaluation fails, both the worker call and
the original accumulator expression propagate the same error and state. -/
theorem evaluate_worker_call_argument_error {C F : Type}
    (loc workerLoc ticks acc : Nat) (op : AssocOp) (pure : Bvi.Exp) (args : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (pureValue oldValue : Value)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (notNoop : op ≠ .noop) (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s))
    (argsRun : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env state = (.err error, next) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env state = (.err error, next) := by
  obtain ⟨_, _, _, extendedRun⟩ :=
    evaluate_worker_arguments op acc pure args env state pureValue oldValue notNoop pureTyped oldTyped lookup pureRun
  have workerArgs : BviSem.evaluate (args ++ [applyOp op (.var acc) pure]) env state = (.err error, next) := by
    rw [extendedRun, argsRun]
  have callRun : BviSem.evaluate [.call ticks (some loc) args none] env state = (.err error, next) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rfl
  constructor
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate, workerArgs]
    rfl
  · rw [evaluate_applyOp_var op acc (applyOp op pure (.call ticks (some loc) args none)) env state oldValue lookup]
    rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env state pureValue (pureRun state)]
    rw [callRun]

/-- If the call clock is exhausted after evaluating arguments, the original
call and the rewritten worker call both time out in the same state. -/
theorem evaluate_worker_call_timeout {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body originalBody pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env : List Value) (state middle : BviSem.BviState C F)
    (callArgs : List Value) (pureValue oldValue : Value)
    (notNoop : op ≠ .noop) (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s))
    (argsRun : BviSem.evaluate args env state = (.val callArgs, middle))
    (lengthEq : callArgs.length = arity)
    (originalCode : sptLookup loc middle.code = some (arity, originalBody))
    (optimized : optimizedCode loc arity body workerLoc middle.code op)
    (timeout : middle.clock < ticks + 1) :
    BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env state = (.err (.abort .timeoutError), { middle with clock := 0 }) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env state = (.err (.abort .timeoutError), { middle with clock := 0 }) := by
  obtain ⟨newValue, _, _, extendedRun⟩ :=
    evaluate_worker_arguments op acc pure args env state pureValue oldValue notNoop pureTyped oldTyped lookup pureRun
  have workerArgs : BviSem.evaluate (args ++ [applyOp op (.var acc) pure]) env state =
      (.val (callArgs ++ [newValue]), middle) := by rw [extendedRun, argsRun]
  have workerCode := optimizedCode_find_worker loc arity body workerLoc middle.code op callArgs newValue optimized lengthEq
  have callRun : BviSem.evaluate [.call ticks (some loc) args none] env state =
      (.err (.abort .timeoutError), { middle with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [findCode, originalCode, lengthEq, timeout]
  constructor
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate, workerArgs]
    simp [workerCode, timeout]
  · rw [evaluate_applyOp_var op acc (applyOp op pure (.call ticks (some loc) args none)) env state oldValue lookup]
    rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env state pureValue (pureRun state)]
    rw [callRun]

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

/-- A direct recursive call through related code yields the same non-return
callee result and a related final state. -/
theorem evaluate_related_direct_call {C F : Type} (loc arity ticks : Nat)
    (body : Bvi.Exp) (args : List Bvi.Exp) (env : List Value)
    (sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (target targetMiddle : BviSem.BviState C F) (values : List Value) (result : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) values result
        sourceNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] (BviSem.decClock (ticks + 1) sourceMiddle) values result
        sourceNext optimized target acc env2 loc ts ty)
    (related : stateRel sourceMiddle targetMiddle) (lengthEq : values.length = arity)
    (sourceCode : sptLookup loc sourceMiddle.code = some (arity, body))
    (argsRun : BviSem.evaluate args env target = (.val values, targetMiddle))
    (enoughClock : ticks + 1 ≤ sourceMiddle.clock)
    (bodyRun : BviSem.evaluate [body] values (BviSem.decClock (ticks + 1) sourceMiddle) =
      (result, sourceNext))
    (notTypeError : result ≠ .err (.abort .typeError))
    (noReturn : ∀ values, result ≠ .err (.raise (.ret values))) :
    ∃ targetNext, BviSem.evaluate [.call ticks (some loc) args none] env target = (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  have decRelated := stateRel_decClock sourceMiddle targetMiddle (ticks + 1) related
  have decCode : sptLookup loc (BviSem.decClock (ticks + 1) sourceMiddle).code = some (arity, body) := by
    simpa [BviSem.decClock] using sourceCode
  obtain ⟨compiled, targetNext, targetCode, targetBody, finalRelated⟩ :=
    evaluate_related_callee loc arity body values (BviSem.decClock (ticks + 1) sourceMiddle)
      sourceNext (BviSem.decClock (ticks + 1) targetMiddle) result bodyIH decRelated lengthEq decCode bodyRun notTypeError
  have lookup : sptLookup loc targetMiddle.code = some (arity, compiled) := by
    simpa [BviSem.decClock] using targetCode
  have targetEnough : ¬targetMiddle.clock < ticks + 1 := by
    have clocks := (stateRel_const sourceMiddle targetMiddle related).2.1
    omega
  refine ⟨targetNext, ?_, finalRelated⟩
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, findCode,
    lookup, lengthEq, targetEnough, BviSem.fixClock_evaluate]
  rw [targetBody]
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort reason => rfl
    | raise payload =>
      cases payload with
      | exn exception => rfl
      | ret values => exact (noReturn values rfl).elim

/-- A recursive worker body agrees with applying its incoming accumulator to
the original body. The hypothesis is the smaller-clock body induction case. -/
theorem evaluate_optimized_worker_body {C F : Type} (loc arity workerLoc : Nat)
    (body : Bvi.Exp) (op : AssocOp) (args : List Value) (accumulator : Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (result : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] source args result sourceNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] source args result sourceNext optimized target acc env2 loc ts ty)
    (related : stateRel source target) (lengthEq : args.length = arity)
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc target.code op)
    (typed : valueMatchesType accumulator (opType op))
    (run : BviSem.evaluate [body] args source = (result, sourceNext))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ result' t1 t2,
      BviSem.evaluate [(rewriteSource loc workerLoc op arity (List.replicate arity .any) body).2]
        (args ++ [accumulator]) target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var arity) body] (args ++ [accumulator]) target = (result', t2) ∧
      stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  have check : checkExpOriginal loc arity body = some op := by
    obtain ⟨_, _, _, check, _, _⟩ := optimized
    exact check
  obtain ⟨outCtx, scanTy, branch, scan, _, notAny, notNoop⟩ :=
    checkExpOriginal_scan loc arity body op check
  have envRelated : envRel (opType op) true arity args (args ++ [accumulator]) := by
    simpa [lengthEq] using envRel_worker op args accumulator notNoop typed
  have types : tyRel args (List.replicate arity .any) := by
    simpa [lengthEq] using tyRel_replicate_any args
  have hyp : rewriteTailHyp [body] source args result sourceNext true target arity (args ++ [accumulator])
      loc (List.replicate arity .any) (opType op) :=
    ⟨run, envRelated, related, types, by simp, notTypeError⟩
  obtain ⟨_, _, _, optRun⟩ :=
    bodyIH true target arity (args ++ [accumulator]) loc (List.replicate arity .any) (opType op) hyp
  have req : sptLookup loc source.code = some (arity, body) ∧
      optimizedCode loc arity body workerLoc target.code op ∧ opType op = opType op ∧
      (∃ op1 outCtx resultTy branch,
        scanExpr (List.replicate arity .any) loc [body] = [(outCtx, resultTy, branch, some op1)] ∧
        resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) :=
    ⟨sourceCode, optimized, rfl, op, outCtx, scanTy, branch, scan, notAny, notNoop, rfl⟩
  obtain ⟨result', t1, t2, workerRun, appliedRun, rel1, rel2⟩ :=
    optRun rfl op workerLoc body arity (by simpa only [List.headD_cons] using req)
  exact ⟨result', t1, t2, by simpa only [List.headD_cons] using workerRun,
    by simpa only [List.headD_cons] using appliedRun, rel1, rel2⟩

/-- A rewritten worker call evaluates its extended arguments and executes the
worker body obtained from the smaller-clock induction hypothesis. -/
theorem evaluate_optimized_worker_call {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env : List Value) (target targetMiddle : BviSem.BviState C F)
    (sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (callArgs : List Value) (pureValue oldValue : Value) (bodyResult : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceNext optimized target acc env2 loc ts ty)
    (related : stateRel sourceMiddle targetMiddle) (lengthEq : callArgs.length = arity)
    (sourceCode : sptLookup loc sourceMiddle.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc targetMiddle.code op)
    (notNoop : op ≠ .noop) (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s))
    (argsRun : BviSem.evaluate args env target = (.val callArgs, targetMiddle))
    (enoughClock : ticks + 1 ≤ sourceMiddle.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) sourceMiddle) =
      (bodyResult, sourceNext))
    (notTypeError : bodyResult ≠ .err (.abort .typeError))
    (noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values))) :
    ∃ newValue result' t1 t2,
      accumulatorApply op [pureValue, oldValue] = some newValue ∧
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var arity) body] (callArgs ++ [newValue])
        (BviSem.decClock (ticks + 1) targetMiddle) = (result', t2) ∧
      stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨newValue, update, typed, extendedRun⟩ :=
    evaluate_worker_arguments op acc pure args env target pureValue oldValue notNoop pureTyped oldTyped lookup pureRun
  have workerArgs : BviSem.evaluate (args ++ [applyOp op (.var acc) pure]) env target =
      (.val (callArgs ++ [newValue]), targetMiddle) := by rw [extendedRun, argsRun]
  have found := optimizedCode_find_worker loc arity body workerLoc targetMiddle.code op callArgs newValue
    optimized lengthEq
  have clockMatch := (stateRel_const sourceMiddle targetMiddle related).2.1
  have notTimeout : ¬targetMiddle.clock < ticks + 1 := by omega
  have decremented := stateRel_decClock sourceMiddle targetMiddle (ticks + 1) related
  have decSourceCode : sptLookup loc (BviSem.decClock (ticks + 1) sourceMiddle).code = some (arity, body) := by
    simpa [BviSem.decClock] using sourceCode
  have decOptimized : optimizedCode loc arity body workerLoc (BviSem.decClock (ticks + 1) targetMiddle).code op := by
    simpa [BviSem.decClock] using optimized
  obtain ⟨result', t1, t2, workerRun, appliedRun, rel1, rel2⟩ :=
    evaluate_optimized_worker_body loc arity workerLoc body op callArgs newValue
      (BviSem.decClock (ticks + 1) sourceMiddle) sourceNext (BviSem.decClock (ticks + 1) targetMiddle)
      bodyResult bodyIH decremented lengthEq decSourceCode decOptimized typed bodyRun notTypeError
  have envRelated : envRel (opType op) true arity callArgs (callArgs ++ [newValue]) := by
    simpa [lengthEq] using envRel_worker op callArgs newValue notNoop typed
  have types : tyRel callArgs (List.replicate arity .any) := by
    simpa [lengthEq] using tyRel_replicate_any callArgs
  have hyp : rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult sourceNext
      true (BviSem.decClock (ticks + 1) targetMiddle) arity (callArgs ++ [newValue]) loc
      (List.replicate arity .any) (opType op) :=
    ⟨bodyRun, envRelated, decremented, types, by simp, notTypeError⟩
  obtain ⟨ordinaryNext, ordinaryRun, _, _⟩ :=
    bodyIH true (BviSem.decClock (ticks + 1) targetMiddle) arity (callArgs ++ [newValue]) loc
      (List.replicate arity .any) (opType op) hyp
  have workerLookup : (callArgs ++ [newValue])[arity]? = some newValue := by simp [← lengthEq]
  have resultNoReturn := evaluate_applyOp_noReturn op arity body (callArgs ++ [newValue])
    (BviSem.decClock (ticks + 1) targetMiddle) ordinaryNext t2 newValue bodyResult result'
    workerLookup ordinaryRun noReturn appliedRun
  refine ⟨newValue, result', t1, t2, update, ?_, appliedRun, rel1, rel2⟩
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, workerArgs]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    found, notTimeout, BviSem.fixClock_evaluate]
  rw [workerRun]
  cases result' with
  | val values => rfl
  | err error =>
    cases error with
    | abort reason => rfl
    | raise payload =>
      cases payload with
      | exn exception => rfl
      | ret values => exact (resultNoReturn values rfl).elim

/-- Successful recursive-candidate calls agree with the original expression
with its accumulator applied, and both final states remain related. -/
theorem evaluate_worker_candidate_success {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env : List Value) (target targetMiddle : BviSem.BviState C F)
    (sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (callArgs : List Value) (pureValue oldValue : Value) (bodyResult : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceNext optimized target acc env2 loc ts ty)
    (related : stateRel sourceMiddle targetMiddle) (lengthEq : callArgs.length = arity)
    (sourceCode : sptLookup loc sourceMiddle.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc targetMiddle.code op)
    (notNoop : op ≠ .noop) (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env[acc]? = some oldValue)
    (pureRun : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env s = (.val [pureValue], s))
    (argsRun : BviSem.evaluate args env target = (.val callArgs, targetMiddle))
    (enoughClock : ticks + 1 ≤ sourceMiddle.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) sourceMiddle) =
      (bodyResult, sourceNext))
    (notTypeError : bodyResult ≠ .err (.abort .typeError))
    (noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values))) :
    ∃ result' t1 t2,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env target = (result', t2) ∧ stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨newValue, result', t1, t2, update, workerRun, appliedRun, rel1, _⟩ :=
    evaluate_optimized_worker_call loc arity workerLoc ticks acc body pure op args env target targetMiddle
      sourceMiddle sourceNext callArgs pureValue oldValue bodyResult bodyIH related lengthEq sourceCode
      optimized notNoop pureTyped oldTyped lookup pureRun argsRun enoughClock bodyRun notTypeError noReturn
  obtain ⟨originalNext, originalRun, originalRelated⟩ :=
    evaluate_related_direct_call loc arity ticks body args env sourceMiddle sourceNext target targetMiddle
      callArgs bodyResult bodyIH related lengthEq sourceCode argsRun enoughClock bodyRun notTypeError noReturn
  have typed : valueMatchesType newValue (opType op) := by
    obtain ⟨value, valueRun, valueTyped⟩ := accumulator_typed op pureValue oldValue notNoop pureTyped oldTyped
    rw [update] at valueRun
    cases valueRun
    exact valueTyped
  have decRelated := stateRel_decClock sourceMiddle targetMiddle (ticks + 1) related
  have envRelated : envRel (opType op) true arity callArgs (callArgs ++ [newValue]) := by
    simpa [lengthEq] using envRel_worker op callArgs newValue notNoop typed
  have types : tyRel callArgs (List.replicate arity .any) := by
    simpa [lengthEq] using tyRel_replicate_any callArgs
  have hyp : rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult sourceNext
      true (BviSem.decClock (ticks + 1) targetMiddle) arity (callArgs ++ [newValue]) loc
      (List.replicate arity .any) (opType op) :=
    ⟨bodyRun, envRelated, decRelated, types, by simp, notTypeError⟩
  obtain ⟨bodyTargetNext, bodyTargetRun, _, _⟩ :=
    bodyIH true (BviSem.decClock (ticks + 1) targetMiddle) arity (callArgs ++ [newValue]) loc
      (List.replicate arity .any) (opType op) hyp
  have workerVar : BviSem.evaluate [.var arity] (callArgs ++ [newValue])
      (BviSem.decClock (ticks + 1) targetMiddle) = (.val [newValue], BviSem.decClock (ticks + 1) targetMiddle) := by
    simp [BviSem.evaluate, ← lengthEq]
  have updatedRun : BviSem.evaluate [applyOp op (.var acc) pure] env target = (.val [newValue], target) := by
    rw [evaluate_applyOp_var op acc pure env target oldValue lookup, pureRun target]
    simp [doApp_toOp_pure, update]
  obtain ⟨matchingResult, workerApplied, originalApplied⟩ :=
    evaluate_applyOp_matching op (.var arity) body (applyOp op (.var acc) pure)
      (.call ticks (some loc) args none) (callArgs ++ [newValue]) env
      (BviSem.decClock (ticks + 1) targetMiddle) bodyTargetNext target originalNext newValue bodyResult
      workerVar updatedRun bodyTargetRun originalRun
  have sameResult : result' = matchingResult := by
    rw [appliedRun] at workerApplied
    exact congrArg Prod.fst workerApplied
  subst matchingResult
  refine ⟨result', t1, originalNext, workerRun, ?_, rel1, originalRelated⟩
  rw [evaluate_applyOp_reassociate op acc pure (.call ticks (some loc) args none) env target
    pureValue oldValue notNoop pureTyped oldTyped lookup pureRun]
  exact originalApplied

/-- The successful recursive-candidate worker simulation relates its final
states to the complete source accumulator operation, not just the callee. -/
theorem evaluate_worker_candidate_operation {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env1 env2 : List Value) (source : BviSem.BviState (Nat × C) F)
    (sourceMiddle sourceBodyNext sourceNext : BviSem.BviState (Nat × C) F)
    (target targetMiddle : BviSem.BviState C F) (callArgs : List Value)
    (pureValue oldValue : Value) (bodyResult sourceResult : BviSem.BviResult)
    (bodyIH : ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
      rewriteTailHyp [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceBodyNext optimized target acc env2 loc ts ty →
      rewriteTailPost [body] (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult
        sourceBodyNext optimized target acc env2 loc ts ty)
    (related : stateRel sourceMiddle targetMiddle) (lengthEq : callArgs.length = arity)
    (sourceCode : sptLookup loc sourceMiddle.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc targetMiddle.code op)
    (notNoop : op ≠ .noop) (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env2[acc]? = some oldValue)
    (pureSource : BviSem.evaluate [pure] env1 source = (.val [pureValue], source))
    (pureTarget : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env2 s = (.val [pureValue], s))
    (argsTarget : BviSem.evaluate args env2 target = (.val callArgs, targetMiddle))
    (enoughClock : ticks + 1 ≤ sourceMiddle.clock)
    (bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) sourceMiddle) =
      (bodyResult, sourceBodyNext))
    (callSource : BviSem.evaluate [.call ticks (some loc) args none] env1 source =
      (bodyResult, sourceBodyNext))
    (operationSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext))
    (notTypeError : bodyResult ≠ .err (.abort .typeError))
    (noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values))) :
    ∃ result' t1 t2,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env2 target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env2 target = (result', t2) ∧ stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  have finalState : sourceNext = sourceBodyNext :=
    evaluate_applyOp_pure_state op pure (.call ticks (some loc) args none) env1 source sourceBodyNext
      sourceNext pureValue bodyResult sourceResult pureSource callSource operationSource
  subst sourceNext
  exact evaluate_worker_candidate_success loc arity workerLoc ticks acc body pure op args env2 target targetMiddle
    sourceMiddle sourceBodyNext callArgs pureValue oldValue bodyResult bodyIH related lengthEq sourceCode optimized
    notNoop pureTyped oldTyped lookup pureTarget argsTarget enoughClock bodyRun notTypeError noReturn

/-- When source call arguments fail, the candidate worker and the original
accumulator expression propagate that failure to states related to the full
source operation's final state. -/
theorem evaluate_worker_candidate_argument_error {C F : Type}
    (loc workerLoc ticks acc : Nat) (op : AssocOp) (pure : Bvi.Exp) (args : List Bvi.Exp)
    (env1 env2 : List Value) (source sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (ctx : List ValueType) (ty : ValueType)
    (pureValue oldValue : Value) (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (sourceResult : BviSem.BviResult)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (envRelated : envRel ty true acc env1 env2) (related : stateRel source target)
    (types : tyRel env1 ctx) (notNoop : op ≠ .noop)
    (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env2[acc]? = some oldValue)
    (pureSource : BviSem.evaluate [pure] env1 source = (.val [pureValue], source))
    (pureTarget : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env2 s = (.val [pureValue], s))
    (argsSource : BviSem.evaluate args env1 source = (.err error, sourceMiddle))
    (operationSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext))
    (notTypeError : sourceResult ≠ .err (.abort .typeError)) :
    ∃ targetNext,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env2 target = (.err error, targetNext) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env2 target = (.err error, targetNext) ∧ stateRel sourceNext targetNext := by
  have sourceCall : BviSem.evaluate [.call ticks (some loc) args none] env1 source =
      (.err error, sourceMiddle) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsSource]
    rfl
  have sourceOperation : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (.err error, sourceMiddle) := by
    rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env1 source pureValue pureSource,
      sourceCall]
  have same := sourceOperation.symm.trans operationSource
  have errorOk : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
    intro bad
    apply notTypeError
    exact (congrArg Prod.fst same).symm.trans bad
  have argsHyp : rewriteTailHyp args source env1 (.err error) sourceMiddle false target acc env2 loc ctx ty :=
    ⟨argsSource, envRel_disable ty true acc env1 env2 envRelated, related, types, by simp, errorOk⟩
  obtain ⟨targetNext, targetArgs, finalRelated, _⟩ :=
    argsIH source env1 (.err error) sourceMiddle false target acc env2 loc ctx ty argsHyp
  obtain ⟨workerRun, originalRun⟩ :=
    evaluate_worker_call_argument_error loc workerLoc ticks acc op pure args env2 target targetNext
      pureValue oldValue error notNoop pureTyped oldTyped lookup pureTarget targetArgs
  have stateEq : sourceMiddle = sourceNext := congrArg Prod.snd same
  exact ⟨targetNext, workerRun, originalRun, by simpa [stateEq] using finalRelated⟩

/-- If a direct call's arguments evaluate successfully and its enclosing pure
accumulator operation does not type-error, the installed function's arity
matches the argument list. -/
theorem evaluate_candidate_arity {C F : Type}
    (loc arity ticks : Nat) (body pure : Bvi.Exp) (op : AssocOp) (args : List Bvi.Exp)
    (env : List Value) (source middle next : BviSem.BviState C F)
    (values : List Value) (pureValue : Value) (result : BviSem.BviResult)
    (pureRun : BviSem.evaluate [pure] env source = (.val [pureValue], source))
    (argsRun : BviSem.evaluate args env source = (.val values, middle))
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (run : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env source =
      (result, next)) (notTypeError : result ≠ .err (.abort .typeError)) : values.length = arity := by
  have found := evaluate_lookup_preserved args env source middle (.val values) loc arity body argsRun sourceCode
  by_contra bad
  have callRun : BviSem.evaluate [.call ticks (some loc) args none] env source =
      (.err (.abort .typeError), middle) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [findCode, found, bad]
  have operationRun : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env source =
      (.err (.abort .typeError), middle) := by
    rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env source pureValue pureRun, callRun]
  apply notTypeError
  exact (congrArg Prod.fst (operationRun.symm.trans run)).symm

/-- A candidate whose arguments succeed but exhaust the call clock times out
in related source and target states, including after the accumulator rewrite. -/
theorem evaluate_worker_candidate_timeout {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env1 env2 : List Value)
    (source sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (ctx : List ValueType) (ty : ValueType)
    (callArgs : List Value) (pureValue oldValue : Value) (sourceResult : BviSem.BviResult)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (envRelated : envRel ty true acc env1 env2) (related : stateRel source target)
    (types : tyRel env1 ctx) (notNoop : op ≠ .noop)
    (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env2[acc]? = some oldValue)
    (pureSource : BviSem.evaluate [pure] env1 source = (.val [pureValue], source))
    (pureTarget : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env2 s = (.val [pureValue], s))
    (argsSource : BviSem.evaluate args env1 source = (.val callArgs, sourceMiddle))
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc target.code op)
    (timeout : sourceMiddle.clock < ticks + 1)
    (operationSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext)) (notTypeError : sourceResult ≠ .err (.abort .typeError)) :
    ∃ targetNext,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env2 target = (.err (.abort .timeoutError), targetNext) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env2 target = (.err (.abort .timeoutError), targetNext) ∧ stateRel sourceNext targetNext := by
  have lengthEq := evaluate_candidate_arity loc arity ticks body pure op args env1 source sourceMiddle sourceNext
    callArgs pureValue sourceResult pureSource argsSource sourceCode operationSource notTypeError
  have argsHyp : rewriteTailHyp args source env1 (.val callArgs) sourceMiddle false target acc env2 loc ctx ty :=
    ⟨argsSource, envRel_disable ty true acc env1 env2 envRelated, related, types, by simp, by simp⟩
  obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
    argsIH source env1 (.val callArgs) sourceMiddle false target acc env2 loc ctx ty argsHyp
  have sourceCodeMiddle := evaluate_lookup_preserved args env1 source sourceMiddle (.val callArgs)
    loc arity body argsSource sourceCode
  have targetGrowth := BviProps.evaluate_code_mono args env2 target targetMiddle (.val callArgs) targetArgs
  have optimizedMiddle := optimizedCode_subspt loc arity body workerLoc target.code targetMiddle.code op
    optimized targetGrowth
  obtain ⟨wrapper, worker, compiled, check, wrapperFound, workerFound⟩ := optimizedMiddle
  have targetTimeout : targetMiddle.clock < ticks + 1 := by
    have clocks := (stateRel_const sourceMiddle targetMiddle middleRelated).2.1
    omega
  have sourceCall : BviSem.evaluate [.call ticks (some loc) args none] env1 source =
      (.err (.abort .timeoutError), { sourceMiddle with clock := 0 }) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsSource]
    simp [findCode, sourceCodeMiddle, lengthEq, timeout]
  have sourceOperation : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (.err (.abort .timeoutError), { sourceMiddle with clock := 0 }) := by
    rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env1 source pureValue pureSource,
      sourceCall]
  have same := sourceOperation.symm.trans operationSource
  obtain ⟨workerRun, originalRun⟩ :=
    evaluate_worker_call_timeout loc arity workerLoc ticks acc body wrapper pure op args env2 target targetMiddle
      callArgs pureValue oldValue notNoop pureTyped oldTyped lookup pureTarget targetArgs lengthEq wrapperFound
      ⟨wrapper, worker, compiled, check, wrapperFound, workerFound⟩ targetTimeout
  have stateEq : { sourceMiddle with clock := 0 } = sourceNext := congrArg Prod.snd same
  exact ⟨{ targetMiddle with clock := 0 }, workerRun, originalRun,
    by simpa [stateEq] using stateRel_withClock sourceMiddle targetMiddle 0 middleRelated⟩

/-- Direct calls reject a return raised by their callee. -/
def directCallResult (result : BviSem.BviResult) : BviSem.BviResult :=
  match result with
  | .err (.raise (.ret _)) => .err (.abort .typeError)
  | other => other

/-- For a candidate with sufficient clock, the source callee execution
supplies the smaller-clock induction hypothesis needed by the worker. -/
theorem evaluate_worker_candidate_enough_clock {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env1 env2 : List Value)
    (source sourceMiddle sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (ctx : List ValueType) (ty : ValueType)
    (callArgs : List Value) (pureValue oldValue : Value) (sourceResult : BviSem.BviResult)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (values : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called values r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called values r last optimized target acc env2 loc ts ty)
    (envRelated : envRel ty true acc env1 env2) (related : stateRel source target)
    (types : tyRel env1 ctx) (notNoop : op ≠ .noop)
    (pureTyped : valueMatchesType pureValue (opType op))
    (oldTyped : valueMatchesType oldValue (opType op)) (lookup : env2[acc]? = some oldValue)
    (pureSource : BviSem.evaluate [pure] env1 source = (.val [pureValue], source))
    (pureTarget : ∀ s : BviSem.BviState C F, BviSem.evaluate [pure] env2 s = (.val [pureValue], s))
    (argsSource : BviSem.evaluate args env1 source = (.val callArgs, sourceMiddle))
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc target.code op)
    (enoughClock : ticks + 1 ≤ sourceMiddle.clock)
    (operationSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext)) (notTypeError : sourceResult ≠ .err (.abort .typeError)) :
    ∃ result' t1 t2,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env2 target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env2 target = (result', t2) ∧ stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  have lengthEq := evaluate_candidate_arity loc arity ticks body pure op args env1 source sourceMiddle sourceNext
    callArgs pureValue sourceResult pureSource argsSource sourceCode operationSource notTypeError
  have argsHyp : rewriteTailHyp args source env1 (.val callArgs) sourceMiddle false target acc env2 loc ctx ty :=
    ⟨argsSource, envRel_disable ty true acc env1 env2 envRelated, related, types, by simp, by simp⟩
  obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
    argsIH source env1 (.val callArgs) sourceMiddle false target acc env2 loc ctx ty argsHyp
  have sourceCodeMiddle := evaluate_lookup_preserved args env1 source sourceMiddle (.val callArgs)
    loc arity body argsSource sourceCode
  have targetGrowth := BviProps.evaluate_code_mono args env2 target targetMiddle (.val callArgs) targetArgs
  have optimizedMiddle := optimizedCode_subspt loc arity body workerLoc target.code targetMiddle.code op
    optimized targetGrowth
  have argsClock := BviSem.evaluate_clock_le args env1 source
  rw [argsSource] at argsClock
  have small : (BviSem.decClock (ticks + 1) sourceMiddle).clock < source.clock := by
    simp only [BviSem.decClock]
    simp only at argsClock
    omega
  have noTimeout : ¬sourceMiddle.clock < ticks + 1 := by omega
  cases bodyRun : BviSem.evaluate [body] callArgs (BviSem.decClock (ticks + 1) sourceMiddle) with
  | mk bodyResult bodyNext =>
    have callShape : BviSem.evaluate [.call ticks (some loc) args none] env1 source =
        (directCallResult bodyResult, bodyNext) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsSource]
      simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        findCode, sourceCodeMiddle, lengthEq, noTimeout]
      rw [BviSem.fixClock_evaluate, bodyRun]
      unfold directCallResult
      cases bodyResult with
      | val values => rfl
      | err error => cases error with
        | abort reason => rfl
        | raise payload => cases payload <;> rfl
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      have run := operationSource
      rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env1 source pureValue pureSource,
        callShape, bad] at run
      simp only [directCallResult] at run
      apply notTypeError
      exact (congrArg Prod.fst run).symm
    have noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)) := by
      intro values bad
      have run := operationSource
      rw [evaluate_applyOp_pureLeft op pure (.call ticks (some loc) args none) env1 source pureValue pureSource,
        callShape, bad] at run
      simp only [directCallResult] at run
      apply notTypeError
      exact (congrArg Prod.fst run).symm
    have callSource : BviSem.evaluate [.call ticks (some loc) args none] env1 source = (bodyResult, bodyNext) := by
      rw [callShape]
      unfold directCallResult
      cases bodyResult with
      | val values => rfl
      | err error => cases error with
        | abort reason => rfl
        | raise payload => cases payload with
          | exn value => rfl
          | ret values => exact (noReturn values rfl).elim
    exact evaluate_worker_candidate_operation loc arity workerLoc ticks acc body pure op args env1 env2
      source sourceMiddle bodyNext sourceNext target targetMiddle callArgs pureValue oldValue bodyResult sourceResult
      (clockIH body (BviSem.decClock (ticks + 1) sourceMiddle) callArgs bodyResult bodyNext small)
      middleRelated lengthEq sourceCodeMiddle optimizedMiddle notNoop pureTyped oldTyped lookup pureSource pureTarget
      targetArgs enoughClock bodyRun callSource operationSource bodyNotType noReturn

/-- A checked pure operand and direct recursive call satisfy the worker
simulation for argument errors, timeouts, and successful callee execution. -/
theorem evaluate_worker_candidate {C F : Type}
    (loc arity workerLoc ticks acc : Nat) (body pure : Bvi.Exp) (op : AssocOp)
    (args : List Bvi.Exp) (env1 env2 : List Value)
    (source sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (ctx : List ValueType) (ty : ValueType) (sourceResult : BviSem.BviResult)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (termIH : rewriteTailProperty (C := C) (F := F) [pure])
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (values : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called values r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called values r last optimized target acc env2 loc ts ty)
    (envRelated : envRel ty true acc env1 env2) (related : stateRel source target)
    (types : tyRel env1 ctx) (notNoop : op ≠ .noop) (sameType : opType op = ty)
    (termOk : term ctx (opType op) pure = true)
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc target.code op)
    (operationSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext)) (notTypeError : sourceResult ≠ .err (.abort .typeError)) :
    ∃ result' t1 t2,
      BviSem.evaluate [.call ticks (some workerLoc) (args ++ [applyOp op (.var acc) pure]) none]
        env2 target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) (applyOp op pure (.call ticks (some loc) args none))]
        env2 target = (result', t2) ∧ stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨pureValue, pureTyped, pureSource, pureTarget⟩ :=
    term_prefix_simulation_all pure ctx (opType op) env1 env2 source target loc termIH termOk types envRelated.1 related
  obtain ⟨oldValue, lookup, oldTyped⟩ := envRel_accumulator ty acc env1 env2 envRelated
  have oldTyped' : valueMatchesType oldValue (opType op) := by simpa [sameType] using oldTyped
  cases argsRun : BviSem.evaluate args env1 source with
  | mk argsResult sourceMiddle =>
    cases argsResult with
    | err error =>
      obtain ⟨targetNext, workerRun, appliedRun, finalRelated⟩ :=
        evaluate_worker_candidate_argument_error loc workerLoc ticks acc op pure args env1 env2 source sourceMiddle
          sourceNext target ctx ty pureValue oldValue error sourceResult argsIH envRelated related types notNoop
          pureTyped oldTyped' lookup (pureSource source) pureTarget argsRun operationSource notTypeError
      exact ⟨.err error, targetNext, targetNext, workerRun, appliedRun, finalRelated, finalRelated⟩
    | val values =>
      by_cases timeout : sourceMiddle.clock < ticks + 1
      · obtain ⟨targetNext, workerRun, appliedRun, finalRelated⟩ :=
          evaluate_worker_candidate_timeout loc arity workerLoc ticks acc body pure op args env1 env2 source
            sourceMiddle sourceNext target ctx ty values pureValue oldValue sourceResult argsIH envRelated related
            types notNoop pureTyped oldTyped' lookup (pureSource source) pureTarget argsRun sourceCode optimized
            timeout operationSource notTypeError
        exact ⟨.err (.abort .timeoutError), targetNext, targetNext, workerRun, appliedRun, finalRelated, finalRelated⟩
      · have enoughClock : ticks + 1 ≤ sourceMiddle.clock := by omega
        exact evaluate_worker_candidate_enough_clock loc arity workerLoc ticks acc body pure op args env1 env2 source
          sourceMiddle sourceNext target ctx ty values pureValue oldValue sourceResult argsIH clockIH envRelated related
          types notNoop pureTyped oldTyped' lookup (pureSource source) pureTarget argsRun sourceCode optimized
          enoughClock operationSource notTypeError

/-- A successful source candidate check selects a worker whose execution
matches the accumulator applied to the original operand order. -/
theorem evaluate_checked_worker_candidate {C F : Type}
    (loc arity workerLoc acc : Nat) (body e checked : Bvi.Exp) (op : AssocOp)
    (env1 env2 : List Value) (source sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (ctx : List ValueType) (ty : ValueType)
    (sourceResult : BviSem.BviResult)
    (subIH : ∀ pure ticks args,
      (e = applyOp op pure (.call ticks (some loc) args none) ∨
        (op ≠ .append ∧ e = applyOp op (.call ticks (some loc) args none) pure)) →
      rewriteTailProperty (C := C) (F := F) [pure] ∧ rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (values : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called values r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called values r last optimized target acc env2 loc ts ty)
    (envRelated : envRel ty true acc env1 env2) (related : stateRel source target)
    (types : tyRel env1 ctx) (sameType : opType op = ty)
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body workerLoc target.code op)
    (check : checkOp ctx op loc e = some checked)
    (sourceRun : BviSem.evaluate [e] env1 source = (sourceResult, sourceNext))
    (notTypeError : sourceResult ≠ .err (.abort .typeError)) :
    ∃ result' t1 t2,
      BviSem.evaluate [(rewriteSource loc workerLoc op acc ctx e).2] env2 target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) e] env2 target = (result', t2) ∧
      stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨pure, ticks, args, termOk, notNoop, original, rewrite⟩ :=
    checkOp_rewrite_worker ctx op loc workerLoc acc e checked check
  obtain ⟨termIH, argsIH⟩ := subIH pure ticks args original
  obtain ⟨pureValue, _, pureSource, pureTarget⟩ :=
    term_prefix_simulation_all pure ctx (opType op) env1 env2 source target loc termIH termOk types envRelated.1 related
  have sourceOrder : BviSem.evaluate [e] env1 source =
      BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source := by
    rcases original with direct | ⟨notAppend, swapped⟩
    · rw [direct]
    · rw [swapped]
      exact (evaluate_applyOp_swap_pure op pure (.call ticks (some loc) args none) env1 source
        pureValue notNoop notAppend pureSource).symm
  have targetOrder : BviSem.evaluate [e] env2 target =
      BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env2 target := by
    rcases original with direct | ⟨notAppend, swapped⟩
    · rw [direct]
    · rw [swapped]
      exact (evaluate_applyOp_swap_pure op pure (.call ticks (some loc) args none) env2 target
        pureValue notNoop notAppend pureTarget).symm
  have normalizedSource : BviSem.evaluate [applyOp op pure (.call ticks (some loc) args none)] env1 source =
      (sourceResult, sourceNext) := sourceOrder.symm.trans sourceRun
  obtain ⟨result', t1, t2, workerRun, appliedRun, rel1, rel2⟩ :=
    evaluate_worker_candidate loc arity workerLoc ticks acc body pure op args env1 env2 source sourceNext target
      ctx ty sourceResult argsIH termIH clockIH envRelated related types notNoop sameType termOk sourceCode optimized
      normalizedSource notTypeError
  obtain ⟨oldValue, lookup, _⟩ := envRel_accumulator ty acc env1 env2 envRelated
  refine ⟨result', t1, t2, ?_, ?_, rel1, rel2⟩
  · simpa [rewrite] using workerRun
  · rw [evaluate_applyOp_var op acc e env2 target oldValue lookup, targetOrder]
    rw [evaluate_applyOp_var op acc (applyOp op pure (.call ticks (some loc) args none)) env2 target oldValue lookup]
      at appliedRun
    exact appliedRun

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

/-- When a singleton scan cannot select an operator, ordinary simulation
suffices for the entire rewrite postcondition. -/
theorem rewriteTailPost_of_no_scan {C F : Type} (e : Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target targetNext : BviSem.BviState C F)
    (acc : Nat) (env2 : List Value) (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (run : BviSem.evaluate [e] env2 target = (result, targetNext))
    (related : stateRel sourceNext targetNext)
    (noScan : ∀ tt resultTy branch op1,
      scanExpr ts loc [e] ≠ [(tt, resultTy, branch, some op1)]) :
    rewriteTailPost [e] source env1 result sourceNext optimized target acc env2 loc ts ty := by
  refine ⟨targetNext, run, related, ?_⟩
  intro _ op workerLoc code arity required
  obtain ⟨_, _, _, op1, tt, resultTy, branch, scan, _, _, _⟩ := required
  exact (noScan tt resultTy branch op1 (by simpa only [List.headD_cons] using scan)).elim

/-- The call simulation for a call without an exception handler. The two
induction hypotheses cover its argument list and smaller-clock callees. -/
theorem rewriteTail_call_noHandler {C F : Type} (ticks : Nat) (dest : Option Nat)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (callArgs : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called callArgs r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called callArgs r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.call ticks dest args none] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.call ticks dest args none] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  have simulation : ∃ targetNext, BviSem.evaluate [.call ticks dest args none] env2 target =
      (result, targetNext) ∧ stateRel sourceNext targetNext := by
    have disabled := envRel_disable ty optimized acc env1 env2 envRelated
    rw [BviSem.evaluate] at run
    simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      BviSem.fixClock_evaluate] at run
    cases argsRun : BviSem.evaluate args env1 source with
    | mk argsResult middle =>
      cases argsResult with
      | err error =>
        simp only [argsRun] at run
        have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have argsHyp : rewriteTailHyp args source env1 (.err error) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, ok⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.err error) middle false target acc env2 loc ts ty argsHyp
        have same : (.err error, middle) = (result, sourceNext) := by simpa [argsRun] using run
        cases same
        refine ⟨targetMiddle, ?_, middleRelated⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp
      | val values =>
        have argsHyp : rewriteTailHyp args source env1 (.val values) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, by simp⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.val values) middle false target acc env2 loc ts ty argsHyp
        simp only [argsRun] at run
        cases resolved : findCode dest values middle.code with
        | none =>
          simp [resolved] at run
          exact (notTypeError run.1.symm).elim
        | some entry =>
          obtain ⟨actual, body⟩ := entry
          have relatedCode := stateRel_codeRel middle targetMiddle middleRelated
          obtain ⟨compiled, targetResolved⟩ :=
            codeRel_findCode_replacement dest values actual middle.code targetMiddle.code body relatedCode resolved
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            have same : (.err (.abort .timeoutError), { middle with clock := 0 }) =
                (result, sourceNext) := by
              simpa [resolved, timeout] using run
            cases same
            refine ⟨{ targetMiddle with clock := 0 }, ?_,
              stateRel_withClock middle targetMiddle 0 middleRelated⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp [targetResolved, targetTimeout]
          · have argsClock := BviSem.evaluate_clock_le args env1 source
            rw [argsRun] at argsClock
            have small : (BviSem.decClock (ticks + 1) middle).clock < source.clock := by
              simp only [BviSem.decClock]
              simp only at argsClock
              omega
            have targetNotTimeout : ¬targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            cases bodyRun : BviSem.evaluate [body] actual (BviSem.decClock (ticks + 1) middle) with
            | mk inner last =>
              rw [resolved] at run
              simp only [timeout, ↓reduceIte, bodyRun] at run
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
              obtain ⟨targetBody, targetNext, targetBodyResolved, targetBodyRun, finalRelated⟩ :=
                evaluate_related_resolved_callee dest values actual body (ticks + 1)
                  middle sourceNext targetMiddle result
                  (clockIH body (BviSem.decClock (ticks + 1) middle) actual result sourceNext small)
                  middleRelated resolved bodyRun notTypeError
              refine ⟨targetNext, ?_, finalRelated⟩
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
              simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                targetBodyResolved, targetNotTimeout, BviSem.fixClock_evaluate]
              rw [targetBodyRun]
              cases result with
              | val values => rfl
              | err error =>
                cases error with
                | abort reason => rfl
                | raise payload =>
                  cases payload with
                  | exn exception => rfl
                  | ret values => exact (notReturn values rfl).elim
  obtain ⟨targetNext, targetRun, targetRelated⟩ := simulation
  apply rewriteTailPost_of_no_scan (.call ticks dest args none) source env1 result sourceNext
    optimized target targetNext acc env2 loc ts ty targetRun targetRelated
  intro tt resultTy branch op1 scan
  rw [scanExpr_single, scanSing.eq_def] at scan
  simp at scan

/-- Result handling for a direct call with a handler, factored out to compare
source and target executions of the same callee outcome. -/
noncomputable def callHandlerOutcome {C F : Type} (handler : Bvi.Exp) (env : List Value)
    (result : BviSem.BviResult) (state : BviSem.BviState C F) : BviSem.EvalResult C F :=
  match result with
  | .err (.raise (.exn value)) =>
    match BviSem.evaluate [handler] (value :: env) state with
    | (.err (.raise (.ret _)), last) => (.err (.abort .typeError), last)
    | other => other
  | .err (.raise (.ret _)) => (.err (.abort .typeError), state)
  | other => (other, state)

/-- The call simulation for a direct call with an exception handler. -/
theorem rewriteTail_call_handler {C F : Type} (ticks place : Nat) (handler : Bvi.Exp)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (callArgs : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called callArgs r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called callArgs r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.call ticks (some place) args (some handler)] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.call ticks (some place) args (some handler)] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  have simulation : ∃ targetNext, BviSem.evaluate [.call ticks (some place) args (some handler)] env2 target =
      (result, targetNext) ∧ stateRel sourceNext targetNext := by
    have disabled := envRel_disable ty optimized acc env1 env2 envRelated
    rw [BviSem.evaluate] at run
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      BviSem.fixClock_evaluate] at run
    cases argsRun : BviSem.evaluate args env1 source with
    | mk argsResult middle =>
      cases argsResult with
      | err error =>
        simp only [argsRun] at run
        have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have argsHyp : rewriteTailHyp args source env1 (.err error) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, ok⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.err error) middle false target acc env2 loc ts ty argsHyp
        have same : (.err error, middle) = (result, sourceNext) := by simpa [argsRun] using run
        cases same
        refine ⟨targetMiddle, ?_, middleRelated⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp
      | val values =>
        have argsHyp : rewriteTailHyp args source env1 (.val values) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, by simp⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.val values) middle false target acc env2 loc ts ty argsHyp
        simp only [argsRun] at run
        cases resolved : findCode (some place) values middle.code with
        | none =>
          simp [resolved] at run
          exact (notTypeError run.1.symm).elim
        | some entry =>
          obtain ⟨actual, body⟩ := entry
          have relatedCode := stateRel_codeRel middle targetMiddle middleRelated
          obtain ⟨compiled, targetResolved⟩ :=
            codeRel_findCode_replacement (some place) values actual middle.code targetMiddle.code body relatedCode resolved
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            have same : (.err (.abort .timeoutError), { middle with clock := 0 }) =
                (result, sourceNext) := by
              simpa [resolved, timeout] using run
            cases same
            refine ⟨{ targetMiddle with clock := 0 }, ?_,
              stateRel_withClock middle targetMiddle 0 middleRelated⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp [targetResolved, targetTimeout]
          · have argsClock := BviSem.evaluate_clock_le args env1 source
            rw [argsRun] at argsClock
            have small : (BviSem.decClock (ticks + 1) middle).clock < source.clock := by
              simp only [BviSem.decClock]
              simp only at argsClock
              omega
            have targetNotTimeout : ¬targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            cases bodyRun : BviSem.evaluate [body] actual (BviSem.decClock (ticks + 1) middle) with
            | mk inner last =>
              rw [resolved] at run
              simp only [timeout, ↓reduceIte, bodyRun] at run
              have innerOk : inner ≠ .err (.abort .typeError) := by
                intro bad
                rw [bad] at run
                simp at run
                exact notTypeError run.1.symm
              obtain ⟨targetBody, targetLast, targetBodyResolved, targetBodyRun, lastRelated⟩ :=
                evaluate_related_resolved_callee (some place) values actual body (ticks + 1)
                  middle last targetMiddle inner
                  (clockIH body (BviSem.decClock (ticks + 1) middle) actual inner last small)
                  middleRelated resolved bodyRun innerOk
              have targetCall : BviSem.evaluate [.call ticks (some place) args (some handler)] env2 target =
                  callHandlerOutcome handler env2 inner targetLast := by
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                  targetBodyResolved, targetNotTimeout, BviSem.fixClock_evaluate]
                rw [targetBodyRun]
                cases inner with
                | val values => rfl
                | err error =>
                  cases error with
                  | abort reason => rfl
                  | raise payload => cases payload <;> rfl
              cases inner with
              | val returned =>
                have same : (.val returned, last) = (result, sourceNext) := by simpa using run
                cases same
                exact ⟨targetLast, by simpa [callHandlerOutcome] using targetCall, lastRelated⟩
              | err error =>
                cases error with
                | abort reason =>
                  have same : (.err (.abort reason), last) = (result, sourceNext) := by simpa using run
                  cases same
                  exact ⟨targetLast, by simpa [callHandlerOutcome] using targetCall, lastRelated⟩
                | raise payload =>
                  cases payload with
                  | ret returned =>
                    simp at run
                    exact (notTypeError run.1.symm).elim
                  | exn exception =>
                    cases handlerRun : BviSem.evaluate [handler] (exception :: env1) last with
                    | mk handlerResult handlerLast =>
                      have same : (handlerResult, handlerLast) = (result, sourceNext) := by
                        cases handlerResult with
                        | val values => simpa [handlerRun] using run
                        | err error =>
                          cases error with
                          | abort reason => simpa [handlerRun] using run
                          | raise payload =>
                            cases payload with
                            | exn value => simpa [handlerRun] using run
                            | ret values =>
                              simp [handlerRun] at run
                              exact (notTypeError run.1.symm).elim
                      have notReturn : ∀ values, handlerResult ≠ .err (.raise (.ret values)) := by
                        intro values eq
                        rw [eq] at handlerRun
                        simp [handlerRun] at run
                        exact notTypeError run.1.symm
                      have bodyClock := BviSem.evaluate_clock_le [body] actual (BviSem.decClock (ticks + 1) middle)
                      rw [bodyRun] at bodyClock
                      have handlerSmall : last.clock < source.clock := by
                        simp only [BviSem.decClock] at bodyClock
                        simp only at bodyClock argsClock
                        omega
                      cases same
                      have handlerEnv : envRel ty false (1 + acc) (exception :: env1) (exception :: env2) := by
                        simpa using envRel_prepend ty false acc env1 env2 [exception] disabled
                      have handlerTypes : tyRel (exception :: env1) (.any :: ts) :=
                        .cons (by simp) types
                      have handlerHyp : rewriteTailHyp [handler] last (exception :: env1) result sourceNext
                          false targetLast (1 + acc) (exception :: env2) loc (.any :: ts) ty :=
                        ⟨handlerRun, handlerEnv, lastRelated, handlerTypes, by simp, notTypeError⟩
                      obtain ⟨targetNext, targetHandler, finalRelated, _⟩ :=
                        clockIH handler last (exception :: env1) result sourceNext handlerSmall
                          false targetLast (1 + acc) (exception :: env2) loc (.any :: ts) ty handlerHyp
                      refine ⟨targetNext, ?_, finalRelated⟩
                      rw [targetCall]
                      simp only [callHandlerOutcome, targetHandler]
                      cases result with
                      | val values => rfl
                      | err error =>
                        cases error with
                        | abort reason => rfl
                        | raise payload =>
                          cases payload with
                          | exn value => rfl
                          | ret values => exact (notReturn values rfl).elim
  obtain ⟨targetNext, targetRun, targetRelated⟩ := simulation
  apply rewriteTailPost_of_no_scan (.call ticks (some place) args (some handler)) source env1 result sourceNext
    optimized target targetNext acc env2 loc ts ty targetRun targetRelated
  intro tt resultTy branch op1 scan
  rw [scanExpr_single, scanSing.eq_def] at scan
  simp at scan

/-- Result handling for a let-call, including arity checking before its
continuation. -/
noncomputable def letCallOutcome {C F : Type} (rets : Nat) (cont : Bvi.Exp) (env : List Value)
    (result : BviSem.BviResult) (state : BviSem.BviState C F) : BviSem.EvalResult C F :=
  match result with
  | .val _ => (.err (.abort .typeError), state)
  | .err (.raise (.ret values)) =>
    if values.length = rets then BviSem.evaluate [cont] (values ++ env) state
    else (.err (.abort .typeError), state)
  | other => (other, state)

/-- The let-call simulation, including returned values and its continuation. -/
theorem rewriteTail_letCall {C F : Type} (rets ticks place : Nat) (cont : Bvi.Exp)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (callArgs : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called callArgs r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called callArgs r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.letCall rets ticks place args cont] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.letCall rets ticks place args cont] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  have simulation : ∃ targetNext, BviSem.evaluate [.letCall rets ticks place args cont] env2 target =
      (result, targetNext) ∧ stateRel sourceNext targetNext := by
    have disabled := envRel_disable ty optimized acc env1 env2 envRelated
    rw [BviSem.evaluate] at run
    simp only [BviSem.fixClock_evaluate] at run
    cases argsRun : BviSem.evaluate args env1 source with
    | mk argsResult middle =>
      cases argsResult with
      | err error =>
        simp only [argsRun] at run
        have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have argsHyp : rewriteTailHyp args source env1 (.err error) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, ok⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.err error) middle false target acc env2 loc ts ty argsHyp
        have same : (.err error, middle) = (result, sourceNext) := by simpa [argsRun] using run
        cases same
        refine ⟨targetMiddle, ?_, middleRelated⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
      | val values =>
        have argsHyp : rewriteTailHyp args source env1 (.val values) middle false
            target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, by simp⟩
        obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
          argsIH source env1 (.val values) middle false target acc env2 loc ts ty argsHyp
        simp only [argsRun] at run
        cases resolved : findCode (some place) values middle.code with
        | none =>
          simp [resolved] at run
          exact (notTypeError run.1.symm).elim
        | some entry =>
          obtain ⟨actual, body⟩ := entry
          have relatedCode := stateRel_codeRel middle targetMiddle middleRelated
          obtain ⟨compiled, targetResolved⟩ :=
            codeRel_findCode_replacement (some place) values actual middle.code targetMiddle.code body relatedCode resolved
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            have same : (.err (.abort .timeoutError), { middle with clock := 0 }) =
                (result, sourceNext) := by
              simpa [resolved, timeout] using run
            cases same
            refine ⟨{ targetMiddle with clock := 0 }, ?_,
              stateRel_withClock middle targetMiddle 0 middleRelated⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp [targetResolved, targetTimeout]
          · have argsClock := BviSem.evaluate_clock_le args env1 source
            rw [argsRun] at argsClock
            have small : (BviSem.decClock (ticks + 1) middle).clock < source.clock := by
              simp only [BviSem.decClock]
              simp only at argsClock
              omega
            have targetNotTimeout : ¬targetMiddle.clock < ticks + 1 := by
              have := (stateRel_const middle targetMiddle middleRelated).2.1
              omega
            cases bodyRun : BviSem.evaluate [body] actual (BviSem.decClock (ticks + 1) middle) with
            | mk inner last =>
              rw [resolved] at run
              simp only [timeout, ↓reduceIte, bodyRun] at run
              have innerOk : inner ≠ .err (.abort .typeError) := by
                intro bad
                rw [bad] at run
                simp at run
                exact notTypeError run.1.symm
              obtain ⟨targetBody, targetLast, targetBodyResolved, targetBodyRun, lastRelated⟩ :=
                evaluate_related_resolved_callee (some place) values actual body (ticks + 1)
                  middle last targetMiddle inner
                  (clockIH body (BviSem.decClock (ticks + 1) middle) actual inner last small)
                  middleRelated resolved bodyRun innerOk
              have targetCall : BviSem.evaluate [.letCall rets ticks place args cont] env2 target =
                  letCallOutcome rets cont env2 inner targetLast := by
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                simp only [targetBodyResolved, targetNotTimeout, ↓reduceIte, BviSem.fixClock_evaluate]
                rw [targetBodyRun]
                cases inner with
                | val values => rfl
                | err error =>
                  cases error with
                  | abort reason => rfl
                  | raise payload => cases payload <;> rfl
              cases inner with
              | val returned =>
                simp at run
                exact (notTypeError run.1.symm).elim
              | err error =>
                cases error with
                | abort reason =>
                  have same : (.err (.abort reason), last) = (result, sourceNext) := by simpa using run
                  cases same
                  exact ⟨targetLast, by simpa [letCallOutcome] using targetCall, lastRelated⟩
                | raise payload =>
                  cases payload with
                  | exn exception =>
                    have same : (.err (.raise (.exn exception)), last) = (result, sourceNext) := by simpa using run
                    cases same
                    exact ⟨targetLast, by simpa [letCallOutcome] using targetCall, lastRelated⟩
                  | ret returned =>
                    by_cases returnLength : returned.length = rets
                    · have contRun : BviSem.evaluate [cont] (returned ++ env1) last = (result, sourceNext) := by
                        simpa [returnLength] using run
                      have bodyClock := BviSem.evaluate_clock_le [body] actual
                        (BviSem.decClock (ticks + 1) middle)
                      rw [bodyRun] at bodyClock
                      have contSmall : last.clock < source.clock := by
                        simp only [BviSem.decClock] at bodyClock
                        simp only at bodyClock argsClock
                        omega
                      have contEnv := envRel_prepend ty false acc env1 env2 returned disabled
                      have contTypes : tyRel (returned ++ env1) (List.replicate returned.length .any ++ ts) :=
                        tyRel_append env1 ts (List.replicate returned.length .any) returned
                          ⟨types, tyRel_replicate_any returned⟩
                      have contHyp : rewriteTailHyp [cont] last (returned ++ env1) result sourceNext false
                          targetLast (returned.length + acc) (returned ++ env2) loc
                          (List.replicate returned.length .any ++ ts) ty :=
                        ⟨contRun, contEnv, lastRelated, contTypes, by simp, notTypeError⟩
                      obtain ⟨targetNext, targetCont, finalRelated, _⟩ :=
                        clockIH cont last (returned ++ env1) result sourceNext contSmall false targetLast
                          (returned.length + acc) (returned ++ env2) loc
                          (List.replicate returned.length .any ++ ts) ty contHyp
                      exact ⟨targetNext, by simpa [letCallOutcome, returnLength, targetCont] using targetCall,
                        finalRelated⟩
                    · simp [returnLength] at run
                      exact (notTypeError run.1.symm).elim
  obtain ⟨targetNext, targetRun, targetRelated⟩ := simulation
  apply rewriteTailPost_of_no_scan (.letCall rets ticks place args cont) source env1 result sourceNext
    optimized target targetNext acc env2 loc ts ty targetRun targetRelated
  intro tt resultTy branch op1 scan
  rw [scanExpr_single, scanSing.eq_def] at scan
  simp at scan

/-- The complete call case, including handler-free indirect calls and direct
calls with handlers. An indirect call with a handler is a type error. -/
theorem rewriteTail_call {C F : Type} (ticks : Nat) (dest : Option Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (callArgs : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called callArgs r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called callArgs r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.call ticks dest args handler] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.call ticks dest args handler] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  cases handler with
  | none =>
    exact rewriteTail_call_noHandler ticks dest args source env1 result sourceNext
      optimized target acc env2 loc ts ty argsIH clockIH hyp
  | some handler =>
    cases dest with
    | none =>
      obtain ⟨run, _, _, _, _, notTypeError⟩ := hyp
      simp [BviSem.evaluate] at run
      exact (notTypeError run.1.symm).elim
    | some place =>
      exact rewriteTail_call_handler ticks place handler args source env1 result sourceNext
        optimized target acc env2 loc ts ty argsIH clockIH hyp

/-- A rewritten conditional branch has a selected, non-noop operator of the
conditional's specific accumulator type. -/
theorem scanIf_rewritten_branch (ctx : List ValueType) (loc next acc : Nat) (op : AssocOp)
    (cond yes no branch output : Bvi.Exp)
    (member : branch = yes ∨ branch = no)
    (notNoop : op ≠ .noop)
    (specific : (scanSing ctx loc (.ifThenElse cond yes no)).2.1 ≠ .any)
    (sameType : (scanSing ctx loc (.ifThenElse cond yes no)).2.1 = opType op)
    (rewritten : rewriteSource loc next op acc (scanSing ctx loc cond).1 branch = (true, output)) :
    ∃ outCtx resultTy branchFlag op1,
      scanExpr (scanSing ctx loc cond).1 loc [branch] = [(outCtx, resultTy, branchFlag, some op1)] ∧
      resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op := by
  have branchTypes := scanSing_if_branch_types ctx loc cond yes no specific
  have branchType : (scanSing (scanSing ctx loc cond).1 loc branch).2.1 = opType op := by
    rcases member with rfl | rfl
    · exact branchTypes.1.trans sameType
    · exact branchTypes.2.trans sameType
  have branchSpecific : (scanSing (scanSing ctx loc cond).1 loc branch).2.1 ≠ .any := by
    rw [branchType, ← sameType]
    exact specific
  have flags := rewriteSingle_scan branch (scanSing ctx loc cond).1 loc next acc op notNoop
  rw [rewriteSingle_eq_source, rewritten] at flags
  rcases hscan : scanSing (scanSing ctx loc cond).1 loc branch with ⟨outCtx, resultTy, branchFlag, choice⟩
  cases choice with
  | none =>
    have impossible := flags.1 (by rw [hscan])
    simp at impossible
  | some op1 =>
    have noNoop := scanSing_ne_noop (scanSing ctx loc cond).1 loc branch
    rw [hscan] at noNoop
    have noNoop' : op1 ≠ .noop := by simpa using noNoop
    have typed := scanSing_choice_type branch (scanSing ctx loc cond).1 loc op1 (by rw [hscan]) branchSpecific
    refine ⟨outCtx, resultTy, branchFlag, op1, ?_, ?_, noNoop', typed.trans branchType⟩
    · rw [scanExpr_single, hscan]
    · simpa [hscan] using branchSpecific

/-- Applying an accumulator after a simulated branch preserves the related
final state, whether the primitive succeeds or reports a type error. -/
theorem stateRel_applyOp_after {C F : Type} (op : AssocOp) (acc : Nat) (branch : Bvi.Exp)
    (env : List Value) (target targetNext : BviSem.BviState C F)
    (sourceNext : BviSem.BviState (Nat × C) F) (result : BviSem.BviResult)
    (value : Value) (lookup : env[acc]? = some value)
    (run : BviSem.evaluate [branch] env target = (result, targetNext))
    (related : stateRel sourceNext targetNext) :
    ∃ result', BviSem.evaluate [applyOp op (.var acc) branch] env target = (result', targetNext) ∧
      stateRel sourceNext targetNext := by
  rw [evaluate_applyOp_var op acc branch env target value lookup, run]
  cases result with
  | err error => exact ⟨.err error, rfl, related⟩
  | val values =>
    cases applied : accumulatorApply op (values.reverse ++ [value]) with
    | none =>
      refine ⟨.err (.abort .typeError), ?_, related⟩
      simp [doApp_toOp_pure, applied]
    | some out =>
      refine ⟨.val [out], ?_, related⟩
      simp [doApp_toOp_pure, applied]

/-- The explicit accumulator fallback satisfies the optimization postcondition
whenever ordinary evaluation has already been simulated. -/
theorem evaluate_rewrite_fallback {C F : Type} (op : AssocOp) (loc next acc : Nat)
    (ctx : List ValueType) (e : Bvi.Exp) (env : List Value)
    (sourceNext : BviSem.BviState (Nat × C) F) (target targetNext : BviSem.BviState C F)
    (result : BviSem.BviResult) (value : Value) (lookup : env[acc]? = some value)
    (ordinary : BviSem.evaluate [e] env target = (result, targetNext))
    (related : stateRel sourceNext targetNext)
    (fallback : rewriteSource loc next op acc ctx e = (false, applyOp op (.var acc) e)) :
    ∃ result' t1 t2,
      BviSem.evaluate [(rewriteSource loc next op acc ctx e).2] env target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) e] env target = (result', t2) ∧
      stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨result', run, finalRelated⟩ :=
    stateRel_applyOp_after op acc e env target targetNext sourceNext result value lookup ordinary related
  exact ⟨result', targetNext, targetNext, by simpa [fallback] using run, run, finalRelated, finalRelated⟩

/-- The selected conditional branch either uses its rewrite or falls back to
an explicit accumulator operation, preserving the simulation postcondition. -/
theorem rewriteTail_if_branch {C F : Type} (ctx : List ValueType) (loc next acc : Nat)
    (op : AssocOp) (cond yes no branch : Bvi.Exp)
    (source sourceNext : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (target : BviSem.BviState C F) (env2 : List Value) (result : BviSem.BviResult)
    (ty : ValueType) (body : Bvi.Exp) (arity : Nat)
    (member : branch = yes ∨ branch = no)
    (branchIH : rewriteTailProperty (C := C) (F := F) [branch])
    (hyp : rewriteTailHyp [branch] source env1 result sourceNext true target acc env2 loc
      (scanSing ctx loc cond).1 ty)
    (sourceCode : sptLookup loc source.code = some (arity, body))
    (optimized : optimizedCode loc arity body next target.code op)
    (opTy : opType op = ty)
    (specific : (scanSing ctx loc (.ifThenElse cond yes no)).2.1 ≠ .any)
    (sameType : (scanSing ctx loc (.ifThenElse cond yes no)).2.1 = opType op) :
    let pair := rewriteSource loc next op acc (scanSing ctx loc cond).1 branch
    let chosen := if pair.1 then pair.2 else applyOp op (.var acc) branch
    ∃ result' t1 t2, BviSem.evaluate [chosen] env2 target = (result', t1) ∧
      BviSem.evaluate [applyOp op (.var acc) branch] env2 target = (result', t2) ∧
      stateRel sourceNext t1 ∧ stateRel sourceNext t2 := by
  obtain ⟨run, envRelated, related, types, singleton, notTypeError⟩ := hyp
  have notNoop : op ≠ .noop := by
    intro eq
    subst op
    simp [opType] at sameType
    exact specific sameType
  have lookupBound := (envRelated.2 rfl).2.1
  have lookup : env2[acc]? = some env2[acc] := by simp [lookupBound]
  obtain ⟨targetNext, targetRun, targetRelated, optRun⟩ :=
    branchIH source env1 result sourceNext true target acc env2 loc (scanSing ctx loc cond).1 ty
      ⟨run, envRelated, related, types, singleton, notTypeError⟩
  cases rewrite : rewriteSource loc next op acc (scanSing ctx loc cond).1 branch with
  | mk flag output =>
    cases flag with
    | false =>
      obtain ⟨result', applied, related'⟩ :=
        stateRel_applyOp_after op acc branch env2 target targetNext sourceNext result env2[acc]
          lookup targetRun targetRelated
      exact ⟨result', targetNext, targetNext, applied, applied, related', related'⟩
    | true =>
      obtain ⟨outCtx, resultTy, branchFlag, op1, scan, notAny, noNoop, opTypeEq⟩ :=
        scanIf_rewritten_branch ctx loc next acc op cond yes no branch output member notNoop
          specific sameType rewrite
      have req : sptLookup loc source.code = some (arity, body) ∧
          optimizedCode loc arity body next target.code op ∧ opType op = ty ∧
          (∃ op1 outCtx resultTy branchFlag,
            scanExpr (scanSing ctx loc cond).1 loc [branch] = [(outCtx, resultTy, branchFlag, some op1)] ∧
            resultTy ≠ .any ∧ op1 ≠ .noop ∧ opType op1 = opType op) :=
        ⟨sourceCode, optimized, opTy, op1, outCtx, resultTy, branchFlag, scan, notAny, noNoop, opTypeEq⟩
      obtain ⟨result', t1, t2, rewrittenRun, appliedRun, rel1, rel2⟩ :=
        optRun rfl op next body arity (by simpa only [List.headD_cons] using req)
      simp only [List.headD_cons, rewrite] at rewrittenRun
      exact ⟨result', t1, t2, rewrittenRun, by simpa using appliedRun, rel1, rel2⟩

/-- Successful condition evaluation preserves the inferred type context used
to scan both branches. -/
theorem tyRel_if_condition {C F : Type} (ctx : List ValueType) (loc : Nat) (cond : Bvi.Exp)
    (env : List Value) (source next : BviSem.BviState C F) (value : Value)
    (types : tyRel env ctx) (run : BviSem.evaluate [cond] env source = (.val [value], next)) :
    tyRel env (scanSing ctx loc cond).1 := by
  have sound := scanSound_list ctx loc [cond] env source next [value] types run
  have member : scanSing ctx loc cond ∈ scanExpr ctx loc [cond] := by simp [scanExpr_single]
  exact sound.1 _ member

/-- A successful boolean condition selects the corresponding branch without
changing the environment. -/
theorem evaluate_if_of_guard {C F : Type} (cond yes no : Bvi.Exp) (env : List Value)
    (state middle : BviSem.BviState C F) (value : Value) (flag : Bool)
    (guardRun : BviSem.evaluate [cond] env state = (.val [value], middle))
    (truth : asBool value = some flag) :
    BviSem.evaluate [.ifThenElse cond yes no] env state =
      BviSem.evaluate [if flag then yes else no] env middle := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, guardRun]
  change (match asBool value with
    | none => ((.err (.abort .typeError) : BviSem.BviResult), middle)
    | some true => BviSem.evaluate [yes] env middle
    | some false => BviSem.evaluate [no] env middle) = _
  cases flag <;> simp [truth]

/-- Conditional case when the condition propagates an error. Both the
rewritten conditional and the accumulator expression stop at that condition. -/
theorem rewriteTail_if_guard_error {C F : Type} (cond yes no : Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (guardIH : rewriteTailProperty (C := C) (F := F) [cond])
    (hyp : rewriteTailHyp [.ifThenElse cond yes no] source env1 result sourceNext
      optimized target acc env2 loc ts ty)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (middle : BviSem.BviState (Nat × C) F)
    (guardRun : BviSem.evaluate [cond] env1 source = (.err error, middle)) :
    rewriteTailPost [.ifThenElse cond yes no] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, guardRun] at run
  have same : (.err error, middle) = (result, sourceNext) := run
  cases same
  have disabled := envRel_disable ty optimized acc env1 env2 envRelated
  have guardHyp : rewriteTailHyp [cond] source env1 (.err error) sourceNext false
      target acc env2 loc ts ty := ⟨guardRun, disabled, related, types, by simp, notTypeError⟩
  obtain ⟨targetNext, targetGuard, targetRelated, _⟩ :=
    guardIH source env1 (.err error) sourceNext false target acc env2 loc ts ty guardHyp
  have targetIf : BviSem.evaluate [.ifThenElse cond yes no] env2 target = (.err error, targetNext) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetGuard]
  refine ⟨targetNext, targetIf, targetRelated, ?_⟩
  intro enabled op workerLoc code arity required
  simp only [List.headD_cons] at required ⊢
  have accBound := (envRelated.2 enabled).2.1
  have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
  refine ⟨.err error, targetNext, targetNext, ?_, ?_, targetRelated, targetRelated⟩
  · rw [rewriteSource.eq_def]
    dsimp only
    split <;> split <;> rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetGuard]
  · rw [evaluate_applyOp_var op acc (.ifThenElse cond yes no) env2 target env2[acc] lookup, targetIf]

/-- Conditional simulation with optimization disabled. Both branches use
the same induction hypotheses as the source conditional case. -/
theorem rewriteTail_if_noOptimization {C F : Type} (cond yes no : Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (guardIH : rewriteTailProperty (C := C) (F := F) [cond])
    (yesIH : rewriteTailProperty (C := C) (F := F) [yes])
    (noIH : rewriteTailProperty (C := C) (F := F) [no])
    (hyp : rewriteTailHyp [.ifThenElse cond yes no] source env1 result sourceNext
      false target acc env2 loc ts ty) :
    rewriteTailPost [.ifThenElse cond yes no] source env1 result sourceNext
      false target acc env2 loc ts ty := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  cases guardRun : BviSem.evaluate [cond] env1 source with
  | mk guardResult middle =>
    cases guardResult with
    | err error =>
      exact rewriteTail_if_guard_error cond yes no source env1 result sourceNext false target acc env2
        loc ts ty guardIH ⟨run, envRelated, related, types, by simp, notTypeError⟩ error middle guardRun
    | val values =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton cond env1 source middle values guardRun
      have guardHyp : rewriteTailHyp [cond] source env1 (.val [value]) middle false
          target acc env2 loc ts ty := ⟨guardRun, envRelated, related, types, by simp, by simp⟩
      obtain ⟨targetMiddle, targetGuard, middleRelated, _⟩ :=
        guardIH source env1 (.val [value]) middle false target acc env2 loc ts ty guardHyp
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, guardRun] at run
      change (match asBool value with
        | none => (.err (.abort .typeError), middle)
        | some true => BviSem.evaluate [yes] env1 middle
        | some false => BviSem.evaluate [no] env1 middle) = (result, sourceNext) at run
      cases truth : asBool value with
      | none =>
        simp [truth] at run
        exact (notTypeError run.1.symm).elim
      | some truthValue =>
        cases truthValue with
        | false =>
          have branchRun : BviSem.evaluate [no] env1 middle = (result, sourceNext) := by
            simpa [truth] using run
          have branchHyp : rewriteTailHyp [no] middle env1 result sourceNext false
              targetMiddle acc env2 loc ts ty :=
            ⟨branchRun, envRelated, middleRelated, types, by simp, notTypeError⟩
          obtain ⟨targetNext, targetBranch, finalRelated, _⟩ :=
            noIH middle env1 result sourceNext false targetMiddle acc env2 loc ts ty branchHyp
          refine ⟨targetNext, ?_, finalRelated, by simp⟩
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetGuard]
          change (match asBool value with
            | none => ((.err (.abort .typeError) : BviSem.BviResult), targetMiddle)
            | some true => BviSem.evaluate [yes] env2 targetMiddle
            | some false => BviSem.evaluate [no] env2 targetMiddle) = _
          simpa [truth] using targetBranch
        | true =>
          have branchRun : BviSem.evaluate [yes] env1 middle = (result, sourceNext) := by
            simpa [truth] using run
          have branchHyp : rewriteTailHyp [yes] middle env1 result sourceNext false
              targetMiddle acc env2 loc ts ty :=
            ⟨branchRun, envRelated, middleRelated, types, by simp, notTypeError⟩
          obtain ⟨targetNext, targetBranch, finalRelated, _⟩ :=
            yesIH middle env1 result sourceNext false targetMiddle acc env2 loc ts ty branchHyp
          refine ⟨targetNext, ?_, finalRelated, by simp⟩
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetGuard]
          change (match asBool value with
            | none => ((.err (.abort .typeError) : BviSem.BviResult), targetMiddle)
            | some true => BviSem.evaluate [yes] env2 targetMiddle
            | some false => BviSem.evaluate [no] env2 targetMiddle) = _
          simpa [truth] using targetBranch

/-- Complete conditional case of the source-shaped tail-rewrite simulation. -/
theorem rewriteTail_if {C F : Type} (cond yes no : Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (guardIH : rewriteTailProperty (C := C) (F := F) [cond])
    (yesIH : rewriteTailProperty (C := C) (F := F) [yes])
    (noIH : rewriteTailProperty (C := C) (F := F) [no])
    (hyp : rewriteTailHyp [.ifThenElse cond yes no] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.ifThenElse cond yes no] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  cases optimized with
  | false =>
    exact rewriteTail_if_noOptimization cond yes no source env1 result sourceNext target acc env2
      loc ts ty guardIH yesIH noIH hyp
  | true =>
    obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
    cases guardRun : BviSem.evaluate [cond] env1 source with
    | mk guardResult middle =>
      cases guardResult with
      | err error =>
        exact rewriteTail_if_guard_error cond yes no source env1 result sourceNext true target acc env2
          loc ts ty guardIH ⟨run, envRelated, related, types, by simp, notTypeError⟩ error middle guardRun
      | val values =>
        obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton cond env1 source middle values guardRun
        have disabled := envRel_disable ty true acc env1 env2 envRelated
        have guardHyp : rewriteTailHyp [cond] source env1 (.val [value]) middle false
            target acc env2 loc ts ty := ⟨guardRun, disabled, related, types, by simp, by simp⟩
        obtain ⟨targetMiddle, targetGuard, middleRelated, _⟩ :=
          guardIH source env1 (.val [value]) middle false target acc env2 loc ts ty guardHyp
        cases truth : asBool value with
        | none =>
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, guardRun] at run
          change (match asBool value with
            | none => ((.err (.abort .typeError) : BviSem.BviResult), middle)
            | some true => BviSem.evaluate [yes] env1 middle
            | some false => BviSem.evaluate [no] env1 middle) = (result, sourceNext) at run
          simp [truth] at run
          exact (notTypeError run.1.symm).elim
        | some flag =>
          let selected := if flag then yes else no
          have branchRun : BviSem.evaluate [selected] env1 middle = (result, sourceNext) := by
            rw [evaluate_if_of_guard cond yes no env1 source middle value flag guardRun truth] at run
            exact run
          have branchTypes := tyRel_if_condition ts loc cond env1 source middle value types guardRun
          have branchHyp : rewriteTailHyp [selected] middle env1 result sourceNext true targetMiddle
              acc env2 loc (scanSing ts loc cond).1 ty :=
            ⟨branchRun, envRelated, middleRelated, branchTypes, by simp, notTypeError⟩
          have selectedIH : rewriteTailProperty (C := C) (F := F) [selected] := by
            cases flag <;> simp [selected, yesIH, noIH]
          obtain ⟨targetNext, targetBranch, finalRelated, _⟩ :=
            selectedIH middle env1 result sourceNext true targetMiddle acc env2 loc
              (scanSing ts loc cond).1 ty branchHyp
          refine ⟨targetNext, ?_, finalRelated, ?_⟩
          · rw [evaluate_if_of_guard cond yes no env2 target targetMiddle value flag targetGuard truth]
            exact targetBranch
          · intro _ op workerLoc code arity required
            simp only [List.headD_cons] at required ⊢
            obtain ⟨sourceCode, optCode, opTy, op1, outCtx, resultTy, scanBranch,
              scan, notAny, _, opTypeEq⟩ := required
            have globalScan : scanSing ts loc (.ifThenElse cond yes no) =
                (outCtx, resultTy, scanBranch, some op1) := by
              rw [scanExpr_single] at scan
              simpa using scan
            have specific : (scanSing ts loc (.ifThenElse cond yes no)).2.1 ≠ .any := by
              simpa [globalScan] using notAny
            have globalType := scanSing_choice_type (.ifThenElse cond yes no) ts loc op1
              (by rw [globalScan]) specific
            have sameType : (scanSing ts loc (.ifThenElse cond yes no)).2.1 = opType op := by
              exact globalType.symm.trans opTypeEq
            have sourceCodeNext := evaluate_lookup_preserved [cond] env1 source middle (.val [value])
              loc arity code guardRun sourceCode
            have targetGrowth := BviProps.evaluate_code_mono [cond] env2 target targetMiddle (.val [value]) targetGuard
            have targetCodeNext := optimizedCode_subspt loc arity code workerLoc target.code targetMiddle.code
              op optCode targetGrowth
            have member : selected = yes ∨ selected = no := by
              cases flag <;> simp [selected]
            obtain ⟨r, t1, t2, branchRewritten, branchApplied, rel1, rel2⟩ :=
              rewriteTail_if_branch ts loc workerLoc acc op cond yes no selected middle sourceNext env1
                targetMiddle env2 result ty code arity member selectedIH branchHyp sourceCodeNext
                targetCodeNext opTy specific sameType
            have accBound := (envRelated.2 rfl).2.1
            have lookup : env2[acc]? = some env2[acc] := by simp [accBound]
            have rewriteIf : (rewriteSource loc workerLoc op acc ts (.ifThenElse cond yes no)).2 =
                .ifThenElse cond
                  (if (rewriteSource loc workerLoc op acc (scanSing ts loc cond).1 yes).1 then
                    (rewriteSource loc workerLoc op acc (scanSing ts loc cond).1 yes).2
                   else applyOp op (.var acc) yes)
                  (if (rewriteSource loc workerLoc op acc (scanSing ts loc cond).1 no).1 then
                    (rewriteSource loc workerLoc op acc (scanSing ts loc cond).1 no).2
                   else applyOp op (.var acc) no) := by
              rw [rewriteSource.eq_def]
              dsimp only
              rw [scanExpr_single]
              simp only [List.headD_cons]
              rfl
            refine ⟨r, t1, t2, ?_, ?_, rel1, rel2⟩
            · rw [rewriteIf, evaluate_if_of_guard _ _ _ env2 target targetMiddle value flag targetGuard truth]
              cases flag <;> simpa [selected] using branchRewritten
            · rw [evaluate_applyOp_if op acc cond yes no env2 target env2[acc] lookup]
              rw [evaluate_if_of_guard _ _ _ env2 target targetMiddle value flag targetGuard truth]
              cases flag <;> simpa [selected] using branchApplied

/-- Ordinary operation evaluation is simulated when successful primitive
applications preserve state relations and primitive errors are type errors.
This Flapjack helper isolates those primitive obligations. -/
theorem evaluate_op_related {C F : Type} (operation : ClosLang.Op) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (appSuccess : ∀ (values : List Value) (s t : BviSem.BviState (Nat × C) F)
      (u : BviSem.BviState C F) (v : Value), stateRel s u →
      BviSem.doApp operation values s = .val (v, t) →
      ∃ u', BviSem.doApp operation values u = .val (v, u') ∧ stateRel t u')
    (appError : ∀ (values : List Value) (s : BviSem.BviState (Nat × C) F)
      (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet),
      BviSem.doApp operation values s = .err error → error = .abort .typeError)
    (hyp : rewriteTailHyp [.op operation args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    ∃ targetNext, BviSem.evaluate [.op operation args] env2 target = (result, targetNext) ∧
      stateRel sourceNext targetNext := by
  obtain ⟨run, envRelated, related, types, _, notTypeError⟩ := hyp
  have disabled := envRel_disable ty optimized acc env1 env2 envRelated
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases argsRun : BviSem.evaluate args env1 source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      simp only [argsRun] at run
      have ok : (.err error : BviSem.BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have argsHyp : rewriteTailHyp args source env1 (.err error) middle false
          target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, ok⟩
      obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
        argsIH source env1 (.err error) middle false target acc env2 loc ts ty argsHyp
      have same : (.err error, middle) = (result, sourceNext) := by simpa [argsRun] using run
      cases same
      refine ⟨targetMiddle, ?_, middleRelated⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
    | val values =>
      have argsHyp : rewriteTailHyp args source env1 (.val values) middle false
          target acc env2 loc ts ty := ⟨argsRun, disabled, related, types, by simp, by simp⟩
      obtain ⟨targetMiddle, targetArgs, middleRelated, _⟩ :=
        argsIH source env1 (.val values) middle false target acc env2 loc ts ty argsHyp
      cases applied : BviSem.doApp operation values.reverse middle with
      | err error =>
        have typeError := appError values.reverse middle error applied
        subst error
        simp [argsRun, applied] at run
        exact (notTypeError run.1.symm).elim
      | val pair =>
        obtain ⟨value, last⟩ := pair
        have same : (.val [value], last) = (result, sourceNext) := by simpa [argsRun, applied] using run
        cases same
        obtain ⟨targetNext, targetApplied, finalRelated⟩ :=
          appSuccess values.reverse middle sourceNext targetMiddle value middleRelated applied
        refine ⟨targetNext, ?_, finalRelated⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        dsimp only
        rw [targetApplied]

/-- Shared operation simulation for a primitive whose scan selects no
accumulator and whose only primitive error is the source type error. The
primitive correspondence is a premise of this Flapjack helper. -/
theorem rewriteTail_op_noChoice {C F : Type} (operation : ClosLang.Op) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (noChoice : (scanSing ts loc (.op operation args)).2.2.2 = none)
    (appSuccess : ∀ (values : List Value) (s t : BviSem.BviState (Nat × C) F)
      (u : BviSem.BviState C F) (v : Value), stateRel s u →
      BviSem.doApp operation values s = .val (v, t) →
      ∃ u', BviSem.doApp operation values u = .val (v, u') ∧ stateRel t u')
    (appError : ∀ (values : List Value) (s : BviSem.BviState (Nat × C) F)
      (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet),
      BviSem.doApp operation values s = .err error → error = .abort .typeError)
    (hyp : rewriteTailHyp [.op operation args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op operation args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨targetNext, targetRun, targetRelated⟩ :=
    evaluate_op_related operation args source env1 result sourceNext optimized target acc env2 loc ts ty
      argsIH appSuccess appError hyp
  apply rewriteTailPost_of_no_scan (.op operation args) source env1 result sourceNext
    optimized target targetNext acc env2 loc ts ty targetRun targetRelated
  intro tt resultTy branch op1 scan
  rw [scanExpr_single] at scan
  have scanEq : scanSing ts loc (.op operation args) = (tt, resultTy, branch, some op1) := by
    simpa using scan
  rw [scanEq] at noChoice
  simp at noChoice

/-- Complete label-operation case of the source-shaped simulation. -/
theorem rewriteTail_op_label {C F : Type} (label : Nat) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.label label) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.label label) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.label label) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_label label
  · exact doApp_label_error label
  · exact hyp

/-- Complete integer constant operation case of the source-shaped simulation. -/
theorem rewriteTail_op_intConst {C F : Type} (number : Int) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.intOp (.const number)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.intOp (.const number)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.intOp (.const number)) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_intConst number
  · exact doApp_intConst_error number
  · exact hyp

/-- Complete global-pointer read operation case of the source-shaped simulation. -/
theorem rewriteTail_op_globalsPtr {C F : Type}  (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.globOp .globalsPtr) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.globOp .globalsPtr) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.globOp .globalsPtr) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_globalsPtr
  · exact doApp_globalsPtr_error
  · exact hyp

/-- Global-slot reads preserve the rewrite simulation through related stores. -/
theorem rewriteTail_op_global {C F : Type} (index : Nat) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.globOp (.global index)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.globOp (.global index)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.globOp (.global index)) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_global index
  · exact doApp_global_error index
  · exact hyp

/-- Global-slot writes preserve the rewrite simulation through related stores. -/
theorem rewriteTail_op_setGlobal {C F : Type} (index : Nat) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.globOp (.setGlobal index)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.globOp (.setGlobal index)) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.globOp (.setGlobal index)) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_setGlobal index
  · exact doApp_setGlobal_error index
  · exact hyp

/-- Complete global-pointer write operation case of the source-shaped simulation. -/
theorem rewriteTail_op_setGlobalsPtr {C F : Type}  (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.globOp .setGlobalsPtr) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.globOp .setGlobalsPtr) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.globOp .setGlobalsPtr) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_setGlobalsPtr
  · exact doApp_setGlobalsPtr_error
  · exact hyp

/-- Complete operation case for integer primitives that the accumulator scan
does not recognize, including subtraction, division, and comparisons. -/
theorem rewriteTail_op_nonAccumulatorInt {C F : Type} (operation : ClosLang.IntOp) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (notAccumulator : fromOp (.intOp operation) = .noop)
    (hyp : rewriteTailHyp [.op (.intOp operation) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.intOp operation) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.intOp operation) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice, notAccumulator]
    rfl
  · exact stateRel_doApp_intOp_success operation
  · exact doApp_intOp_error operation
  · exact hyp

/-- Complete operation case for word primitives, which do not select an
accumulator optimization. -/
theorem rewriteTail_op_word {C F : Type} (operation : ClosLang.WordOp) (args : List Bvi.Exp)
    (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (.wordOp operation) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (.wordOp operation) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (.wordOp operation) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice]
    simp [fromOp, BEq.beq, instBEqAssocOp.beq]
  · exact stateRel_doApp_wordOp_success operation
  · exact doApp_wordOp_error operation
  · exact hyp

/-- Accumulator operations are simulated when optimization is disabled,
regardless of whether their candidate check would succeed. -/
theorem rewriteTail_op_accumulator_noOptimization {C F : Type} (assoc : AssocOp)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (hyp : rewriteTailHyp [.op (toOp assoc) args] source env1 result sourceNext
      false target acc env2 loc ts ty) :
    rewriteTailPost [.op (toOp assoc) args] source env1 result sourceNext
      false target acc env2 loc ts ty := by
  obtain ⟨targetNext, run, related⟩ :=
    evaluate_op_related (toOp assoc) args source env1 result sourceNext false target acc env2 loc ts ty
      argsIH (stateRel_doApp_toOp assoc) (doApp_toOp_error_type assoc) hyp
  exact ⟨targetNext, run, related, by simp⟩

/-- Accumulator operations satisfy the source-shaped rewrite simulation:
a successful candidate uses the worker, while a failed check uses the
explicit accumulator fallback. The induction hypotheses cover the argument
list, the selected candidate's subexpressions, and smaller-clock callees. -/
theorem rewriteTail_op_accumulator {C F : Type} (assoc : AssocOp)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (subIH : ∀ op pure ticks callArgs,
      (.op (toOp assoc) args = applyOp op pure (.call ticks (some loc) callArgs none) ∨
        (op ≠ .append ∧ .op (toOp assoc) args = applyOp op (.call ticks (some loc) callArgs none) pure)) →
      rewriteTailProperty (C := C) (F := F) [pure] ∧ rewriteTailProperty (C := C) (F := F) callArgs)
    (clockIH : ∀ (body : Bvi.Exp) (called : BviSem.BviState (Nat × C) F)
      (values : List Value) (r : BviSem.BviResult) (last : BviSem.BviState (Nat × C) F),
      called.clock < source.clock → ∀ optimized (target : BviSem.BviState C F) acc env2 loc ts ty,
        rewriteTailHyp [body] called values r last optimized target acc env2 loc ts ty →
        rewriteTailPost [body] called values r last optimized target acc env2 loc ts ty)
    (hyp : rewriteTailHyp [.op (toOp assoc) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (toOp assoc) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  obtain ⟨targetNext, ordinary, finalRelated⟩ :=
    evaluate_op_related (toOp assoc) args source env1 result sourceNext optimized target acc env2 loc ts ty
      argsIH (stateRel_doApp_toOp assoc) (doApp_toOp_error_type assoc) hyp
  refine ⟨targetNext, ordinary, finalRelated, ?_⟩
  intro enabled op workerLoc body arity required
  obtain ⟨sourceCode, optCode, opTypeEq, _⟩ := required
  have envEnabled : envRel ty true acc env1 env2 := by simpa [enabled] using hyp.2.1
  cases checked : checkOp ts op loc (.op (toOp assoc) args) with
  | none =>
    obtain ⟨value, lookup, _⟩ := envRel_accumulator ty acc env1 env2 envEnabled
    have fallback := rewriteSource_op_fallback ts loc workerLoc acc op (toOp assoc) args (.inr checked)
    simpa only [List.headD_cons] using
      evaluate_rewrite_fallback op loc workerLoc acc ts (.op (toOp assoc) args) env2 sourceNext target targetNext
        result value lookup ordinary finalRelated fallback
  | some candidate =>
    simpa only [List.headD_cons] using
      evaluate_checked_worker_candidate loc arity workerLoc acc body (.op (toOp assoc) args) candidate op
        env1 env2 source sourceNext target ts ty result (subIH op) clockIH envEnabled hyp.2.2.1 hyp.2.2.2.1
        opTypeEq sourceCode optCode checked hyp.1 hyp.2.2.2.2.2

/-- Complete accumulator-operation case when the source candidate check
finds no recursive call. -/
theorem rewriteTail_op_accumulator_noCandidate {C F : Type} (assoc : AssocOp)
    (args : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F) (env1 : List Value)
    (result : BviSem.BviResult) (sourceNext : BviSem.BviState (Nat × C) F)
    (optimized : Bool) (target : BviSem.BviState C F) (acc : Nat) (env2 : List Value)
    (loc : Nat) (ts : List ValueType) (ty : ValueType)
    (argsIH : rewriteTailProperty (C := C) (F := F) args)
    (noCandidate : checkOp ts assoc loc (.op (toOp assoc) args) = none)
    (hyp : rewriteTailHyp [.op (toOp assoc) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty) :
    rewriteTailPost [.op (toOp assoc) args] source env1 result sourceNext
      optimized target acc env2 loc ts ty := by
  apply rewriteTail_op_noChoice (toOp assoc) args source env1 result sourceNext
    optimized target acc env2 loc ts ty argsIH
  · rw [scanSing_op_choice, fromOp_toOp]
    cases assoc <;> simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx]
  · exact stateRel_doApp_toOp assoc
  · exact doApp_toOp_error_type assoc
  · exact hyp

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
