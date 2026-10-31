import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

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
