import Flapjack.Compiler.Backend.BviToData.Proofs.CompileSource
import Flapjack.Compiler.Backend.BviToData.Proofs.Variables
import Flapjack.Compiler.Backend.BviToData.Proofs.Result
import Flapjack.Compiler.Backend.Semantics.DataSem.Control
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateLength

/-! The BVI-to-data compiler simulation, factored along the source cases. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

def isException (r : BviSem.BviResult) : Prop :=
  ∃ v, r = .err (.raise (.exn v))

def isReturn (r : BviSem.BviResult) : Prop :=
  ∃ vs, r = .err (.raise (.ret vs))

def isResult (r : BviSem.BviResult) : Prop :=
  ∃ vs, r = .val vs

/-- The source theorem's result-dependent obligations. This is factored
infrastructure, pending review of the BVI evaluator and the complete proof. -/
def correctOutcome {C F : Type} (res : BviSem.BviResult)
    (t1 t2 : DataSem.State C F) (n next : Nat) (corr live vs : List Nat)
    (env : List BvlSem.Value) (tail : Bool)
    (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls : Option Nat) : Prop :=
  match pres with
  | some r =>
    (¬isReturn res → dataToBviResult r = res) ∧
    (isReturn res → ∃ values, r = .val values ∧ res = .err (.raise (.ret (values.map dataToBviValue)))) ∧
    ((isResult res ∨ isReturn res) → t1.stack = t2.stack ∧ t1.handler = t2.handler) ∧
    (isResult res → tail = true) ∧
    (isException res → DataSem.jumpExc { t2 with stack := t1.stack, handler := t1.handler } =
      some { t2 with localsSize := ls })
  | none =>
    tail = false ∧ n ≤ next ∧ (∀ v ∈ vs, v < next) ∧
    (∀ k, next ≤ k → sptLookup k t2.locals = none) ∧
    DataProps.varCorr env corr (sptMap dataToBviValue t2.locals) ∧
    (∀ k x, sptLookup k t2.locals = some x → k < next) ∧
    (∀ k x, sptLookup k t1.locals = some x → (k ∉ live → k ∈ corr) →
      sptLookup k t2.locals = some x) ∧
    t1.stack = t2.stack ∧ t1.handler = t2.handler ∧
    (DataSem.jumpExc t1 ≠ none → DataSem.jumpExc t2 ≠ none) ∧
    match res with
    | .val values => DataProps.varCorr values vs (sptMap dataToBviValue t2.locals)
    | _ => False

private theorem varCorr_member {α : Type} {values : List α} {names : List Nat} {env : Spt α}
    (related : DataProps.varCorr values names env) :
    ∀ name ∈ names, ∃ value, DataSem.getVar name env = some value := by
  induction related with
  | nil => simp
  | @cons name value names values lookup rest ih =>
    intro key member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨value, lookup⟩
    · exact ih key member

/-- A continuing compilation preserves each live local and supplies every
result local for the next compilation. This is simulation infrastructure for
the source list case. -/
theorem correctOutcome_live {C F : Type} (values : List BvlSem.Value)
    (t1 t2 : DataSem.State C F) (n next : Nat) (corr live vs : List Nat)
    (env : List BvlSem.Value) (ls : Option Nat)
    (outcome : correctOutcome (.val values) t1 t2 n next corr live vs env false none ls)
    (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    ∀ v ∈ vs ++ live, sptLookup v t2.locals ≠ none := by
  rcases outcome with ⟨_, _, _, _, _, _, preserved, _, _, _, resultVars⟩
  intro v member
  simp only [List.mem_append] at member
  rcases member with resultMember | liveMember
  · have read := varCorr_member resultVars v resultMember
    rcases read with ⟨value, read⟩
    simp only [DataSem.getVar, sptLookup_sptMap] at read
    cases found : sptLookup v t2.locals with
    | none => simp [found] at read
    | some x => simp
  · cases found : sptLookup v t1.locals with
    | none => exact False.elim (livePresent v liveMember found)
    | some value =>
      have keep := preserved v value found (by intro missing; exact False.elim (missing liveMember))
      rw [keep]
      simp

/-- Two continuing non-tail expression compilations compose their complete
local-state obligations. The second compilation keeps the first result name
live, as required by the source list traversal. -/
theorem correctOutcome_cons {C F : Type} (head : BvlSem.Value) (tailValues : List BvlSem.Value)
    (t1 t2 t3 : DataSem.State C F) (n n1 n2 : Nat) (corr live names : List Nat)
    (name : Nat) (env : List BvlSem.Value) (ls1 ls2 : Option Nat)
    (first : correctOutcome (.val [head]) t1 t2 n n1 corr live [name] env false none ls1)
    (rest : correctOutcome (.val tailValues) t2 t3 n1 n2 corr (name :: live) names env false none ls2) :
    correctOutcome (.val (head :: tailValues)) t1 t3 n n2 corr live (name :: names) env false none ls2 := by
  rcases first with ⟨_, nBound, nameBound, _, _, _, preserve1, stack1, handler1, jump1, firstVars⟩
  rcases rest with ⟨_, nextBound, namesBound, fresh2, env2, localBound2, preserve2, stack2, handler2, jump2, restVars⟩
  have headRead : DataSem.getVar name (sptMap dataToBviValue t2.locals) = some head := by
    cases firstVars with
    | cons lookup _ => exact lookup
  have headRead' : DataSem.getVar name (sptMap dataToBviValue t3.locals) = some head := by
    simp only [DataSem.getVar, sptLookup_sptMap] at headRead ⊢
    cases found : sptLookup name t2.locals with
    | none => simp [found] at headRead
    | some value =>
      have keep := preserve2 name value found (by simp)
      rw [keep]
      simpa [found] using headRead
  simp only [correctOutcome, true_and, List.mem_cons]
  refine ⟨Nat.le_trans nBound nextBound, ?_, fresh2, env2, localBound2, ?_, stack1.trans stack2,
    handler1.trans handler2, fun h => jump2 (jump1 h), ?_⟩
  · intro v member
    rcases member with rfl | member
    · exact Nat.lt_of_lt_of_le (nameBound v (by simp)) nextBound
    · exact namesBound v member
  · intro k x lookup needed
    have firstKeep := preserve1 k x lookup needed
    apply preserve2 k x firstKeep
    intro missing
    apply needed
    intro liveMember
    exact missing (by simp [liveMember])
  · exact List.Forall₂.cons headRead' restVars

/-- A stopped recursive continuation preserves the first compilation's
stack and handler invariants, including the exception jump obligation. -/
theorem correctOutcome_stop_after_continue {C F : Type} (head : BvlSem.Value)
    (res : BviSem.BviResult) (t1 tmid t2 : DataSem.State C F)
    (n nmid next name : Nat) (corr live names : List Nat) (env : List BvlSem.Value)
    (result : Result (List DataSem.Value) DataSem.Value) (ls1 ls2 : Option Nat)
    (first : correctOutcome (.val [head]) t1 tmid n nmid corr live [name] env false none ls1)
    (rest : correctOutcome res tmid t2 nmid next corr (name :: live) names env false (some result) ls2) :
    correctOutcome res t1 t2 n next corr live (name :: names) env false (some result) ls2 := by
  rcases first with ⟨_, _, _, _, _, _, _, stack, handler, _, _⟩
  rcases rest with ⟨projection, returned, preserved, tail, exception⟩
  refine ⟨projection, returned, ?_, tail, ?_⟩
  · intro resultOrReturn
    obtain ⟨stackRest, handlerRest⟩ := preserved resultOrReturn
    exact ⟨stack.trans stackRest, handler.trans handlerRest⟩
  · intro raised
    simpa only [stack, handler] using exception raised

/-- Sequential data evaluation needs no clock adjustment when the first
result's clock is bounded by the initial clock. -/
theorem evaluateSeq_continue {C F : Type} (first rest : DataLang.Prog)
    (t1 t2 : DataSem.State C F) (result : DataSem.EvalResult C F)
    (firstRun : DataSem.evaluate first t1 = (none, t2))
    (clockBound : t2.clock ≤ t1.clock)
    (restRun : DataSem.evaluate rest t2 = result) :
    DataSem.evaluate (.seq first rest) t1 = result := by
  simp [DataSem.evaluate, firstRun, DataSem.fixClock, Nat.min_eq_right clockBound, restRun]

/-- A stopped first program prevents the second program from running. -/
theorem evaluateSeq_stop {C F : Type} (first rest : DataLang.Prog)
    (t1 t2 : DataSem.State C F) (result : Result (List DataSem.Value) DataSem.Value)
    (firstRun : DataSem.evaluate first t1 = (some result, t2))
    (clockBound : t2.clock ≤ t1.clock) :
    DataSem.evaluate (.seq first rest) t1 = (some result, t2) := by
  simp [DataSem.evaluate, firstRun, DataSem.fixClock, Nat.min_eq_right clockBound]

/-- Successful non-tail list composition: the two recursive simulations
combine with the real BVI clock bound into one source and target execution.
The other result cases and the full inductive theorem remain open. -/
theorem compileCorrect_cons_success {C F : Type} (x y : Bvi.Exp) (xs : List Bvi.Exp)
    (env : List BvlSem.Value) (head : BvlSem.Value) (values : List BvlSem.Value)
    (s1 smid s2 : BviSem.BviState C F) (t1 tmid t2 : DataSem.State C F)
    (n nmid next name : Nat) (corr live names : List Nat) (first rest : DataLang.Prog)
    (ls1 ls2 : Option Nat)
    (sourceFirst : BviSem.evaluate [x] env s1 = (.val [head], smid))
    (sourceRest : BviSem.evaluate (y :: xs) env smid = (.val values, s2))
    (compileFirst : compileSource n corr false live [x] = (first, [name], nmid))
    (compileRest : compileSource nmid corr false (name :: live) (y :: xs) = (rest, names, next))
    (targetFirst : DataSem.evaluate first t1 = (none, tmid))
    (targetRest : DataSem.evaluate rest tmid = (none, t2))
    (initialRel : stateRel s1 t1) (middleRel : stateRel smid tmid) (finalRel : stateRel s2 t2)
    (firstOutcome : correctOutcome (.val [head]) t1 tmid n nmid corr live [name] env false none ls1)
    (restOutcome : correctOutcome (.val values) tmid t2 nmid next corr (name :: live) names env false none ls2) :
    BviSem.evaluate (x :: y :: xs) env s1 = (.val (head :: values), s2) ∧
    compileSource n corr false live (x :: y :: xs) = (.seq first rest, name :: names, next) ∧
    DataSem.evaluate (.seq first rest) t1 = (none, t2) ∧ stateRel s2 t2 ∧
    correctOutcome (.val (head :: values)) t1 t2 n next corr live (name :: names) env false none ls2 := by
  have sourceBound := BviSem.evaluate_clock_le [x] env s1
  rw [sourceFirst] at sourceBound
  have targetBound : tmid.clock ≤ t1.clock := by
    simpa [← initialRel.1, ← middleRel.1] using sourceBound
  refine ⟨?_, ?_, evaluateSeq_continue first rest t1 tmid _ targetFirst targetBound targetRest, finalRel, ?_⟩
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate, sourceFirst, sourceRest]
    rfl
  · simp [compileSource, compileFirst, compileRest, Flapjack.holHd]
  · exact correctOutcome_cons head values t1 tmid t2 n nmid next corr live names name env ls1 ls2 firstOutcome restOutcome

/-- An error from the first expression stops the entire compiled list. This
composes the first recursive simulation without evaluating the remaining
source expressions or target code. -/
theorem compileCorrect_cons_firstStop {C F : Type} (x y : Bvi.Exp) (xs : List Bvi.Exp)
    (env : List BvlSem.Value) (error : ErrorResult BviSem.ExnOrRet)
    (s1 s2 : BviSem.BviState C F) (t1 t2 : DataSem.State C F)
    (n nmid next name : Nat) (corr live names : List Nat) (first rest : DataLang.Prog)
    (result : Result (List DataSem.Value) DataSem.Value) (ls : Option Nat)
    (sourceFirst : BviSem.evaluate [x] env s1 = (.err error, s2))
    (compileFirst : compileSource n corr false live [x] = (first, [name], nmid))
    (compileRest : compileSource nmid corr false (name :: live) (y :: xs) = (rest, names, next))
    (targetFirst : DataSem.evaluate first t1 = (some result, t2))
    (initialRel : stateRel s1 t1) (finalRel : stateRel s2 t2)
    (outcome : correctOutcome (.err error) t1 t2 n nmid corr live [name] env false (some result) ls) :
    BviSem.evaluate (x :: y :: xs) env s1 = (.err error, s2) ∧
    compileSource n corr false live (x :: y :: xs) = (.seq first rest, name :: names, next) ∧
    DataSem.evaluate (.seq first rest) t1 = (some result, t2) ∧ stateRel s2 t2 ∧
    correctOutcome (.err error) t1 t2 n next corr live (name :: names) env false (some result) ls := by
  have sourceBound := BviSem.evaluate_clock_le [x] env s1
  rw [sourceFirst] at sourceBound
  have targetBound : t2.clock ≤ t1.clock := by
    simpa [← initialRel.1, ← finalRel.1] using sourceBound
  refine ⟨?_, ?_, evaluateSeq_stop first rest t1 t2 result targetFirst targetBound, finalRel, ?_⟩
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate, sourceFirst]
  · simp [compileSource, compileFirst, compileRest, Flapjack.holHd]
  · exact outcome

/-- The first expression continues and the remaining expression list stops.
The source and target both return that stop, with the source theorem's full
result obligations transferred through the first compilation. -/
theorem compileCorrect_cons_restStop {C F : Type} (x y : Bvi.Exp) (xs : List Bvi.Exp)
    (env : List BvlSem.Value) (head : BvlSem.Value) (error : ErrorResult BviSem.ExnOrRet)
    (s1 smid s2 : BviSem.BviState C F) (t1 tmid t2 : DataSem.State C F)
    (n nmid next name : Nat) (corr live names : List Nat) (first rest : DataLang.Prog)
    (result : Result (List DataSem.Value) DataSem.Value) (ls1 ls2 : Option Nat)
    (sourceFirst : BviSem.evaluate [x] env s1 = (.val [head], smid))
    (sourceRest : BviSem.evaluate (y :: xs) env smid = (.err error, s2))
    (compileFirst : compileSource n corr false live [x] = (first, [name], nmid))
    (compileRest : compileSource nmid corr false (name :: live) (y :: xs) = (rest, names, next))
    (targetFirst : DataSem.evaluate first t1 = (none, tmid))
    (targetRest : DataSem.evaluate rest tmid = (some result, t2))
    (initialRel : stateRel s1 t1) (middleRel : stateRel smid tmid) (finalRel : stateRel s2 t2)
    (firstOutcome : correctOutcome (.val [head]) t1 tmid n nmid corr live [name] env false none ls1)
    (restOutcome : correctOutcome (.err error) tmid t2 nmid next corr (name :: live) names env false (some result) ls2) :
    BviSem.evaluate (x :: y :: xs) env s1 = (.err error, s2) ∧
    compileSource n corr false live (x :: y :: xs) = (.seq first rest, name :: names, next) ∧
    DataSem.evaluate (.seq first rest) t1 = (some result, t2) ∧ stateRel s2 t2 ∧
    correctOutcome (.err error) t1 t2 n next corr live (name :: names) env false (some result) ls2 := by
  have sourceBound := BviSem.evaluate_clock_le [x] env s1
  rw [sourceFirst] at sourceBound
  have targetBound : tmid.clock ≤ t1.clock := by
    simpa [← initialRel.1, ← middleRel.1] using sourceBound
  refine ⟨?_, ?_, evaluateSeq_continue first rest t1 tmid _ targetFirst targetBound targetRest, finalRel, ?_⟩
  · rw [BviSem.evaluate, BviSem.fixClock_evaluate, sourceFirst, sourceRest]
  · simp [compileSource, compileFirst, compileRest, Flapjack.holHd]
  · exact correctOutcome_stop_after_continue head (.err error) t1 tmid t2 n nmid next name corr live names env result ls1 ls2 firstOutcome restOutcome

/-- Empty-expression case of the full source simulation invariant. This case
is not tagged as a HOL port while the source-shaped BVI evaluator awaits its
own correspondence review. -/
theorem compileCorrect_nil {C F : Type} (env : List BvlSem.Value)
    (s1 s2 : BviSem.BviState C F) (res : BviSem.BviResult)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (run : BviSem.evaluate [] env s1 = (res, s2))
    (notTypeError : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (tailShape : ([] : List Bvi.Exp).length ≠ 1 → tail = false)
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1)
    (_livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException res → DataSem.jumpExc t1 ≠ none) :
    ∃ t2 prog pres vs next ls,
      compileSource n corr tail live [] = (prog, vs, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome res t1 t2 n next corr live vs env tail pres ls := by
  simp only [BviSem.evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  have notTail : tail = false := tailShape (by simp)
  refine ⟨t1, .skip, none, [], n, none, ?_, ?_, related, ?_⟩
  · simp [compileSource]
  · simp [DataSem.evaluate]
  · simp only [correctOutcome, notTail, true_and, le_refl, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, vars]
    refine ⟨fresh, ?_, ?_, ?_⟩
    · intro k x lookup
      by_contra bound
      have absent := fresh k (Nat.le_of_not_gt bound)
      rw [lookup] at absent
      contradiction
    · intro k x lookup _
      exact lookup
    · exact ⟨fun h => h, List.Forall₂.nil⟩

/-- Variable case of the source simulation invariant, including both tail
and non-tail compilation. The evaluator still awaits correspondence review. -/
theorem compileCorrect_var {C F : Type} (index : Nat) (env : List BvlSem.Value)
    (s1 s2 : BviSem.BviState C F) (res : BviSem.BviResult)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (run : BviSem.evaluate [.var index] env s1 = (res, s2))
    (notTypeError : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (_tailShape : ([.var index] : List Bvi.Exp).length ≠ 1 → tail = false)
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1)
    (_livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (_exceptionJump : isException res → DataSem.jumpExc t1 ≠ none) :
    ∃ t2 prog pres vs next ls,
      compileSource n corr tail live [.var index] = (prog, vs, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome res t1 t2 n next corr live vs env tail pres ls := by
  cases valueAt : env[index]? with
  | none =>
    simp [BviSem.evaluate, valueAt] at run
    rcases run with ⟨rfl, _⟩
    exact False.elim (notTypeError rfl)
  | some value =>
    simp [BviSem.evaluate, valueAt] at run
    rcases run with ⟨rfl, rfl⟩
    obtain ⟨name, dataValue, nameAt, read, projected, _, _, _⟩ :=
      evaluateVar_nonTail index n corr live env s1 t1 value related vars (by simp [BviSem.evaluate, valueAt])
    cases tail with
    | false =>
      refine ⟨t1, .skip, none, [name], max n (name + 1), none, ?_, ?_, related, ?_⟩
      · simp [compileSource, nameAt]
      · simp [DataSem.evaluate]
      · simp only [correctOutcome, true_and, List.mem_singleton, forall_eq, vars]
        refine ⟨Nat.le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro k hk
          exact fresh k (Nat.le_trans (Nat.le_max_left _ _) hk)
        · intro k x lookup
          by_contra bound
          have absent := fresh k (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_not_gt bound))
          rw [lookup] at absent
          contradiction
        · intro k x lookup _
          exact lookup
        · exact fun h => h
        · constructor
          · simpa [DataSem.getVar, sptLookup_sptMap, read, projected] using congrArg (Option.map dataToBviValue) read
          · constructor
    | true =>
      refine ⟨DataSem.flushState false t1, .return [name], some (.val [dataValue]), [n], n + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, nameAt]
      · simp [DataSem.evaluate, DataSem.getVars, read]
      · simpa [stateRel, DataSem.flushState] using related
      · simp [correctOutcome, isReturn, isResult, isException, dataToBviResult, projected, DataSem.flushState]

end Flapjack.Compiler.Backend.BviToData
