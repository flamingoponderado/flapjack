import Flapjack.Compiler.Backend.BviToData.Proofs.CompileSource
import Flapjack.Compiler.Backend.BviToData.Proofs.Variables
import Flapjack.Compiler.Backend.BviToData.Proofs.Result
import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBool
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

private theorem varCorr_append {α : Type} {values1 values2 : List α} {names1 names2 : List Nat}
    {env : Spt α} (first : DataProps.varCorr values1 names1 env)
    (second : DataProps.varCorr values2 names2 env) :
    DataProps.varCorr (values1 ++ values2) (names1 ++ names2) env := by
  induction first with
  | nil => exact second
  | cons lookup _ ih => exact .cons lookup ih

private theorem varCorr_append_right {α : Type} (values1 values2 : List α) (names1 names2 : List Nat)
    (env : Spt α) (lengths : values1.length = names1.length)
    (related : DataProps.varCorr (values1 ++ values2) (names1 ++ names2) env) :
    DataProps.varCorr values2 names2 env := by
  induction values1 generalizing names1 with
  | nil =>
    cases names1 with
    | nil => exact related
    | cons _ _ => simp at lengths
  | cons value values ih =>
    cases names1 with
    | nil => simp at lengths
    | cons name names =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      cases related with
      | cons _ rest => exact ih names lengths rest

private theorem varCorr_insert_absent {α : Type} {values : List α} {names : List Nat}
    {env : Spt α} (related : DataProps.varCorr values names env)
    (dest : Nat) (value : α) (absent : sptLookup dest env = none) :
    DataProps.varCorr values names (sptInsert dest value env) := by
  induction related with
  | nil => constructor
  | @cons name first names values lookup rest ih =>
    have different : name ≠ dest := by
      intro same
      subst name
      simp [DataSem.getVar, absent] at lookup
    constructor
    · simpa [DataSem.getVar, sptLookup_sptInsert_ne dest name value env different] using lookup
    · exact ih

private theorem jumpExc_setVar_ne_none {C F : Type} (state : DataSem.State C F)
    (name : Nat) (value : DataSem.Value) :
    DataSem.jumpExc (DataSem.setVar name value state) ≠ none ↔ DataSem.jumpExc state ≠ none := by
  simp only [DataSem.jumpExc, DataSem.setVar]
  by_cases h : state.handler < state.stack.length
  · simp only [h, ite_true]
  · simp [h]

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

/-- Compose the local-state obligations for a successful binding list and
its body, dropping the temporary bindings from the outer correspondence. -/
theorem correctOutcome_let {C F : Type} (values : List BvlSem.Value) (res : BviSem.BviResult)
    (t1 tmid t2 : DataSem.State C F) (n nmid next : Nat) (corr live boundNames names : List Nat)
    (env : List BvlSem.Value) (tail : Bool)
    (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls1 ls2 : Option Nat)
    (first : correctOutcome (.val values) t1 tmid n nmid corr live boundNames env false none ls1)
    (body : correctOutcome res tmid t2 nmid next (boundNames ++ corr) live names (values ++ env) tail pres ls2) :
    correctOutcome res t1 t2 n next corr live names env tail pres ls2 := by
  rcases first with ⟨_, nBound, _, _, _, _, preserve1, stack1, handler1, jump1, firstVars⟩
  cases pres with
  | some result =>
    rcases body with ⟨projection, returned, preserved, tailResult, exception⟩
    refine ⟨projection, returned, ?_, tailResult, ?_⟩
    · intro resultOrReturn
      obtain ⟨stack2, handler2⟩ := preserved resultOrReturn
      exact ⟨stack1.trans stack2, handler1.trans handler2⟩
    · intro raised
      simpa only [stack1, handler1] using exception raised
  | none =>
    rcases body with ⟨notTail, nextBound, namesBound, fresh, envBound, localBound, preserve2,
      stack2, handler2, jump2, resultVars⟩
    have lengths : values.length = boundNames.length := firstVars.length_eq.symm
    have envOriginal := varCorr_append_right values env boundNames corr (sptMap dataToBviValue t2.locals) lengths envBound
    refine ⟨notTail, Nat.le_trans nBound nextBound, namesBound, fresh, envOriginal, localBound, ?_,
      stack1.trans stack2, handler1.trans handler2, fun h => jump2 (jump1 h), resultVars⟩
    intro key value lookup needed
    have firstKeep := preserve1 key value lookup needed
    apply preserve2 key value firstKeep
    intro missing
    exact List.mem_append_right boundNames (needed missing)

/-- Compose a continuing preliminary evaluation with a second simulation
that retains the same environment and live-variable set. -/
theorem correctOutcome_seq {C F : Type} (values : List BvlSem.Value) (res : BviSem.BviResult)
    (t1 tmid t2 : DataSem.State C F) (n nmid next : Nat) (corr live firstNames names : List Nat)
    (env : List BvlSem.Value) (tail : Bool)
    (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls1 ls2 : Option Nat)
    (first : correctOutcome (.val values) t1 tmid n nmid corr live firstNames env false none ls1)
    (second : correctOutcome res tmid t2 nmid next corr live names env tail pres ls2) :
    correctOutcome res t1 t2 n next corr live names env tail pres ls2 := by
  rcases first with ⟨_, nBound, _, _, _, _, preserve1, stack1, handler1, jump1, _⟩
  cases pres with
  | some result =>
    rcases second with ⟨projection, returned, preserved, tailResult, exception⟩
    refine ⟨projection, returned, ?_, tailResult, ?_⟩
    · intro resultOrReturn
      obtain ⟨stack2, handler2⟩ := preserved resultOrReturn
      exact ⟨stack1.trans stack2, handler1.trans handler2⟩
    · intro raised
      simpa only [stack1, handler1] using exception raised
  | none =>
    rcases second with ⟨notTail, nextBound, namesBound, fresh, envVars, localBound, preserve2,
      stack2, handler2, jump2, resultVars⟩
    refine ⟨notTail, Nat.le_trans nBound nextBound, namesBound, fresh, envVars, localBound, ?_,
      stack1.trans stack2, handler1.trans handler2, fun h => jump2 (jump1 h), resultVars⟩
    intro key value lookup needed
    exact preserve2 key value (preserve1 key value lookup needed) needed

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
The assembled simulation is proved separately in `Proofs.Simulation`; HOL correspondence review remains open. -/
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

/-- The compiler invariant for a fixed source expression list and initial
state, with arbitrary target state and compiler parameters. This is proof
infrastructure for assembling the source evaluator induction. -/
def simulationFor {C F : Type} (xs : List Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F) : Prop :=
  ∀ (res : BviSem.BviResult) (s2 : BviSem.BviState C F) (t1 : DataSem.State C F)
    (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat),
    BviSem.evaluate xs env s1 = (res, s2) →
    res ≠ .err (.abort .typeError) →
    DataProps.varCorr env corr (sptMap dataToBviValue t1.locals) →
    (xs.length ≠ 1 → tail = false) →
    (∀ k, n ≤ k → sptLookup k t1.locals = none) →
    stateRel s1 t1 →
    (∀ v ∈ live, sptLookup v t1.locals ≠ none) →
    (isException res → DataSem.jumpExc t1 ≠ none) →
    ∃ t2 prog pres vs next ls,
      compileSource n corr tail live xs = (prog, vs, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome res t1 t2 n next corr live vs env tail pres ls

/-- The list case assembled from recursive compiler simulations. The second
induction premise applies to intermediate states reached by a successful
first expression. This remains untagged until the BVI evaluator is reviewed
and the assembled induction is in `Proofs.Simulation`. -/
theorem compileCorrect_cons {C F : Type} (x y : Bvi.Exp) (xs : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F)
    (ihFirst : simulationFor [x] env s1)
    (ihRest : ∀ (head : BvlSem.Value) (smid : BviSem.BviState C F),
      BviSem.evaluate [x] env s1 = (.val [head], smid) → simulationFor (y :: xs) env smid) :
    simulationFor (x :: y :: xs) env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  have notTail : tail = false := tailShape (by simp)
  subst tail
  generalize firstRun : BviSem.evaluate [x] env s1 = firstPair
  obtain ⟨firstResult, smid⟩ := firstPair
  cases firstResult with
  | err error =>
    have whole : BviSem.evaluate (x :: y :: xs) env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, firstRun]
    rw [whole] at run
    cases run
    obtain ⟨t2, first, pres, firstNames, nmid, ls, compiled, target, state, outcome⟩ :=
      ihFirst (.err error) s2 t1 n corr false live firstRun notTypeError vars (by simp) fresh related livePresent exceptionJump
    have len := compileSource_LENGTH n corr false live [x] first firstNames nmid compiled
    cases firstNames with
    | nil => simp at len
    | cons name restNames =>
      cases restNames with
      | cons name2 more => simp at len
      | nil =>
        cases pres with
        | none => simp [correctOutcome] at outcome
        | some result =>
          generalize restCompiled : compileSource nmid corr false (name :: live) (y :: xs) = restTriple
          obtain ⟨rest, names, next⟩ := restTriple
          obtain ⟨_, compiledAll, targetAll, stateAll, outcomeAll⟩ :=
            compileCorrect_cons_firstStop x y xs env error s1 s2 t1 t2 n nmid next name corr live names first rest result ls firstRun compiled restCompiled target related state outcome
          exact ⟨t2, .seq first rest, some result, name :: names, next, ls, compiledAll, targetAll, stateAll, outcomeAll⟩
  | val values =>
    obtain ⟨head, rfl⟩ := BviSem.evaluate_singleton x env s1 smid values firstRun
    obtain ⟨tmid, first, pres, firstNames, nmid, ls1, compiled, target, middleRel, outcome⟩ :=
      ihFirst (.val [head]) smid t1 n corr false live firstRun (by simp) vars (by simp) fresh related livePresent
        (by simp [isException])
    have len := compileSource_LENGTH n corr false live [x] first firstNames nmid compiled
    cases firstNames with
    | nil => simp at len
    | cons name restNames =>
      cases restNames with
      | cons name2 more => simp at len
      | nil =>
        cases pres with
        | some result => simp [correctOutcome, isResult] at outcome
        | none =>
          have firstOutcome := outcome
          have liveMid : ∀ v ∈ name :: live, sptLookup v tmid.locals ≠ none := by
            simpa using correctOutcome_live [head] t1 tmid n nmid corr live [name] env ls1 outcome livePresent
          rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, jumpMid, _⟩
          generalize restRun : BviSem.evaluate (y :: xs) env smid = restPair
          obtain ⟨restResult, slast⟩ := restPair
          cases restResult with
          | val tailValues =>
            have whole : BviSem.evaluate (x :: y :: xs) env s1 = (.val (head :: tailValues), slast) := by
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, firstRun, restRun]
              rfl
            rw [whole] at run
            cases run
            obtain ⟨t2, rest, pres, names, next, ls2, restCompiled, targetRest, finalRel, restOutcome⟩ :=
              ihRest head smid firstRun (.val tailValues) s2 tmid nmid corr false (name :: live) restRun (by simp) varsMid
                (by simp) freshMid middleRel liveMid (by simp [isException])
            cases pres with
            | some result => simp [correctOutcome, isResult] at restOutcome
            | none =>
              obtain ⟨_, compiledAll, targetAll, stateAll, outcomeAll⟩ :=
                compileCorrect_cons_success x y xs env head tailValues s1 smid s2 t1 tmid t2 n nmid next name corr live names first rest ls1 ls2 firstRun restRun compiled restCompiled target targetRest related middleRel finalRel firstOutcome restOutcome
              exact ⟨t2, .seq first rest, none, name :: names, next, ls2, compiledAll, targetAll, stateAll, outcomeAll⟩
          | err error =>
            have whole : BviSem.evaluate (x :: y :: xs) env s1 = (.err error, slast) := by
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, firstRun, restRun]
            rw [whole] at run
            cases run
            obtain ⟨t2, rest, pres, names, next, ls2, restCompiled, targetRest, finalRel, restOutcome⟩ :=
              ihRest head smid firstRun (.err error) s2 tmid nmid corr false (name :: live) restRun notTypeError varsMid
                (by simp) freshMid middleRel liveMid (fun h => jumpMid (exceptionJump h))
            cases pres with
            | none => simp [correctOutcome] at restOutcome
            | some result =>
              obtain ⟨_, compiledAll, targetAll, stateAll, outcomeAll⟩ :=
                compileCorrect_cons_restStop x y xs env head error s1 smid s2 t1 tmid t2 n nmid next name corr live names first rest result ls1 ls2 firstRun restRun compiled restCompiled target targetRest related middleRel finalRel firstOutcome restOutcome
              exact ⟨t2, .seq first rest, some result, name :: names, next, ls2, compiledAll, targetAll, stateAll, outcomeAll⟩

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

/-- The empty list satisfies the reusable evaluator induction invariant. -/
theorem simulationFor_nil {C F : Type} (env : List BvlSem.Value) (s1 : BviSem.BviState C F) :
    simulationFor [] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  exact compileCorrect_nil env s1 s2 res t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump

/-- A variable expression satisfies the reusable evaluator induction invariant. -/
theorem simulationFor_var {C F : Type} (index : Nat) (env : List BvlSem.Value) (s1 : BviSem.BviState C F) :
    simulationFor [.var index] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  exact compileCorrect_var index env s1 s2 res t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump

private theorem jumpExc_decClock {C F : Type} (state : DataSem.State C F) :
    DataSem.jumpExc (DataSem.decClock state) = (DataSem.jumpExc state).map DataSem.decClock := by
  simp only [DataSem.jumpExc, DataSem.decClock]
  by_cases h : state.handler < state.stack.length
  · simp only [h, ite_true]
    split <;> simp [DataSem.decClock]
  · simp [h]

private theorem outcome_decClock_initial {C F : Type} (res : BviSem.BviResult)
    (t1 t2 : DataSem.State C F) (n next : Nat) (corr live vs : List Nat)
    (env : List BvlSem.Value) (tail : Bool)
    (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls : Option Nat) :
    correctOutcome res (DataSem.decClock t1) t2 n next corr live vs env tail pres ls ↔
    correctOutcome res t1 t2 n next corr live vs env tail pres ls := by
  have sameJump : (DataSem.jumpExc (DataSem.decClock t1) ≠ none) ↔ DataSem.jumpExc t1 ≠ none := by
    rw [jumpExc_decClock]
    simp
  dsimp [DataSem.decClock] at sameJump
  cases pres <;> simp only [correctOutcome, DataSem.decClock, sameJump]

/-- The tick case of the compiler simulation, assuming the recursive
simulation at the decremented source clock. This remains untagged pending
the source evaluator correspondence review. -/
theorem simulationFor_tick {C F : Type} (body : Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F)
    (ih : s1.clock ≠ 0 → simulationFor [body] env (BviSem.decClock 1 s1)) :
    simulationFor [.tick body] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars tailShape fresh related livePresent exceptionJump
  by_cases clockZero : s1.clock = 0
  · have targetZero : t1.clock = 0 := related.1.symm.trans clockZero
    simp [BviSem.evaluate, clockZero] at run
    obtain ⟨rfl, rfl⟩ := run
    generalize compiled : compileSource n corr tail live [body] = triple
    obtain ⟨prog, names, next⟩ := triple
    refine ⟨DataSem.flushState true t1, .seq .tick prog, some (.err (.abort .timeoutError)), names, next, none, ?_, ?_, ?_, ?_⟩
    · simp [compileSource, compiled]
    · simp [DataSem.evaluate, targetZero, DataSem.fixClock, DataSem.flushState]
    · simpa [stateRel, DataSem.flushState] using related
    · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException]
  · have targetNonzero : t1.clock ≠ 0 := by simpa [← related.1] using clockZero
    have bodyRun : BviSem.evaluate [body] env (BviSem.decClock 1 s1) = (res, s2) := by
      simpa [BviSem.evaluate, clockZero] using run
    have jump : isException res → DataSem.jumpExc (DataSem.decClock t1) ≠ none := by
      intro raised
      rw [jumpExc_decClock]
      simpa using exceptionJump raised
    obtain ⟨t2, prog, pres, names, next, ls, compiled, target, finalRel, outcome⟩ :=
      ih clockZero res s2 (DataSem.decClock t1) n corr tail live bodyRun notTypeError
        (by simpa [DataSem.decClock] using vars) (by simp)
        (by simpa [DataSem.decClock] using fresh) (stateRel_decClock s1 t1 related)
        (by simpa [DataSem.decClock] using livePresent) jump
    refine ⟨t2, .seq .tick prog, pres, names, next, ls, ?_, ?_, finalRel, ?_⟩
    · simp [compileSource, compiled]
    · apply evaluateSeq_continue .tick prog t1 (DataSem.decClock t1) (pres, t2)
      · simp [DataSem.evaluate, targetNonzero]
      · simp [DataSem.decClock]
      · exact target
    · exact (outcome_decClock_initial res t1 t2 n next corr live names env tail pres ls).mp outcome

/-- Return expressions evaluate their argument list and then return its
projected values. This remains untagged pending the source evaluator review. -/
theorem simulationFor_return {C F : Type} (args : List Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.return args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argsResult, smid⟩ := pair
  cases argsResult with
  | err error =>
    simp [BviSem.evaluate, argsRun] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t2, prog, pres, names, next, ls, compiled, target, finalRel, outcome⟩ :=
      ih (.err error) smid t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result =>
      have sourceBound := BviSem.evaluate_clock_le args env s1
      rw [argsRun] at sourceBound
      have targetBound : t2.clock ≤ t1.clock := by
        simpa [← related.1, ← finalRel.1] using sourceBound
      refine ⟨t2, .seq prog (.return names), some result, [next], next + 1, ls, ?_, ?_, finalRel, ?_⟩
      · simp [compileSource, compiled]
      · exact evaluateSeq_stop prog (.return names) t1 t2 result target targetBound
      · simpa [correctOutcome, isResult] using outcome
  | val values =>
    simp [BviSem.evaluate, argsRun] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨tmid, prog, pres, names, next, ls, compiled, target, middleRel, outcome⟩ :=
      ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
        (by simp [isException])
    cases pres with
    | some result => simp [correctOutcome, isResult] at outcome
    | none =>
      rcases outcome with ⟨_, _, _, _, _, _, _, stack, handler, _, resultVars⟩
      obtain ⟨dataValues, read, projected⟩ := getVars_lift names values tmid.locals resultVars
      have sourceBound := BviSem.evaluate_clock_le args env s1
      rw [argsRun] at sourceBound
      have targetBound : tmid.clock ≤ t1.clock := by
        simpa [← related.1, ← middleRel.1] using sourceBound
      have returnRun : DataSem.evaluate (.return names) tmid =
          (some (.val dataValues), DataSem.flushState false tmid) := by
        simp [DataSem.evaluate, read]
      refine ⟨DataSem.flushState false tmid, .seq prog (.return names), some (.val dataValues), [next], next + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled]
      · exact evaluateSeq_continue prog (.return names) t1 tmid _ target targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using middleRel
      · simp [correctOutcome, isResult, isReturn, isException, DataSem.flushState, projected, stack, handler]

private theorem jumpExc_preserves {C F : Type} (s : BviSem.BviState C F)
    (before after : DataSem.State C F) (related : stateRel s before)
    (jump : DataSem.jumpExc before = some after) :
    stateRel s after ∧
    DataSem.jumpExc { after with stack := before.stack, handler := before.handler } = some after := by
  unfold DataSem.jumpExc at jump ⊢
  split at jump
  · split at jump
    · simp only [Option.some.injEq] at jump
      subst after
      constructor
      · simpa [stateRel] using related
      · simp_all
    · simp at jump
  · simp at jump

/-- Raise evaluates its operand, projects the raised value, and transfers
control through the corresponding exception frame. This remains untagged
pending the source evaluator review. -/
theorem simulationFor_raise {C F : Type} (body : Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F) (ih : simulationFor [body] env s1) :
    simulationFor [.raise body] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize bodyRun : BviSem.evaluate [body] env s1 = pair
  obtain ⟨bodyResult, smid⟩ := pair
  cases bodyResult with
  | err error =>
    simp [BviSem.evaluate, bodyRun] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t2, prog, pres, names, next, ls, compiled, target, finalRel, outcome⟩ :=
      ih (.err error) smid t1 n corr false live bodyRun notTypeError vars (by simp) fresh related livePresent exceptionJump
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result =>
      have sourceBound := BviSem.evaluate_clock_le [body] env s1
      rw [bodyRun] at sourceBound
      have targetBound : t2.clock ≤ t1.clock := by
        simpa [← related.1, ← finalRel.1] using sourceBound
      refine ⟨t2, .seq prog (.raise (Flapjack.holHd names)), some result, names, next, ls, ?_, ?_, finalRel, ?_⟩
      · simp [compileSource, compiled]
      · exact evaluateSeq_stop prog (.raise (Flapjack.holHd names)) t1 t2 result target targetBound
      · simpa [correctOutcome, isResult] using outcome
  | val values =>
    obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton body env s1 smid values bodyRun
    simp [BviSem.evaluate, bodyRun] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨tmid, prog, pres, names, next, ls, compiled, target, middleRel, outcome⟩ :=
      ih (.val [value]) smid t1 n corr false live bodyRun (by simp) vars (by simp) fresh related livePresent
        (by simp [isException])
    have len := compileSource_LENGTH n corr false live [body] prog names next compiled
    cases names with
    | nil => simp at len
    | cons name rest =>
      cases rest with
      | cons name2 more => simp at len
      | nil =>
        cases pres with
        | some result => simp [correctOutcome, isResult] at outcome
        | none =>
          rcases outcome with ⟨_, _, _, _, _, _, _, stack, handler, jumpKeep, resultVars⟩
          have projectedLookup : sptLookup name (sptMap dataToBviValue tmid.locals) = some value := by
            cases resultVars with
            | cons lookup _ => exact lookup
          rw [sptLookup_sptMap] at projectedLookup
          cases localFound : sptLookup name tmid.locals with
          | none => simp [localFound] at projectedLookup
          | some dataValue =>
            have projection : dataToBviValue dataValue = value := by simpa [localFound] using projectedLookup
            have jumpExists : DataSem.jumpExc tmid ≠ none := jumpKeep (exceptionJump ⟨value, rfl⟩)
            cases jumped : DataSem.jumpExc tmid with
            | none => exact False.elim (jumpExists jumped)
            | some t2 =>
              obtain ⟨finalRel, jumpAgain⟩ := jumpExc_preserves smid tmid t2 middleRel jumped
              have sourceBound := BviSem.evaluate_clock_le [body] env s1
              rw [bodyRun] at sourceBound
              have targetBound : tmid.clock ≤ t1.clock := by
                simpa [← related.1, ← middleRel.1] using sourceBound
              have raiseRun : DataSem.evaluate (.raise name) tmid = (some (.err (.raise dataValue)), t2) := by
                simp [DataSem.evaluate, DataSem.getVar, localFound, jumped]
              refine ⟨t2, .seq prog (.raise name), some (.err (.raise dataValue)), [name], next, t2.localsSize, ?_, ?_, finalRel, ?_⟩
              · simp [compileSource, compiled, Flapjack.holHd]
              · exact evaluateSeq_continue prog (.raise name) t1 tmid _ target targetBound raiseRun
              · simp [correctOutcome, isReturn, isResult, isException, dataToBviResult, projection, stack, handler]
                exact ⟨rfl, by simpa using jumpAgain⟩

/-- The `let` case composes binding and body simulations, extending the
environment by the binding results. This remains untagged pending evaluator
correspondence review. -/
theorem simulationFor_let {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F)
    (ihBindings : simulationFor bindings env s1)
    (ihBody : ∀ (values : List BvlSem.Value) (smid : BviSem.BviState C F),
      BviSem.evaluate bindings env s1 = (.val values, smid) → simulationFor [body] (values ++ env) smid) :
    simulationFor [.let bindings body] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize bindingsRun : BviSem.evaluate bindings env s1 = pair
  obtain ⟨bindingsResult, smid⟩ := pair
  cases bindingsResult with
  | err error =>
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t2, first, pres, boundNames, nmid, ls, compiled, target, finalRel, outcome⟩ :=
      ihBindings (.err error) smid t1 n corr false live bindingsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result =>
      generalize compiledBody : compileSource nmid (boundNames ++ corr) tail live [body] = triple
      obtain ⟨second, names, next⟩ := triple
      have sourceBound := BviSem.evaluate_clock_le bindings env s1
      rw [bindingsRun] at sourceBound
      have targetBound : t2.clock ≤ t1.clock := by
        simpa [← related.1, ← finalRel.1] using sourceBound
      refine ⟨t2, .seq first second, some result, names, next, ls, ?_, ?_, finalRel, ?_⟩
      · simp [compileSource, compiled, compiledBody]
      · exact evaluateSeq_stop first second t1 t2 result target targetBound
      · simpa [correctOutcome, isResult] using outcome
  | val values =>
    have bodyRun : BviSem.evaluate [body] (values ++ env) smid = (res, s2) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
      exact run
    obtain ⟨tmid, first, pres, boundNames, nmid, ls1, compiled, target, middleRel, outcome⟩ :=
      ihBindings (.val values) smid t1 n corr false live bindingsRun (by simp) vars (by simp) fresh related livePresent
        (by simp [isException])
    cases pres with
    | some result => simp [correctOutcome, isResult] at outcome
    | none =>
      have firstOutcome := outcome
      have liveMidAll := correctOutcome_live values t1 tmid n nmid corr live boundNames env ls1 outcome livePresent
      have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
        intro v member
        exact liveMidAll v (List.mem_append_right boundNames member)
      rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, jumpMid, resultVars⟩
      have extendedVars : DataProps.varCorr (values ++ env) (boundNames ++ corr)
          (sptMap dataToBviValue tmid.locals) := varCorr_append resultVars varsMid
      obtain ⟨t2, second, pres, names, next, ls2, compiledBody, targetBody, finalRel, bodyOutcome⟩ :=
        ihBody values smid bindingsRun res s2 tmid nmid (boundNames ++ corr) tail live bodyRun notTypeError
          extendedVars (by simp) freshMid middleRel liveMid (fun h => jumpMid (exceptionJump h))
      have sourceBound := BviSem.evaluate_clock_le bindings env s1
      rw [bindingsRun] at sourceBound
      have targetBound : tmid.clock ≤ t1.clock := by
        simpa [← related.1, ← middleRel.1] using sourceBound
      refine ⟨t2, .seq first second, pres, names, next, ls2, ?_, ?_, finalRel, ?_⟩
      · simp [compileSource, compiled, compiledBody]
      · exact evaluateSeq_continue first second t1 tmid _ target targetBound targetBody
      · exact correctOutcome_let values res t1 tmid t2 n nmid next corr live boundNames names env tail pres ls1 ls2 firstOutcome bodyOutcome

/-- Copy a successful non-tail branch result to a fresh destination. The
full continuing invariant is retained at the incremented destination bound. -/
theorem correctOutcome_move {C F : Type} (value : BvlSem.Value)
    (source : BviSem.BviState C F) (t1 t2 : DataSem.State C F)
    (n next dest name : Nat) (corr live : List Nat) (env : List BvlSem.Value) (ls : Option Nat)
    (related : stateRel source t2)
    (outcome : correctOutcome (.val [value]) t1 t2 n next corr live [name] env false none ls)
    (destBound : next ≤ dest) :
    ∃ dataValue,
      DataSem.evaluate (.move dest name) t2 = (none, DataSem.setVar dest dataValue t2) ∧
      stateRel source (DataSem.setVar dest dataValue t2) ∧
      correctOutcome (.val [value]) t1 (DataSem.setVar dest dataValue t2)
        n (dest + 1) corr live [dest] env false none ls := by
  rcases outcome with ⟨_, nBound, _, fresh, envVars, localBound, preserve, stack, handler, jump, resultVars⟩
  have projectedLookup : sptLookup name (sptMap dataToBviValue t2.locals) = some value := by
    cases resultVars with
    | cons lookup _ => exact lookup
  rw [sptLookup_sptMap] at projectedLookup
  cases read : sptLookup name t2.locals with
  | none => simp [read] at projectedLookup
  | some dataValue =>
    have projection : dataToBviValue dataValue = value := by simpa [read] using projectedLookup
    have absent : sptLookup dest t2.locals = none := fresh dest destBound
    have mappedAbsent : sptLookup dest (sptMap dataToBviValue t2.locals) = none := by
      simp [sptLookup_sptMap, absent]
    have envNew := varCorr_insert_absent envVars dest (dataToBviValue dataValue) mappedAbsent
    refine ⟨dataValue, ?_, ?_, ?_⟩
    · simp [DataSem.evaluate, DataSem.getVar, read]
    · simpa [stateRel, DataSem.setVar] using related
    · simp only [correctOutcome, DataSem.setVar, true_and, List.mem_singleton, forall_eq]
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, stack, handler, ?_, ?_⟩
      · intro k bound
        have different : k ≠ dest := by omega
        rw [sptLookup_sptInsert_ne dest k dataValue t2.locals different]
        exact fresh k (by omega)
      · simpa [sptMap_sptInsert, projection] using envNew
      · intro k x lookup
        by_cases same : k = dest
        · omega
        · rw [sptLookup_sptInsert_ne dest k dataValue t2.locals same] at lookup
          have oldBound := localBound k x lookup
          omega
      · intro k x lookup needed
        have old := preserve k x lookup needed
        have different : k ≠ dest := by
          intro same
          subst k
          rw [absent] at old
          contradiction
        rw [sptLookup_sptInsert_ne dest k dataValue t2.locals different]
        exact old
      · intro hasJump
        have := jump hasJump
        simpa only [DataSem.setVar] using (jumpExc_setVar_ne_none t2 dest dataValue).2 this
      · constructor
        · simp [DataSem.getVar, sptLookup_sptMap, sptLookup_sptInsert_same, projection]
        · constructor

/-- A selected non-tail conditional branch either stops unchanged or copies
its single result into the fresh merge local. Its result and state satisfy the
same simulation invariant at the merge point. -/
theorem simulation_branch_move {C F : Type} (branch : Bvi.Exp) (env : List BvlSem.Value)
    (source nextSource : BviSem.BviState C F) (t1 t2 : DataSem.State C F)
    (res : BviSem.BviResult) (n next dest name : Nat) (corr live : List Nat)
    (prog : DataLang.Prog) (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls : Option Nat)
    (sourceRun : BviSem.evaluate [branch] env source = (res, nextSource))
    (targetRun : DataSem.evaluate prog t1 = (pres, t2))
    (initialRel : stateRel source t1) (finalRel : stateRel nextSource t2)
    (outcome : correctOutcome res t1 t2 n next corr live [name] env false pres ls)
    (destBound : next ≤ dest) :
    ∃ t3 presFinal,
      DataSem.evaluate (.seq prog (.move dest name)) t1 = (presFinal, t3) ∧
      stateRel nextSource t3 ∧
      correctOutcome res t1 t3 n (dest + 1) corr live [dest] env false presFinal ls := by
  have sourceBound := BviSem.evaluate_clock_le [branch] env source
  rw [sourceRun] at sourceBound
  have targetBound : t2.clock ≤ t1.clock := by
    simpa [← initialRel.1, ← finalRel.1] using sourceBound
  cases pres with
  | some result =>
    refine ⟨t2, some result, evaluateSeq_stop prog (.move dest name) t1 t2 result targetRun targetBound, finalRel, ?_⟩
    exact outcome
  | none =>
    cases res with
    | err error => simp [correctOutcome] at outcome
    | val values =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton branch env source nextSource values sourceRun
      obtain ⟨dataValue, moveRun, movedRel, movedOutcome⟩ :=
        correctOutcome_move value nextSource t1 t2 n next dest name corr live env ls finalRel outcome destBound
      refine ⟨DataSem.setVar dest dataValue t2, none, ?_, movedRel, movedOutcome⟩
      exact evaluateSeq_continue prog (.move dest name) t1 t2 _ targetRun targetBound moveRun

private theorem destBool_tests (value : DataSem.Value) (result : Bool)
    (decoded : DataSem.destBool value = some result) :
    DataSem.isBool true value = result ∧ DataSem.isBool false value = !result := by
  cases value with
  | number n => simp [DataSem.destBool] at decoded
  | word64 w => simp [DataSem.destBool] at decoded
  | codePtr p => simp [DataSem.destBool] at decoded
  | refPtr bit ptr => simp [DataSem.destBool] at decoded
  | block ts tag fields =>
    cases fields with
    | cons field rest => simp [DataSem.destBool] at decoded
    | nil =>
      cases tag with
      | zero => simp [DataSem.destBool] at decoded; subst result; simp [DataSem.isBool, BackendCommon.boolToTag, BackendCommon.falseTag, BackendCommon.trueTag]
      | succ tag =>
        cases tag with
        | zero => simp [DataSem.destBool] at decoded; subst result; simp [DataSem.isBool, BackendCommon.boolToTag, BackendCommon.falseTag, BackendCommon.trueTag]
        | succ tag => simp [DataSem.destBool] at decoded

/-- A target conditional selects the branch indicated by decoding the
corresponding BVI value. Timestamps do not affect the choice. -/
theorem evaluateIf_projection {C F : Type} (state : DataSem.State C F) (name : Nat)
    (value : DataSem.Value) (condition : Bool) (yes no : DataLang.Prog)
    (read : DataSem.getVar name state.locals = some value)
    (decoded : BvlSem.asBool (dataToBviValue value) = some condition) :
    DataSem.evaluate (.ifThenElse name yes no) state =
      DataSem.evaluate (if condition then yes else no) state := by
  have dataDecoded : DataSem.destBool value = some condition := by
    rw [← destBool_projection]
    exact decoded
  obtain ⟨yesTest, noTest⟩ := destBool_tests value condition dataDecoded
  cases condition <;> simp [DataSem.evaluate, read, yesTest, noTest]

/-- A selected branch provides the conditional's result invariant in both
tail position and non-tail position, where its result is moved to the common
fresh local. -/
theorem simulation_branch {C F : Type} (branch : Bvi.Exp) (env : List BvlSem.Value)
    (source nextSource : BviSem.BviState C F) (t1 t2 : DataSem.State C F)
    (res : BviSem.BviResult) (n next dest name : Nat) (corr live : List Nat) (tail : Bool)
    (prog : DataLang.Prog) (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls : Option Nat)
    (sourceRun : BviSem.evaluate [branch] env source = (res, nextSource))
    (targetRun : DataSem.evaluate prog t1 = (pres, t2))
    (initialRel : stateRel source t1) (finalRel : stateRel nextSource t2)
    (outcome : correctOutcome res t1 t2 n next corr live [name] env tail pres ls)
    (destBound : next ≤ dest) :
    ∃ t3 presFinal,
      DataSem.evaluate (if tail then prog else .seq prog (.move dest name)) t1 = (presFinal, t3) ∧
      stateRel nextSource t3 ∧
      correctOutcome res t1 t3 n (dest + 1) corr live [dest] env tail presFinal ls := by
  cases tail with
  | false =>
    simpa using simulation_branch_move branch env source nextSource t1 t2 res n next dest name corr live prog pres ls sourceRun targetRun initialRel finalRel outcome destBound
  | true =>
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result => exact ⟨t2, some result, targetRun, finalRel, outcome⟩

private theorem correctOutcome_weaken_start {C F : Type} (res : BviSem.BviResult)
    (t1 t2 : DataSem.State C F) (n n' next : Nat) (corr live names : List Nat)
    (env : List BvlSem.Value) (tail : Bool)
    (pres : Option (Result (List DataSem.Value) DataSem.Value)) (ls : Option Nat)
    (bound : n ≤ n') (outcome : correctOutcome res t1 t2 n' next corr live names env tail pres ls) :
    correctOutcome res t1 t2 n next corr live names env tail pres ls := by
  cases pres with
  | some _ => exact outcome
  | none =>
    rcases outcome with ⟨notTail, nextBound, rest⟩
    exact ⟨notTail, Nat.le_trans bound nextBound, rest⟩

private theorem compileSource_single (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (exp : Bvi.Exp) : ∃ prog name next, compileSource n env tail live [exp] = (prog, [name], next) := by
  generalize compiled : compileSource n env tail live [exp] = triple
  obtain ⟨prog, names, next⟩ := triple
  have len := compileSource_LENGTH n env tail live [exp] prog names next compiled
  cases names with
  | nil => simp at len
  | cons name rest =>
    cases rest with
    | nil => exact ⟨prog, name, next, rfl⟩
    | cons _ _ => simp at len

/-- Conditional simulation, combining condition evaluation, branch choice,
and the fresh-result merge for non-tail compilation. This remains untagged
pending evaluator correspondence review. -/
theorem simulationFor_if {C F : Type} (condition yes no : Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F)
    (ihCondition : simulationFor [condition] env s1)
    (ihBranch : ∀ (value : BvlSem.Value) (smid : BviSem.BviState C F) (choice : Bool),
      BviSem.evaluate [condition] env s1 = (.val [value], smid) →
      BvlSem.asBool value = some choice → simulationFor [if choice then yes else no] env smid) :
    simulationFor [.ifThenElse condition yes no] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  obtain ⟨condCode, condName, n1, compiledCondition⟩ := compileSource_single n corr false live condition
  obtain ⟨yesCode, yesName, n2, compiledYes⟩ := compileSource_single n1 corr tail live yes
  obtain ⟨noCode, noName, n3, compiledNo⟩ := compileSource_single n2 corr tail live no
  let yesTarget := if tail then yesCode else .seq yesCode (.move n3 yesName)
  let noTarget := if tail then noCode else .seq noCode (.move n3 noName)
  have compiledAll : compileSource n corr tail live [.ifThenElse condition yes no] =
      (.seq condCode (.ifThenElse condName yesTarget noTarget), [n3], n3 + 1) := by
    cases tail <;> simp [compileSource, compiledCondition, compiledYes, compiledNo,
      Flapjack.holHd, yesTarget, noTarget]
  generalize conditionRun : BviSem.evaluate [condition] env s1 = pair
  obtain ⟨conditionResult, smid⟩ := pair
  cases conditionResult with
  | err error =>
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t2, prog, pres, names, next, ls, compiled, target, finalRel, outcome⟩ :=
      ihCondition (.err error) smid t1 n corr false live conditionRun notTypeError vars (by simp) fresh related livePresent exceptionJump
    rw [compiledCondition] at compiled
    simp only [Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl, rfl⟩ := compiled
    cases pres with
    | none => simp [correctOutcome] at outcome
    | some result =>
      have sourceBound := BviSem.evaluate_clock_le [condition] env s1
      rw [conditionRun] at sourceBound
      have targetBound : t2.clock ≤ t1.clock := by
        simpa [← related.1, ← finalRel.1] using sourceBound
      refine ⟨t2, .seq condCode (.ifThenElse condName yesTarget noTarget), some result, [n3], n3 + 1, ls,
        compiledAll, ?_, finalRel, ?_⟩
      · exact evaluateSeq_stop condCode (.ifThenElse condName yesTarget noTarget) t1 t2 result target targetBound
      · simpa [correctOutcome, isResult] using outcome
  | val values =>
    obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton condition env s1 smid values conditionRun
    cases decoded : BvlSem.asBool value with
    | none =>
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
      change (match BvlSem.asBool value with
        | none => (.err (.abort .typeError), smid)
        | some true => BviSem.evaluate [yes] env smid
        | some false => BviSem.evaluate [no] env smid) = (res, s2) at run
      rw [decoded] at run
      simp only [Prod.mk.injEq] at run
      exact False.elim (notTypeError run.1.symm)
    | some choice =>
      have branchRun : BviSem.evaluate [if choice then yes else no] env smid = (res, s2) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
        change (match BvlSem.asBool value with
          | none => (.err (.abort .typeError), smid)
          | some true => BviSem.evaluate [yes] env smid
          | some false => BviSem.evaluate [no] env smid) = (res, s2) at run
        rw [decoded] at run
        cases choice <;> exact run
      obtain ⟨tmid, prog, pres, names, next, ls1, compiled, target, middleRel, outcome⟩ :=
        ihCondition (.val [value]) smid t1 n corr false live conditionRun (by simp) vars (by simp) fresh related livePresent
          (by simp [isException])
      rw [compiledCondition] at compiled
      simp only [Prod.mk.injEq] at compiled
      obtain ⟨rfl, rfl, rfl⟩ := compiled
      cases pres with
      | some result => simp [correctOutcome, isResult] at outcome
      | none =>
        have conditionOutcome := outcome
        have liveMidAll := correctOutcome_live [value] t1 tmid n n1 corr live [condName] env ls1 outcome livePresent
        have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
          intro v member
          exact liveMidAll v (List.mem_append_right [condName] member)
        rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, jumpMid, resultVars⟩
        have projectedLookup : sptLookup condName (sptMap dataToBviValue tmid.locals) = some value := by
          cases resultVars with
          | cons lookup _ => exact lookup
        rw [sptLookup_sptMap] at projectedLookup
        cases localFound : sptLookup condName tmid.locals with
        | none => simp [localFound] at projectedLookup
        | some dataValue =>
          have projection : dataToBviValue dataValue = value := by simpa [localFound] using projectedLookup
          have dataDecoded : BvlSem.asBool (dataToBviValue dataValue) = some choice := by simpa [projection] using decoded
          have yesCounter : n1 ≤ n2 := compileSource_LESS_EQ n1 corr tail live [yes] yesCode [yesName] n2 compiledYes
          have noCounter : n2 ≤ n3 := compileSource_LESS_EQ n2 corr tail live [no] noCode [noName] n3 compiledNo
          let branchStart := if choice then n1 else n2
          let branchNext := if choice then n2 else n3
          let branchName := if choice then yesName else noName
          let branchCode := if choice then yesCode else noCode
          have startBound : n1 ≤ branchStart := by cases choice <;> simp [branchStart, yesCounter]
          have destBound : branchNext ≤ n3 := by cases choice <;> simp [branchNext, noCounter]
          have selectedCompiled : compileSource branchStart corr tail live [if choice then yes else no] =
              (branchCode, [branchName], branchNext) := by
            cases choice <;> simp [branchStart, branchNext, branchName, branchCode, compiledYes, compiledNo]
          obtain ⟨tbranch, branchProg, branchPres, branchNames, branchNext', ls2, branchCompiled,
              branchTarget, branchRel, branchOutcome⟩ :=
            ihBranch value smid choice conditionRun decoded res s2 tmid branchStart corr tail live branchRun notTypeError varsMid
              (by simp) (fun k hk => freshMid k (Nat.le_trans startBound hk)) middleRel liveMid (fun h => jumpMid (exceptionJump h))
          rw [selectedCompiled] at branchCompiled
          simp only [Prod.mk.injEq] at branchCompiled
          obtain ⟨rfl, rfl, rfl⟩ := branchCompiled
          obtain ⟨t2, finalPres, selectedTarget, finalRel, selectedOutcome⟩ :=
            simulation_branch (if choice then yes else no) env smid s2 tmid tbranch res branchStart branchNext n3 branchName corr live tail branchCode branchPres ls2 branchRun branchTarget middleRel branchRel branchOutcome destBound
          have ifRun : DataSem.evaluate (.ifThenElse condName yesTarget noTarget) tmid = (finalPres, t2) := by
            rw [evaluateIf_projection tmid condName dataValue choice yesTarget noTarget (by simpa [DataSem.getVar] using localFound) dataDecoded]
            cases choice <;> simpa [yesTarget, noTarget, branchCode, branchName] using selectedTarget
          have sourceBound := BviSem.evaluate_clock_le [condition] env s1
          rw [conditionRun] at sourceBound
          have targetBound : tmid.clock ≤ t1.clock := by
            simpa [← related.1, ← middleRel.1] using sourceBound
          have secondOutcome := correctOutcome_weaken_start res tmid t2 n1 branchStart (n3 + 1)
            corr live [n3] env tail finalPres ls2 startBound selectedOutcome
          refine ⟨t2, .seq condCode (.ifThenElse condName yesTarget noTarget), finalPres, [n3], n3 + 1, ls2,
            compiledAll, ?_, finalRel, ?_⟩
          · exact evaluateSeq_continue condCode (.ifThenElse condName yesTarget noTarget) t1 tmid _ target targetBound ifRun
          · exact correctOutcome_seq [value] res t1 tmid t2 n n1 (n3 + 1) corr live [condName] [n3]
              env tail finalPres ls1 ls2 conditionOutcome secondOutcome

end Flapjack.Compiler.Backend.BviToData
