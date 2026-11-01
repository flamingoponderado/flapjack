import Flapjack.Compiler.Backend.BviToData.Proofs.CompileSource
import Flapjack.Compiler.Backend.BviToData.Proofs.Variables
import Flapjack.Compiler.Backend.BviToData.Proofs.Result
import Flapjack.Compiler.Backend.Semantics.DataSem.Control

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
