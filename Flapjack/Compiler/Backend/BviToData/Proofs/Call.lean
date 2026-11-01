import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect

/-! Call argument cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- An indirect call with a handler is rejected before evaluating its
arguments, so it has no non-type-error execution. -/
theorem simulationFor_call_invalid_handler {C F : Type} (ticks : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List BvlSem.Value) (state : BviSem.BviState C F) :
    simulationFor [.call ticks none args (some handler)] env state := by
  intro res next target n corr tail live run notTypeError
  simp [BviSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact False.elim (notTypeError rfl)

/-- An error while evaluating unhandled-call arguments propagates before
the call executes. This is untagged pending evaluator correspondence review. -/
theorem simulationFor_call_argsError {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks dest args none] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks dest args none] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks dest args none] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    let rest := DataLang.mkTicks ticks (.call (if tail then none else some ([n1], namesOfList (live ++ corr))) dest argNames none)
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
      evaluateSeq_stop argsProg rest t1 t2 result target targetBound
    refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
    · simp [compileSource, compiled, rest]
    · simpa [correctOutcome, isResult] using outcome

/-- An error while evaluating the arguments of a direct call with a handler
propagates before the handler or call executes. -/
theorem simulationFor_call_handler_argsError {C F : Type} (ticks dest : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F)
    (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.call ticks (some dest) args (some handler)] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.call ticks (some dest) args (some handler)] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    generalize handlerCompiled : compileSource (n1 + 1) (n1 :: corr) false live [handler] = triple
    obtain ⟨handlerProg, handlerNames, n2⟩ := triple
    let after := if tail then DataLang.Prog.return [n2] else .skip
    let rest := DataLang.mkTicks ticks (.seq
      (.call (some ([n2], namesOfList (live ++ corr))) (some dest) argNames
        (some (n1, .seq handlerProg (.move n2 (Flapjack.holHd handlerNames))))) after)
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
      evaluateSeq_stop argsProg rest t1 t2 result target targetBound
    refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n2], n2 + 1, ls, ?_, targetRun, finalRel, ?_⟩
    · simp [compileSource, compiled, handlerCompiled, rest, after]
    · simpa [correctOutcome, isResult] using outcome

/-- Errors in let-call arguments propagate before either the call or its
continuation executes, including the tail-call rewrite. -/
theorem simulationFor_letCall_argsError {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F)
    (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.letCall rets ticks dest args body] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.letCall rets ticks dest args body] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  classical
  have wholeRun : BviSem.evaluate [.letCall rets ticks dest args body] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using sourceBound
    by_cases identity : body = .return ((List.range rets).map Bvi.Exp.var)
    · let rest := DataLang.mkTicks ticks (.call none (some dest) argNames none)
      have targetRun : DataSem.evaluate (.seq argsProg rest) t1 = (some result, t2) :=
        evaluateSeq_stop argsProg rest t1 t2 result target targetBound
      refine ⟨wholeRun, t2, .seq argsProg rest, some result, [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, rest]
      · simpa [correctOutcome, isResult] using outcome
    · let returns := (List.range rets).map (n1 + ·)
      generalize bodyCompiled : compileSource (n1 + rets) (returns ++ corr) tail live [body] = triple
      obtain ⟨bodyProg, bodyNames, n2⟩ := triple
      let rest := DataLang.mkTicks ticks (.call (some (returns, namesOfList (live ++ corr))) (some dest) argNames none)
      let inner := DataLang.Prog.seq argsProg rest
      have innerRun : DataSem.evaluate inner t1 = (some result, t2) :=
        evaluateSeq_stop argsProg rest t1 t2 result target targetBound
      have targetRun : DataSem.evaluate (.seq inner bodyProg) t1 = (some result, t2) :=
        evaluateSeq_stop inner bodyProg t1 t2 result innerRun targetBound
      refine ⟨wholeRun, t2, .seq inner bodyProg, some result, bodyNames, n2, ls, ?_, targetRun, finalRel, ?_⟩
      · simp [compileSource, compiled, identity, bodyCompiled, inner, rest, returns]
      · simpa [correctOutcome, isResult] using outcome

end Flapjack.Compiler.Backend.BviToData
