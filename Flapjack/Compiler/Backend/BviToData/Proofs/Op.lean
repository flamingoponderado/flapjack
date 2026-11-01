import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.BviToData.Proofs.FfiAssign

/-! Primitive-operation cases of the BVI-to-data compiler simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- If argument evaluation stops with a non-type error, the compiled
operation stops at the same point, before executing its assignment. This is
an untagged source case pending evaluator correspondence review. -/
theorem simulationFor_op_argsError {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 s2 : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.err error, s2))
    (notTypeError : Result.err error ≠ (.err (.abort .typeError) : BviSem.BviResult))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException (.err error) → DataSem.jumpExc t1 ≠ none) :
    BviSem.evaluate [.op op args] env s1 = (.err error, s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op op args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.err error) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op op args] env s1 = (.err error, s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  obtain ⟨t2, argsProg, pres, argNames, n1, ls, compiled, target, finalRel, outcome⟩ :=
    ih (.err error) s2 t1 n corr false live argsRun notTypeError vars (by simp) fresh related livePresent exceptionJump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    let assignment := iAssign n1 op argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    let whole := if tail then DataLang.Prog.seq inner (.return [n1]) else inner
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have targetBound : t2.clock ≤ t1.clock := by
      simpa [← related.1, ← finalRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (some result, t2) :=
      evaluateSeq_stop argsProg assignment t1 t2 result target targetBound
    have targetRun : DataSem.evaluate whole t1 = (some result, t2) := by
      cases tail with
      | false => exact innerRun
      | true => exact evaluateSeq_stop inner (.return [n1]) t1 t2 result innerRun targetBound
    refine ⟨wholeRun, t2, whole, some result, [n1], n1 + 1, ls, ?_, targetRun, finalRel, ?_⟩
    · cases tail <;> simp [compileSource, compiled, assignment, inner, whole]
    · simpa [correctOutcome, isResult] using outcome

/-- After successful argument evaluation, a terminal FFI event is propagated
by the compiled operation, with or without a trailing tail return. This is an
untagged case pending evaluator review and assembly of the operation proof. -/
theorem simulationFor_op_ffiError {C F : Type} (name : Basis.Pure.MlString.MlString)
    (args : List Bvi.Exp) (env : List BvlSem.Value) (s1 smid : BviSem.BviState C F)
    (values : List BvlSem.Value) (event : HolFinalEvent)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (ffiRun : BviSem.doApp (.ffi name) values.reverse smid = .err (.abort (.ffiError event)))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.ffi name) args] env s1 = (.err (.abort (.ffiError event)), smid) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.ffi name) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel smid t2 ∧
      correctOutcome (.err (.abort (.ffiError event))) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.ffi name) args] env s1 = (.err (.abort (.ffiError event)), smid) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [ffiRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, _, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have ffiProjected : BviSem.doApp (.ffi name) (dataValues.reverse.map dataToBviValue) smid =
        .err (.abort (.ffiError event)) := by
      simpa [List.map_reverse, ← projected] using ffiRun
    obtain ⟨t2, assignmentRun, finalRel⟩ :=
      evaluate_iAssign_ffiError name tmid smid argNames.reverse live corr env dataValues.reverse n1 event middleRel
        varsMid liveMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) ffiProjected
    let assignment := iAssign n1 (.ffi name) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    let whole := if tail then DataLang.Prog.seq inner (.return [n1]) else inner
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by
      simpa [← related.1, ← middleRel.1] using sourceBound
    have finalBound : t2.clock ≤ t1.clock := by
      simpa [← related.1, ← finalRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (some (.err (.abort (.ffiError event))), t2) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have targetRun : DataSem.evaluate whole t1 = (some (.err (.abort (.ffiError event))), t2) := by
      cases tail with
      | false => exact innerRun
      | true => exact evaluateSeq_stop inner (.return [n1]) t1 t2 _ innerRun finalBound
    refine ⟨wholeRun, t2, whole, some (.err (.abort (.ffiError event))), [n1], n1 + 1, none, ?_, targetRun,
      finalRel, ?_⟩
    · cases tail <;> simp [compileSource, compiled, assignment, inner, whole]
    · simp [correctOutcome, dataToBviResult, isResult, isReturn, isException]

end Flapjack.Compiler.Backend.BviToData
