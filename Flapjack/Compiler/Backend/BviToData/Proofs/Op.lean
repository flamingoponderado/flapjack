import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.BviToData.Proofs.FfiAssign
import Flapjack.Compiler.Backend.BviToData.Proofs.OpFrame
import Flapjack.Compiler.Backend.BviToData.Proofs.Install

/-! Primitive-operation cases of the BVI-to-data compiler simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem intOp_error_is_typeError {C F : Type} (op : ClosLang.IntOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.intOp op) args source = .err error) : error = .abort .typeError := by
  cases op <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
    BvlSem.doApp, BvlSem.applyNumeric] at run
  all_goals try (split at run <;> simp_all)
  all_goals try (split at * <;> simp_all)
  case const n =>
    cases args <;> simp_all
    split at run <;> simp_all

private theorem wordOp_error_is_typeError {C F : Type} (op : ClosLang.WordOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.wordOp op) args source = .err error) : error = .abort .typeError := by
  have fallback : BviSem.doAppAux (.wordOp op) args source = some none := by
    cases op <;> simp [BviSem.doAppAux]
  cases wordResult : BvlSem.doWordApp op args with
  | none =>
    simpa [BviSem.doApp, BviSem.doAppFallback, fallback, BvlSem.doApp, BvlSem.applyNumeric, wordResult] using run.symm
  | some value =>
    simp [BviSem.doApp, BviSem.doAppFallback, fallback, BvlSem.doApp, BvlSem.applyNumeric, wordResult] at run

private theorem blockOp_error_is_typeError {C F : Type} (op : ClosLang.BlockOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.blockOp op) args source = .err error) : error = .abort .typeError := by
  cases auxiliary : BviSem.doAppAux (.blockOp op) args source with
  | none => simpa [BviSem.doApp, BviSem.doAppFallback, auxiliary] using run.symm
  | some result =>
    cases result with
    | some pair => simp [BviSem.doApp, BviSem.doAppFallback, auxiliary] at run
    | none =>
      cases blockResult : BvlSem.applyBlock op args (BviSem.toBvl source) with
      | none =>
        simpa [BviSem.doApp, BviSem.doAppFallback, auxiliary, BvlSem.doApp, blockResult] using run.symm
      | some value =>
        simp [BviSem.doApp, BviSem.doAppFallback, auxiliary, BvlSem.doApp, blockResult] at run

private theorem memOp_error_is_typeError {C F : Type} (op : ClosLang.MemOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.memOp op) args source = .err error) : error = .abort .typeError := by
  cases auxiliary : BviSem.doAppAux (.memOp op) args source with
  | none => simpa [BviSem.doApp, BviSem.doAppFallback, auxiliary] using run.symm
  | some result =>
    cases result with
    | some pair => simp [BviSem.doApp, BviSem.doAppFallback, auxiliary] at run
    | none =>
      cases memResult : BvlSem.applyMemory op args (BviSem.toBvl source) with
      | none =>
        simpa [BviSem.doApp, BviSem.doAppFallback, auxiliary, BvlSem.doApp, memResult] using run.symm
      | some value =>
        simp [BviSem.doApp, BviSem.doAppFallback, auxiliary, BvlSem.doApp, memResult] at run

private theorem bvlThunk_error_is_typeError {C F : Type} (op : AstHOL.ThunkOp) (args : List BvlSem.Value)
    (source : BvlSem.State C F) (error : ErrorResult BvlSem.Value)
    (run : BvlSem.doApp (.thunkOp op) args source = .err error) : error = .abort .typeError := by
  cases op <;> cases args <;> simp [BvlSem.doApp] at run
  all_goals try (cases_type List BvlSem.Value <;> simp_all)
  all_goals repeat' (split at run <;> try simp_all)
  all_goals exact run.symm

private theorem thunkOp_error_is_typeError {C F : Type} (op : AstHOL.ThunkOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.thunkOp op) args source = .err error) : error = .abort .typeError := by
  have fallback : BviSem.doAppAux (.thunkOp op) args source = some none := by
    cases op <;> simp [BviSem.doAppAux]
  cases output : BvlSem.doApp (.thunkOp op) args (BviSem.toBvl source) with
  | val pair => simp [BviSem.doApp, BviSem.doAppFallback, fallback, output] at run
  | err err =>
    have onlyType := bvlThunk_error_is_typeError op args (BviSem.toBvl source) err output
    subst err
    simpa [BviSem.doApp, BviSem.doAppFallback, fallback, output] using run.symm

private theorem globalAux_noFallback {C F : Type} (op : ClosLang.GlobOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) : BviSem.doAppAux (.globOp op) args source ≠ some none := by
  cases op <;> cases args <;> simp [BviSem.doAppAux]
  all_goals try (split <;> simp_all)
  all_goals simp only [Option.bind_eq_some_iff, not_exists, not_and]
  all_goals intros
  all_goals try split
  all_goals try (split <;> simp)
  all_goals simp

private theorem globalOp_error_is_typeError {C F : Type} (op : ClosLang.GlobOp) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.globOp op) args source = .err error) : error = .abort .typeError := by
  cases auxiliary : BviSem.doAppAux (.globOp op) args source with
  | none =>
    simpa [BviSem.doApp, BviSem.doAppFallback, auxiliary] using run.symm
  | some result =>
    cases result with
    | none => exact False.elim (globalAux_noFallback op args source auxiliary)
    | some pair => simp [BviSem.doApp, BviSem.doAppFallback, auxiliary] at run

private theorem labelOp_error_is_typeError {C F : Type} (label : Nat) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.label label) args source = .err error) : error = .abort .typeError := by
  cases args with
  | cons a rest => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] using run.symm
  | nil =>
    cases found : sptLookup label source.code with
    | none => simpa [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, found] using run.symm
    | some entry => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, found] at run

private theorem ffiOp_error_is_final {C F : Type} (name : Basis.Pure.MlString.MlString) (args : List BvlSem.Value)
    (source : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp (.ffi name) args source = .err error) (notType : error ≠ .abort .typeError) :
    ∃ event, error = .abort (.ffiError event) := by
  cases args with
  | nil => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
  | cons a rest =>
    cases rest with
    | nil => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
    | cons b rest =>
      cases rest with
      | cons c tail => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
      | nil =>
        cases a with
        | number n => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
        | word64 w => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
        | codePtr p => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
        | block tag vs => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
        | refPtr flag configPtr =>
          cases b with
          | number n => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
          | word64 w => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
          | codePtr p => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
          | block tag vs => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp]
          | refPtr bit ptr =>
            cases configFound : source.refs.lookup configPtr with
            | none => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
            | some configEntry =>
              cases configEntry with
              | valueArray values => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
              | thunk mode value => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
              | mutBlock tag done left child right => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
              | byteArray immutable config =>
                cases immutable with
                | false => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                | true =>
                  cases bytesFound : source.refs.lookup ptr with
                  | none => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                  | some bytesEntry =>
                    cases bytesEntry with
                    | valueArray values => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                    | thunk mode value => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                    | mutBlock tag done left child right => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                    | byteArray mutable bytes =>
                      cases mutable with
                      | true => simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl]
                      | false =>
                        cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                        | final event =>
                          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl,
                            configFound, bytesFound, call] at run
                          exact ⟨event, run.symm⟩
                        | ret ffi updated =>
                          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl,
                            configFound, bytesFound, call] at run

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

/-- A successful integer primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_int_success {C F : Type} (op : ClosLang.IntOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.intOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.intOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.intOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.intOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.intOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_int_outcome op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.intOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.intOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- Complete integer-operation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful integer application handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_int {C F : Type} (op : ClosLang.IntOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.intOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.intOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.intOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.intOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.intOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := intOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.intOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_int_success op args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- A successful word primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_word_success {C F : Type} (op : ClosLang.WordOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.wordOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.wordOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.wordOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.wordOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.wordOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_word_outcome op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.wordOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.wordOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- A successful block op primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_block_success {C F : Type} (op : ClosLang.BlockOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.blockOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.blockOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.blockOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.blockOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.blockOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_block_outcome op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.blockOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.blockOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- A successful installation expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_install_success {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp .install values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op .install args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op .install args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op .install args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp .install (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_install_outcome tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 .install argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op .install args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- A successful memory expression satisfies the simulation invariant,
assuming its primitive frame. This is untagged pending evaluator
correspondence review. -/
theorem simulationFor_op_mem_success_of_frame {C F : Type} (op : ClosLang.MemOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (primitiveFrame : ∀ (args : List DataSem.Value) (before after : DataSem.State C F) (value : DataSem.Value),
      DataSem.doApp (.memOp op) args before = .val (value, after) → DataSem.SameLocalControl before after)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.memOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.memOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.memOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.memOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.memOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_mem_outcome_of_frame op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        primitiveFrame middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.memOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.memOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- A successful thunk operation primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_thunk_success {C F : Type} (op : AstHOL.ThunkOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (notForce : op ≠ .forceThunk)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.thunkOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.thunkOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.thunkOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.thunkOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.thunkOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_thunk_outcome op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        notForce middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.thunkOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.thunkOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- Complete word-operation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful word application handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_word {C F : Type} (op : ClosLang.WordOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.wordOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.wordOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.wordOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.wordOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.wordOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := wordOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.wordOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_word_success op args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- Complete block op expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful block op handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_block {C F : Type} (op : ClosLang.BlockOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.blockOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.blockOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.blockOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.blockOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.blockOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := blockOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.blockOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_block_success op args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- Complete installation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful installation handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_install {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op .install args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op .install args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError .install args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp .install values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op .install args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := install_error_is_typeError values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op .install args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_install_success args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- Memory expression simulation conditional on the primitive frame.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_mem_of_frame {C F : Type} (op : ClosLang.MemOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F)
    (primitiveFrame : ∀ (args : List DataSem.Value) (before after : DataSem.State C F) (value : DataSem.Value),
      DataSem.doApp (.memOp op) args before = .val (value, after) → DataSem.SameLocalControl before after)
    (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.memOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.memOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.memOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.memOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := memOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.memOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_mem_success_of_frame op args env s1 smid s2 values result primitiveFrame ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- Reference allocation satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_ref {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .ref) args] env s1 :=
  simulationFor_op_mem_of_frame .ref args env s1
    (DataSem.doApp_mem_frame_of_aux .ref DataSem.doAppAux_ref_frame) ih

/-- Array allocation satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_refArray {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .refArray) args] env s1 :=
  simulationFor_op_mem_of_frame .refArray args env s1
    (DataSem.doApp_mem_frame_of_aux .refArray DataSem.doAppAux_refArray_frame) ih

/-- GC configuration satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_configGC {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .configGC) args] env s1 :=
  simulationFor_op_mem_of_frame .configGC args env s1
    (DataSem.doApp_mem_frame_of_aux .configGC DataSem.doAppAux_configGC_frame) ih

/-- Array bounds checking satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_boundsCheckArray {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .boundsCheckArray) args] env s1 :=
  simulationFor_op_mem_of_frame .boundsCheckArray args env s1
    (DataSem.doApp_mem_frame_of_aux .boundsCheckArray DataSem.doAppAux_boundsCheckArray_frame) ih

/-- Both byte-array bounds-check modes satisfy the expression simulation. -/
theorem simulationFor_op_boundsCheckByte {C F : Type} (loose : Bool) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.boundsCheckByte loose)) args] env s1 :=
  simulationFor_op_mem_of_frame (.boundsCheckByte loose) args env s1
    (DataSem.doApp_mem_frame_of_aux (.boundsCheckByte loose) (DataSem.doAppAux_boundsCheckByte_frame loose)) ih

/-- Array length satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_length {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .length) args] env s1 :=
  simulationFor_op_mem_of_frame .length args env s1
    (DataSem.doApp_mem_frame_of_aux .length DataSem.doAppAux_length_frame) ih

/-- Byte-array length satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_lengthByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .lengthByte) args] env s1 :=
  simulationFor_op_mem_of_frame .lengthByte args env s1
    (DataSem.doApp_mem_frame_of_aux .lengthByte DataSem.doAppAux_lengthByte_frame) ih

/-- Indexed reads satisfy the BVI-to-data expression simulation. -/
theorem simulationFor_op_el {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .el) args] env s1 :=
  simulationFor_op_mem_of_frame .el args env s1
    (DataSem.doApp_mem_frame_of_aux .el DataSem.doAppAux_el_frame) ih

/-- Byte-array reads satisfy the BVI-to-data expression simulation. -/
theorem simulationFor_op_derefByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .derefByte) args] env s1 :=
  simulationFor_op_mem_of_frame .derefByte args env s1
    (DataSem.doApp_mem_frame_of_aux .derefByte DataSem.doAppAux_derefByte_frame) ih

/-- Array updates satisfy the BVI-to-data expression simulation. -/
theorem simulationFor_op_update {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .update) args] env s1 :=
  simulationFor_op_mem_of_frame .update args env s1
    (DataSem.doApp_mem_frame_of_aux .update DataSem.doAppAux_update_frame) ih

/-- Byte-array updates satisfy the BVI-to-data expression simulation. -/
theorem simulationFor_op_updateByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .updateByte) args] env s1 :=
  simulationFor_op_mem_of_frame .updateByte args env s1
    (DataSem.doApp_mem_frame_of_aux .updateByte DataSem.doAppAux_updateByte_frame) ih

/-- Byte-array allocation satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_refByte {C F : Type} (flag : Bool) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.refByte flag)) args] env s1 :=
  simulationFor_op_mem_of_frame (.refByte flag) args env s1
    (DataSem.doApp_mem_frame_of_aux (.refByte flag) (DataSem.doAppAux_refByte_frame flag)) ih

/-- Mutable-constructor allocation satisfies the expression simulation. -/
theorem simulationFor_op_mutCons {C F : Type} (tag index : Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.mutCons tag index)) args] env s1 :=
  simulationFor_op_mem_of_frame (.mutCons tag index) args env s1
    (DataSem.doApp_mem_frame_of_aux (.mutCons tag index) (DataSem.doAppAux_mutCons_frame tag index)) ih

/-- Constructor finalisation satisfies the expression simulation. -/
theorem simulationFor_op_finaliseCons {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .finaliseCons) args] env s1 :=
  simulationFor_op_mem_of_frame .finaliseCons args env s1
    (DataSem.doApp_mem_frame_of_aux .finaliseCons DataSem.doAppAux_finaliseCons_frame) ih

/-- Mutable-constructor updates satisfy the expression simulation. -/
theorem simulationFor_op_updateCons {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .updateCons) args] env s1 :=
  simulationFor_op_mem_of_frame .updateCons args env s1
    (DataSem.doApp_mem_frame_of_aux .updateCons DataSem.doAppAux_updateCons_frame) ih

/-- String comparison satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_stringCmp {C F : Type} (fast : Bool) (cmp : Opb) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.stringCmp fast cmp)) args] env s1 :=
  simulationFor_op_mem_of_frame (.stringCmp fast cmp) args env s1
    (DataSem.doApp_mem_frame_of_aux (.stringCmp fast cmp) (DataSem.doAppAux_stringCmp_frame fast cmp)) ih

/-- Byte-array XOR satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_xorByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .xorByte) args] env s1 :=
  simulationFor_op_mem_of_frame .xorByte args env s1
    (DataSem.doApp_mem_frame_of_aux .xorByte DataSem.doAppAux_xorByte_frame) ih

/-- The current source evaluator rejects `concatByteVec`; its expression simulation
therefore only propagates argument errors. -/
theorem simulationFor_op_concatByteVec {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .concatByteVec) args] env s1 :=
  simulationFor_op_mem_of_frame .concatByteVec args env s1
    (DataSem.doApp_mem_frame_of_aux .concatByteVec DataSem.doAppAux_concatByteVec_frame) ih

/-- The current source evaluator rejects `fromListByte`; its expression simulation
therefore only propagates argument errors. -/
theorem simulationFor_op_fromListByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .fromListByte) args] env s1 :=
  simulationFor_op_mem_of_frame .fromListByte args env s1
    (DataSem.doApp_mem_frame_of_aux .fromListByte DataSem.doAppAux_fromListByte_frame) ih

/-- The current source evaluator rejects `toListByte`; its expression simulation
therefore only propagates argument errors. -/
theorem simulationFor_op_toListByte {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .toListByte) args] env s1 :=
  simulationFor_op_mem_of_frame .toListByte args env s1
    (DataSem.doApp_mem_frame_of_aux .toListByte DataSem.doAppAux_toListByte_frame) ih

/-- The current source evaluator rejects `lengthByteVec`; its expression simulation
therefore only propagates argument errors. -/
theorem simulationFor_op_lengthByteVec {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .lengthByteVec) args] env s1 :=
  simulationFor_op_mem_of_frame .lengthByteVec args env s1
    (DataSem.doApp_mem_frame_of_aux .lengthByteVec DataSem.doAppAux_lengthByteVec_frame) ih

/-- The current source evaluator rejects `derefByteVec`; its expression simulation
therefore only propagates argument errors. -/
theorem simulationFor_op_derefByteVec {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp .derefByteVec) args] env s1 :=
  simulationFor_op_mem_of_frame .derefByteVec args env s1
    (DataSem.doApp_mem_frame_of_aux .derefByteVec DataSem.doAppAux_derefByteVec_frame) ih

/-- The source evaluator rejects the `true` byte-copy mode after evaluating
its arguments, so only argument errors can satisfy the simulation premise. -/
theorem simulationFor_op_copyByte_true {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.copyByte true)) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.memOp (.copyByte true)) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.memOp (.copyByte true)) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    have whole : BviSem.evaluate [.op (.memOp (.copyByte true)) args] env s1 =
        (.err (.abort .typeError), smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]
    rw [whole] at run
    cases run
    exact False.elim (notTypeError rfl)

/-- False-mode byte copy satisfies the BVI-to-data expression simulation. -/
theorem simulationFor_op_copyByte_false {C F : Type} (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp (.copyByte false)) args] env s1 :=
  simulationFor_op_mem_of_frame (.copyByte false) args env s1
    (DataSem.doApp_mem_frame_of_aux (.copyByte false) DataSem.doAppAux_copyByte_false_frame) ih

/-- All memory operations satisfy the expression simulation. The result is
untagged pending evaluator correspondence review. -/
theorem simulationFor_op_mem {C F : Type} (op : ClosLang.MemOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.memOp op) args] env s1 := by
  cases op with
  | ref => exact simulationFor_op_ref args env s1 ih
  | update => exact simulationFor_op_update args env s1 ih
  | el => exact simulationFor_op_el args env s1 ih
  | length => exact simulationFor_op_length args env s1 ih
  | lengthByte => exact simulationFor_op_lengthByte args env s1 ih
  | refByte flag => exact simulationFor_op_refByte flag args env s1 ih
  | refArray => exact simulationFor_op_refArray args env s1 ih
  | derefByte => exact simulationFor_op_derefByte args env s1 ih
  | updateByte => exact simulationFor_op_updateByte args env s1 ih
  | concatByteVec => exact simulationFor_op_concatByteVec args env s1 ih
  | copyByte flag =>
    cases flag with
    | false => exact simulationFor_op_copyByte_false args env s1 ih
    | true => exact simulationFor_op_copyByte_true args env s1 ih
  | fromListByte => exact simulationFor_op_fromListByte args env s1 ih
  | toListByte => exact simulationFor_op_toListByte args env s1 ih
  | lengthByteVec => exact simulationFor_op_lengthByteVec args env s1 ih
  | derefByteVec => exact simulationFor_op_derefByteVec args env s1 ih
  | stringCmp fast cmp => exact simulationFor_op_stringCmp fast cmp args env s1 ih
  | xorByte => exact simulationFor_op_xorByte args env s1 ih
  | boundsCheckArray => exact simulationFor_op_boundsCheckArray args env s1 ih
  | boundsCheckByte loose => exact simulationFor_op_boundsCheckByte loose args env s1 ih
  | mutCons tag index => exact simulationFor_op_mutCons tag index args env s1 ih
  | updateCons => exact simulationFor_op_updateCons args env s1 ih
  | finaliseCons => exact simulationFor_op_finaliseCons args env s1 ih
  | configGC => exact simulationFor_op_configGC args env s1 ih

/-- Complete thunk operation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful thunk operation handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_thunk {C F : Type} (op : AstHOL.ThunkOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.thunkOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.thunkOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.thunkOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.thunkOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.thunkOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := thunkOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.thunkOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      by_cases notForce : op ≠ .forceThunk
      · exact (simulationFor_op_thunk_success op args env s1 smid s2 values result notForce ih argsRun opRun
          t1 n corr tail live vars fresh related livePresent).2
      · have force : op = .forceThunk := by simpa using notForce
        subst op
        cases values.reverse <;>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at opRun

/-- A successful returning FFI primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_ffi_success {C F : Type} (name : Basis.Pure.MlString.MlString) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.ffi name) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.ffi name) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.ffi name) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.ffi name) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.ffi name) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_ffi_outcome name tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.ffi name) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.ffi name) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- Complete FFI-operation expression case of the BVI-to-data simulation,
including returning calls, terminal events and argument errors. This remains
untagged pending evaluator correspondence review. -/
theorem simulationFor_op_ffi {C F : Type} (name : Basis.Pure.MlString.MlString) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.ffi name) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.ffi name) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.ffi name) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.ffi name) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.ffi name) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have notType : error ≠ .abort .typeError := by
        intro equal
        exact notTypeError (by rw [equal])
      obtain ⟨event, rfl⟩ := ffiOp_error_is_final name values.reverse s2 error opRun notType
      exact (simulationFor_op_ffiError name args env s1 s2 values event ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.ffi name) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_ffi_success name args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- A successful global primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_global_success {C F : Type} (op : ClosLang.GlobOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.globOp op) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.globOp op) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.globOp op) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.globOp op) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.globOp op) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_global_outcome op tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.globOp op) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.globOp op) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- Complete global-operation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful global application handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_global {C F : Type} (op : ClosLang.GlobOp) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.globOp op) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.globOp op) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.globOp op) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.globOp op) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.globOp op) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := globalOp_error_is_typeError op values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.globOp op) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_global_success op args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- A successful label primitive expression satisfies the compiler
simulation invariant in tail and non-tail position. This source case remains
untagged pending evaluator review and assembly of the complete operation proof. -/
theorem simulationFor_op_label_success {C F : Type} (label : Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 smid s2 : BviSem.BviState C F)
    (values : List BvlSem.Value) (result : BvlSem.Value)
    (ih : simulationFor args env s1) (argsRun : BviSem.evaluate args env s1 = (.val values, smid))
    (opRun : BviSem.doApp (.label label) values.reverse smid = .val (result, s2))
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1) (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none) :
    BviSem.evaluate [.op (.label label) args] env s1 = (.val [result], s2) ∧
    ∃ t2 prog pres names next ls,
      compileSource n corr tail live [.op (.label label) args] = (prog, names, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome (.val [result]) t1 t2 n next corr live names env tail pres ls := by
  have wholeRun : BviSem.evaluate [.op (.label label) args] env s1 = (.val [result], s2) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp [opRun]
  obtain ⟨tmid, argsProg, pres, argNames, n1, ls, compiled, target, middleRel, outcome⟩ :=
    ih (.val values) smid t1 n corr false live argsRun (by simp) vars (by simp) fresh related livePresent
      (by simp [isException])
  cases pres with
  | some result => simp [correctOutcome, isResult] at outcome
  | none =>
    have firstOutcome := outcome
    have liveMidAll := correctOutcome_live values t1 tmid n n1 corr live argNames env ls outcome livePresent
    have liveMid : ∀ v ∈ live, sptLookup v tmid.locals ≠ none := by
      intro v member
      exact liveMidAll v (List.mem_append_right argNames member)
    rcases outcome with ⟨_, _, _, freshMid, varsMid, _, _, _, _, _, resultVars⟩
    obtain ⟨dataValues, read, projected⟩ := getVars_lift argNames values tmid.locals resultVars
    have projectedRun : BviSem.doApp (.label label) (dataValues.reverse.map dataToBviValue) smid = .val (result, s2) := by
      simpa [List.map_reverse, ← projected] using opRun
    obtain ⟨tassign, dataValue, assignmentRun, resultProjection, finalRel, destRead, assignmentOutcome⟩ :=
      evaluate_iAssign_label_outcome label tmid smid s2 argNames.reverse live corr env dataValues.reverse n1 result
        middleRel varsMid liveMid freshMid (DataProps.getVars_reverse argNames tmid.locals dataValues read) projectedRun
    let assignment := iAssign n1 (.label label) argNames.reverse live corr
    let inner := DataLang.Prog.seq argsProg assignment
    have sourceBound := BviSem.evaluate_clock_le args env s1
    rw [argsRun] at sourceBound
    have middleBound : tmid.clock ≤ t1.clock := by simpa [← related.1, ← middleRel.1] using sourceBound
    have innerRun : DataSem.evaluate inner t1 = (none, tassign) :=
      evaluateSeq_continue argsProg assignment t1 tmid _ target middleBound assignmentRun
    have innerOutcome := correctOutcome_seq values (.val [result]) t1 tmid tassign n n1 (n1 + 1) corr live
      argNames [n1] env false none ls none firstOutcome assignmentOutcome
    cases tail with
    | false =>
      refine ⟨wholeRun, tassign, inner, none, [n1], n1 + 1, none, ?_, innerRun, finalRel, innerOutcome⟩
      simp [compileSource, compiled, assignment, inner]
    | true =>
      have fullBound := BviSem.evaluate_clock_le [.op (.label label) args] env s1
      rw [wholeRun] at fullBound
      have targetBound : tassign.clock ≤ t1.clock := by simpa [← related.1, ← finalRel.1] using fullBound
      have returnRun : DataSem.evaluate (.return [n1]) tassign =
          (some (.val [dataValue]), DataSem.flushState false tassign) := by
        simp [DataSem.evaluate, DataSem.getVars, DataSem.getVar, destRead]
      refine ⟨wholeRun, DataSem.flushState false tassign, .seq inner (.return [n1]), some (.val [dataValue]),
        [n1], n1 + 1, none, ?_, ?_, ?_, ?_⟩
      · simp [compileSource, compiled, assignment, inner]
      · exact evaluateSeq_continue inner (.return [n1]) t1 tassign _ innerRun targetBound returnRun
      · simpa [stateRel, DataSem.flushState] using finalRel
      · have stack := innerOutcome.2.2.2.2.2.2.2.1
        have handler := innerOutcome.2.2.2.2.2.2.2.2.1
        simp [correctOutcome, dataToBviResult, isResult, isReturn, isException,
          DataSem.flushState, ← resultProjection, stack, handler]

/-- Complete label-operation expression case of the BVI-to-data simulation.
The recursive hypothesis covers its argument list; non-type errors propagate
from arguments, and successful label application handles both tail modes.
This remains untagged pending evaluator correspondence review. -/
theorem simulationFor_op_label {C F : Type} (label : Nat) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op (.label label) args] env s1 := by
  intro res s2 t1 n corr tail live run notTypeError vars _ fresh related livePresent exceptionJump
  generalize argsRun : BviSem.evaluate args env s1 = pair
  obtain ⟨argResult, smid⟩ := pair
  cases argResult with
  | err error =>
    have whole : BviSem.evaluate [.op (.label label) args] env s1 = (.err error, smid) := by
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    rw [whole] at run
    cases run
    exact (simulationFor_op_argsError (.label label) args env s1 s2 error ih argsRun notTypeError
      t1 n corr tail live vars fresh related livePresent exceptionJump).2
  | val values =>
    generalize opRun : BviSem.doApp (.label label) values.reverse smid = opResult
    cases opResult with
    | err error =>
      have whole : BviSem.evaluate [.op (.label label) args] env s1 = (.err error, smid) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      have onlyTypeError := labelOp_error_is_typeError label values.reverse s2 error opRun
      exact False.elim (notTypeError (by rw [onlyTypeError]))
    | val pair =>
      obtain ⟨result, slast⟩ := pair
      have whole : BviSem.evaluate [.op (.label label) args] env s1 = (.val [result], slast) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp [opRun]
      rw [whole] at run
      cases run
      exact (simulationFor_op_label_success label args env s1 smid s2 values result ih argsRun opRun
        t1 n corr tail live vars fresh related livePresent).2

/-- Every BVI operation satisfies the expression simulation, assuming the
argument-list induction hypothesis. This assembled result remains untagged
pending correspondence review of the BVI and data evaluators. -/
theorem simulationFor_op {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (env : List BvlSem.Value) (s1 : BviSem.BviState C F) (ih : simulationFor args env s1) :
    simulationFor [.op op args] env s1 := by
  cases op with
  | label label => exact simulationFor_op_label label args env s1 ih
  | ffi name => exact simulationFor_op_ffi name args env s1 ih
  | intOp op => exact simulationFor_op_int op args env s1 ih
  | wordOp op => exact simulationFor_op_word op args env s1 ih
  | blockOp op => exact simulationFor_op_block op args env s1 ih
  | globOp op => exact simulationFor_op_global op args env s1 ih
  | memOp op => exact simulationFor_op_mem op args env s1 ih
  | thunkOp op => exact simulationFor_op_thunk op args env s1 ih
  | install => exact simulationFor_op_install args env s1 ih

end Flapjack.Compiler.Backend.BviToData
