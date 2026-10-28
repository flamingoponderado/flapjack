import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EnvironmentDomain
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalPattern
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock

/-! Execution of the flat expression generated for source Eval. The
proof-side evaluators and factored relations remain under HOL review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- If the flat Eval callback and declaration body succeed, the generated
body reads the stored environment ID through the reserved global reference.
The declaration run is the declaration induction hypothesis. -/
theorem evaluate_evalBody_success {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state last : FlatSem.State C F)
    (bytes words stored : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C)
    (decoded : FlatSem.doEval [bytes, words] state.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (positive : 0 < state.clock)
    (declarationRun : FlatSem.evaluateDecs (FlatSem.decClock { state with evalConfig := nextConfig }) decs =
      (last, none))
    (globals : last.globals[0]? = some (some (.loc true 0)))
    (references : last.refs[0]? = some (.refv stored)) :
    let evalEnv : FlatSem.Environment FlatSem.Value :=
      { env with v := (ofString "words", words) :: (ofString "bytes", bytes) :: env.v }
    let body : FlatLang.Exp :=
      .let_ .none none (.app .none (.src .eval)
        ([ofString "bytes", ofString "words"].map (.varLocal .none)))
        (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
          (.app .none (.el 0) [.varLocal .none (ofString "r")]))
    FlatSem.evaluate evalEnv state [body] = (last, .val [stored]) := by
  have lastBound : last.clock ≤ state.clock := by
    have bound := FlatSem.evaluate_clock_spec.2.2 _ _ _ _ declarationRun
    exact Nat.le_trans bound (Nat.sub_le _ _)
  have namesDistinct : ofString "bytes" ≠ ofString "words" := by decide
  have nonzero : state.clock ≠ 0 := Nat.ne_of_gt positive
  have declarations : FlatSem.evaluateDecs
      { state with clock := state.clock - 1, evalConfig := nextConfig } decs = (last, none) := by
    simpa [FlatSem.decClock] using declarationRun
  simp [List.lookup, BEq.beq, namesDistinct, FlatSem.evaluate, FlatSem.fixClock, FlatSem.decClock, FlatSem.applyResult,
    FlatSem.doApp, FlatSem.doAppFlat, FlatSem.unitValue, storeLookup,
    decoded, nonzero, declarations, globals, references, Nat.min_eq_right lastBound]

/-- An error from the evaluated declarations propagates through the generated
body without reading the reserved global reference. -/
theorem evaluate_evalBody_error {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state last : FlatSem.State C F)
    (bytes words : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C) (error : ErrorResult FlatSem.Value)
    (decoded : FlatSem.doEval [bytes, words] state.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (positive : 0 < state.clock)
    (declarationRun : FlatSem.evaluateDecs (FlatSem.decClock { state with evalConfig := nextConfig }) decs =
      (last, some error)) :
    let evalEnv : FlatSem.Environment FlatSem.Value :=
      { env with v := (ofString "words", words) :: (ofString "bytes", bytes) :: env.v }
    let body : FlatLang.Exp :=
      .let_ .none none (.app .none (.src .eval)
        ([ofString "bytes", ofString "words"].map (.varLocal .none)))
        (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
          (.app .none (.el 0) [.varLocal .none (ofString "r")]))
    FlatSem.evaluate evalEnv state [body] = (last, .err error) := by
  have lastBound : last.clock ≤ state.clock := by
    have bound := FlatSem.evaluate_clock_spec.2.2 _ _ _ _ declarationRun
    exact Nat.le_trans bound (Nat.sub_le _ _)
  have namesDistinct : ofString "bytes" ≠ ofString "words" := by decide
  have nonzero : state.clock ≠ 0 := Nat.ne_of_gt positive
  have declarations : FlatSem.evaluateDecs
      { state with clock := state.clock - 1, evalConfig := nextConfig } decs = (last, some error) := by
    simpa [FlatSem.decClock] using declarationRun
  simp [List.lookup, BEq.beq, namesDistinct, FlatSem.evaluate, FlatSem.fixClock,
    FlatSem.decClock, decoded, nonzero, declarations, Nat.min_eq_right lastBound]

/-- The callback installs its next configuration before the zero-clock
timeout; no declarations or reserved-reference lookup are executed. -/
theorem evaluate_evalBody_timeout {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (bytes words : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C)
    (decoded : FlatSem.doEval [bytes, words] state.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (zero : state.clock = 0) :
    let evalEnv : FlatSem.Environment FlatSem.Value :=
      { env with v := (ofString "words", words) :: (ofString "bytes", bytes) :: env.v }
    let body : FlatLang.Exp :=
      .let_ .none none (.app .none (.src .eval)
        ([ofString "bytes", ofString "words"].map (.varLocal .none)))
        (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
          (.app .none (.el 0) [.varLocal .none (ofString "r")]))
    FlatSem.evaluate evalEnv state [body] =
      ({ state with evalConfig := nextConfig }, .err (.abort .timeoutError)) := by
  have namesDistinct : ofString "bytes" ≠ ofString "words" := by decide
  simp [List.lookup, BEq.beq, namesDistinct, FlatSem.evaluate, FlatSem.fixClock, decoded, zero]

/-- A rejected Eval callback reports a type error in the unchanged state. -/
theorem evaluate_evalBody_rejected {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (bytes words : FlatSem.Value)
    (decoded : FlatSem.doEval [bytes, words] state.evalConfig = none) :
    let evalEnv : FlatSem.Environment FlatSem.Value :=
      { env with v := (ofString "words", words) :: (ofString "bytes", bytes) :: env.v }
    let body : FlatLang.Exp :=
      .let_ .none none (.app .none (.src .eval)
        ([ofString "bytes", ofString "words"].map (.varLocal .none)))
        (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
          (.app .none (.el 0) [.varLocal .none (ofString "r")]))
    FlatSem.evaluate evalEnv state [body] = (state, .err (.abort .typeError)) := by
  have namesDistinct : ofString "bytes" ≠ ofString "words" := by decide
  simp [List.lookup, BEq.beq, namesDistinct, FlatSem.evaluate, FlatSem.fixClock, decoded]

/-- The generated six-element pattern binds the last two operands before
running the Eval body. This isolates pattern selection from the body result. -/
theorem evaluate_compileEval_body {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state arguments last : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words : FlatSem.Value) (result : Result (List FlatSem.Value) FlatSem.Value)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (arguments, .val [words, bytes, d, c, b, a]))
    (bodyRun :
      let evalEnv : FlatSem.Environment FlatSem.Value :=
        { env with v := (ofString "words", words) :: (ofString "bytes", bytes) :: env.v }
      let body : FlatLang.Exp :=
        .let_ .none none (.app .none (.src .eval)
          ([ofString "bytes", ofString "words"].map (.varLocal .none)))
          (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
            (.app .none (.el 0) [.varLocal .none (ofString "r")]))
      FlatSem.evaluate evalEnv arguments [body] = (last, result)) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] = (last, result) := by
  let body : FlatLang.Exp :=
    .let_ .none none (.app .none (.src .eval)
      ([ofString "bytes", ofString "words"].map (.varLocal .none)))
      (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
        (.app .none (.el 0) [.varLocal .none (ofString "r")]))
  let pattern : FlatLang.Pat :=
    .pcon none [.pany, .pany, .pany, .pany, .pvar (ofString "bytes"), .pvar (ofString "words")]
  let : Nonempty FlatSem.Value := ⟨.conv none []⟩
  have tupleRun : FlatSem.evaluate env state [.con .none none (compileExps trace compMap exprs)] =
      (arguments, .val [.conv none [a, b, c, d, bytes, words]]) := by
    simp [FlatSem.evaluate, operandRun]
  have argumentBound : arguments.clock ≤ state.clock := by
    exact FlatSem.evaluate_clock_spec.1 _ _ _ _ _ operandRun
  have fixed : FlatSem.fixClock state (arguments, (Result.val [.conv none [a, b, c, d, bytes, words]] :
      Result (List FlatSem.Value) FlatSem.Value)) =
      (arguments, Result.val [.conv none [a, b, c, d, bytes, words]]) := by
    simp [FlatSem.fixClock, Nat.min_eq_right argumentBound]
  have matchRow : FlatSem.pmatchRows [(pattern, body)] arguments (.conv none [a, b, c, d, bytes, words]) =
      .match ([(ofString "words", words), (ofString "bytes", bytes)], pattern, body) := by
    have row := pmatchRows_dropFour [a, b, c, d, bytes, words] (ofString "bytes") (ofString "words")
      body arguments (by rfl)
    simpa [pattern, Flapjack.holEl, Flapjack.holLast, Flapjack.holHd] using row
  have namesDistinct : ofString "bytes" ≠ ofString "words" := by decide
  have selection : FlatSem.selectRow arguments [(pattern, body)] (.conv none [a, b, c, d, bytes, words])
      FlatSem.bindExnV = .ok ([(ofString "words", words), (ofString "bytes", bytes)], body) := by
    simp [FlatSem.selectRow, matchRow, pattern, FlatLang.patBindings, FlatLang.patsBindings,
      Ne.symm namesDistinct]
  change FlatSem.evaluate env state [.mat .none (.con .none none (compileExps trace compMap exprs))
    [(pattern, body)]] = (last, result)
  rw [FlatSem.evaluate, tupleRun, fixed]
  simp (config := { zeta := false })
  have selection' := selection
  dsimp only [body] at selection'
  rw [selection']
  simpa [body] using bodyRun

/-- On six successfully evaluated operands, the generated pattern passes the
last two values to the flat callback and returns the stored environment ID. -/
theorem evaluate_compileEval_success {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state arguments last : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words stored : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (arguments, .val [words, bytes, d, c, b, a]))
    (decoded : FlatSem.doEval [bytes, words] arguments.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (positive : 0 < arguments.clock)
    (declarationRun : FlatSem.evaluateDecs (FlatSem.decClock { arguments with evalConfig := nextConfig }) decs =
      (last, none))
    (globals : last.globals[0]? = some (some (.loc true 0)))
    (references : last.refs[0]? = some (.refv stored)) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] = (last, .val [stored]) := by
  exact evaluate_compileEval_body env state arguments last trace compMap exprs a b c d bytes words
    (.val [stored]) operandRun
    (evaluate_evalBody_success env arguments last bytes words stored decs nextConfig
      decoded positive declarationRun globals references)

/-- A declaration error propagates through the complete generated Eval
expression after its six operands have succeeded. -/
theorem evaluate_compileEval_error {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state arguments last : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C) (error : ErrorResult FlatSem.Value)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (arguments, .val [words, bytes, d, c, b, a]))
    (decoded : FlatSem.doEval [bytes, words] arguments.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (positive : 0 < arguments.clock)
    (declarationRun : FlatSem.evaluateDecs (FlatSem.decClock { arguments with evalConfig := nextConfig }) decs =
      (last, some error)) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] = (last, .err error) := by
  exact evaluate_compileEval_body env state arguments last trace compMap exprs a b c d bytes words
    (.err error) operandRun
    (evaluate_evalBody_error env arguments last bytes words decs nextConfig error decoded positive declarationRun)

/-- The generated Eval expression times out after installing the callback's
next configuration when its operands exhaust the clock. -/
theorem evaluate_compileEval_timeout {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state arguments : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words : FlatSem.Value) (decs : List FlatLang.Exp)
    (nextConfig : FlatSem.InstallConfig C)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (arguments, .val [words, bytes, d, c, b, a]))
    (decoded : FlatSem.doEval [bytes, words] arguments.evalConfig = some (decs, nextConfig, FlatSem.unitValue))
    (zero : arguments.clock = 0) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] =
      ({ arguments with evalConfig := nextConfig }, .err (.abort .timeoutError)) := by
  exact evaluate_compileEval_body env state arguments { arguments with evalConfig := nextConfig }
    trace compMap exprs a b c d bytes words (.err (.abort .timeoutError)) operandRun
    (evaluate_evalBody_timeout env arguments bytes words decs nextConfig decoded zero)

/-- A rejected callback propagates the same type error through the complete
generated expression. -/
theorem evaluate_compileEval_rejected {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state arguments : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words : FlatSem.Value)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (arguments, .val [words, bytes, d, c, b, a]))
    (decoded : FlatSem.doEval [bytes, words] arguments.evalConfig = none) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] =
      (arguments, .err (.abort .typeError)) := by
  exact evaluate_compileEval_body env state arguments arguments trace compMap exprs a b c d bytes words
    (.err (.abort .typeError)) operandRun (evaluate_evalBody_rejected env arguments bytes words decoded)

/-- An operand error prevents pattern selection and propagates unchanged. -/
theorem evaluate_compileEval_operand_error {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state last : FlatSem.State C F)
    (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (error : ErrorResult FlatSem.Value)
    (operandRun : FlatSem.evaluate env state (compileExps trace compMap exprs).reverse =
      (last, .err error)) :
    FlatSem.evaluate env state [compileExp trace compMap (.app .eval exprs)] = (last, .err error) := by
  have bound : last.clock ≤ state.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ operandRun
  simp [compileExp, FlatSem.evaluate, operandRun, FlatSem.fixClock, Nat.min_eq_right bound]

/-- The operand-error case of source-to-flat Eval simulation. The list
simulation is the induction hypothesis; the preliminary relations are not
yet reviewed as the original HOL invariant. -/
theorem exprSim_eval_operand_error {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (trace : List VarN) (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (exprs : List AstHOL.Exp)
    (sourceLast : SemanticPrimitivesHOL.State F) (error : ErrorResult Value)
    (operandRun : EvaluateHOL.evaluate sourceState sourceEnv exprs.reverse = (sourceLast, .err error))
    (operandSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState exprs.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .eval exprs) := by
  unfold ExprListSim at operandSim
  rw [compileExps_reverse, operandRun] at operandSim
  cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse with
  | mk flatLast flatResult =>
    rw [flatRun] at operandSim
    obtain ⟨resultRel, states⟩ := operandSim
    cases resultRel with
    | raise valueRel =>
      unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv exprs.reverse []).1, operandRun]
      rw [evaluate_compileEval_operand_error flatEnv flatState flatLast trace compMap exprs _ flatRun]
      exact ⟨.raise valueRel, states⟩
    | abort kind =>
      unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv exprs.reverse []).1, operandRun]
      rw [evaluate_compileEval_operand_error flatEnv flatState flatLast trace compMap exprs _ flatRun]
      exact ⟨.abort kind, states⟩

/-- Source Eval follows successful operand evaluation, callback decoding,
declaration execution, and environment declaration, restoring the caller's
generation in the final state. -/
theorem evaluate_sourceEval_success {F : Type}
    (env evalEnv newEnv : SemEnv Value) (state arguments last : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (begin after : Option EvalState) (value : Value)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (positive : 0 < arguments.clock)
    (declarationRun : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { arguments with evalState := begin }) evalEnv decs = (last, .val newEnv))
    (declared : declareEnv last.evalState (extendDecEnv newEnv evalEnv) = some (value, after)) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      ({ last with evalState := resetEnvGeneration arguments.evalState after }, .val [value]) := by
  have nonzero : arguments.clock ≠ 0 := Nat.ne_of_gt positive
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate state env exprs.reverse []).1, operandRun]
  simp only [List.reverse_reverse, getOpClass]
  rw [EvaluateHOL.fixClockDoEvalRes]
  simp only [EvaluateHOL.doEvalRes, decoded, nonzero, if_false]
  rw [(EvaluateHOL.fixClockEvaluate (EvaluateHOL.decClock { arguments with evalState := begin })
    evalEnv [] decs).2, declarationRun]
  simp [declared]

/-- A successful callback at clock zero returns timeout after installing the
source callback state, before executing any declaration. -/
theorem evaluate_sourceEval_timeout {F : Type}
    (env evalEnv : SemEnv Value) (state arguments : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec) (begin : Option EvalState)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (zero : arguments.clock = 0) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      ({ arguments with evalState := begin }, .err (.abort .timeoutError)) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate state env exprs.reverse []).1, operandRun]
  simp only [List.reverse_reverse, getOpClass]
  rw [EvaluateHOL.fixClockDoEvalRes]
  simp [EvaluateHOL.doEvalRes, decoded, zero, EvaluateHOL.timeoutError]

/-- A declaration error propagates from source Eval. Raised exceptions reset
the generation, while aborts retain the declaration state as in CakeML. -/
theorem evaluate_sourceEval_declaration_error {F : Type}
    (env evalEnv : SemEnv Value) (state arguments last : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (begin : Option EvalState) (error : ErrorResult Value)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (positive : 0 < arguments.clock)
    (declarationRun : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { arguments with evalState := begin }) evalEnv decs = (last, .err error)) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      (match error with
       | .abort _ => last
       | .raise _ => { last with evalState := resetEnvGeneration arguments.evalState last.evalState }, .err error) := by
  have nonzero : arguments.clock ≠ 0 := Nat.ne_of_gt positive
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate state env exprs.reverse []).1, operandRun]
  simp only [List.reverse_reverse, getOpClass]
  rw [EvaluateHOL.fixClockDoEvalRes]
  simp only [EvaluateHOL.doEvalRes, decoded, nonzero, if_false]
  rw [(EvaluateHOL.fixClockEvaluate (EvaluateHOL.decClock { arguments with evalState := begin })
    evalEnv [] decs).2]
  cases error <;> simp_all only

/-- An error in the declaration induction hypothesis propagates through
both Eval expressions and preserves the factored result and state relations.
The source and flat declaration runs are the induction hypothesis; neither
whole Eval result is assumed. -/
theorem evaluate_eval_declaration_error_related {C F : Type}
    (genv : GlobalEnv) (envId : Nat × Nat) (config nextConfig : Config)
    (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (sourceEnv evalEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceInitial sourceArguments sourceLast : SemanticPrimitivesHOL.State F)
    (flatInitial flatArguments flatLast : FlatSem.State C F)
    (begin : Option EvalState) (sourceError : ErrorResult Value) (flatError : ErrorResult FlatSem.Value)
    (exprs : List AstHOL.Exp) (sourceValues : List Value) (a b c d bytes words : FlatSem.Value)
    (flatNextConfig : FlatSem.InstallConfig C) (trace : List VarN) (compMap : Environment)
    (n : Nat) (next : NextIndices) (newMap : Environment) (gen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp)
    (sourceRun : EvaluateHOL.evaluate sourceInitial sourceEnv exprs.reverse =
      (sourceArguments, .val sourceValues.reverse))
    (sourceDecoded : SemanticPrimitivesHOL.doEval sourceValues sourceArguments.evalState =
      some (evalEnv, decs, begin))
    (positive : 0 < sourceArguments.clock)
    (sourceDeclarations : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { sourceArguments with evalState := begin }) evalEnv decs =
        (sourceLast, .err sourceError))
    (flatRun : FlatSem.evaluate flatEnv flatInitial (compileExps trace compMap exprs).reverse =
      (flatArguments, .val [words, bytes, d, c, b, a]))
    (flatDecoded : FlatSem.doEval [bytes, words] flatArguments.evalConfig =
      some (flatDecs, flatNextConfig, FlatSem.unitValue))
    (compiled : incCompileProg envId config decs = (nextConfig, flatDecs))
    (compiledBody : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, newMap, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { FlatSem.decClock { flatArguments with evalConfig := flatNextConfig } with
        globals := flatArguments.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
        (flatLast, some flatError))
    (argumentsRel : StateRel genv sourceArguments flatArguments)
    (lastRel : StateRel genv sourceLast flatLast)
    (errorRel : EvalResultRel genv (.err sourceError) (.err flatError)) :
    let sourceResult := EvaluateHOL.evaluate sourceInitial sourceEnv [.app .eval exprs]
    let flatResult := FlatSem.evaluate flatEnv flatInitial [compileExp trace compMap (.app .eval exprs)]
    EvalResultRel genv sourceResult.2 flatResult.2 ∧ StateRel genv sourceResult.1 flatResult.1 := by
  have flatPositive : 0 < flatArguments.clock := by
    cases argumentsRel with
    | intro _ _ clock _ => simpa [← clock] using positive
  let flatStart := FlatSem.decClock { flatArguments with evalConfig := flatNextConfig }
  have bodyRun' : FlatSem.evaluateDecs
      { flatStart with globals := flatStart.globals ++ List.replicate (next.vidx - config.next.vidx) none }
        body = (flatLast, some flatError) := by simpa [flatStart, FlatSem.decClock] using bodyRun
  have flatDeclarations := evaluateIncCompileProg_error flatStart flatLast envId config decs n next
    newMap gen body flatError compiledBody bodyRun'
  rw [compiled] at flatDeclarations
  have flatResult := evaluate_compileEval_error flatEnv flatInitial flatArguments flatLast trace compMap exprs
    a b c d bytes words flatDecs flatNextConfig flatError flatRun flatDecoded flatPositive
    (by simpa [flatStart] using flatDeclarations)
  have sourceResult := evaluate_sourceEval_declaration_error sourceEnv evalEnv sourceInitial sourceArguments
    sourceLast exprs sourceValues decs begin sourceError sourceRun sourceDecoded positive sourceDeclarations
  dsimp only
  rw [sourceResult, flatResult]
  refine ⟨errorRel, ?_⟩
  cases lastRel with
  | intro nonempty refs clock ffi =>
    cases sourceError <;> exact .intro _ _ nonempty refs clock ffi

/-- With related operands and the callback invariant, a zero-clock Eval
times out in both evaluators after advancing their respective callback states.
The operand runs are the expression-list induction hypothesis. -/
theorem exprSim_eval_timeout {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (compMap : Environment)
    (trace : List VarN) (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState sourceArguments : SemanticPrimitivesHOL.State F) (flatState flatArguments : FlatSem.State C F)
    (exprs : List AstHOL.Exp) (sa sb sc sd sourceBytes sourceWords : Value)
    (a b c d bytes words : FlatSem.Value) (evalEnv : SemEnv Value) (decs : List Dec) (begin : Option EvalState)
    (sourceRun : EvaluateHOL.evaluate sourceState sourceEnv exprs.reverse =
      (sourceArguments, .val [sourceWords, sourceBytes, sd, sc, sb, sa]))
    (flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse =
      (flatArguments, .val [words, bytes, d, c, b, a]))
    (valuesRel : List.Forall₂ (ValueRel genv) [sa, sb, sc, sd, sourceBytes, sourceWords]
      [a, b, c, d, bytes, words])
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv idxs sourceArguments flatArguments)
    (decoded : SemanticPrimitivesHOL.doEval [sa, sb, sc, sd, sourceBytes, sourceWords]
      sourceArguments.evalState = some (evalEnv, decs, begin))
    (zero : sourceArguments.clock = 0) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .eval exprs) := by
  obtain ⟨_, _, _, _, flatDecs, _, _, _, _, flatDecoded, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    OracleInvariant.doEval_factoredInvariant_sourceShape interp transform sourceArguments flatArguments gen genv
      idxs invariant [sa, sb, sc, sd, sourceBytes, sourceWords] [a, b, c, d, bytes, words]
      valuesRel (evalEnv, decs, begin) decoded
  have flatDecoded' : FlatSem.doEval [bytes, words] flatArguments.evalConfig =
      some (flatDecs, { flatArguments.evalConfig with
        compileOracle := Flapjack.holShiftSeq 1 flatArguments.evalConfig.compileOracle }, FlatSem.unitValue) := by
    simpa using flatDecoded
  have states := invariant.2.2.1
  have flatZero : flatArguments.clock = 0 := by
    cases states with
    | intro _ _ clock _ => exact clock.symm.trans zero
  have sourceResult := evaluate_sourceEval_timeout sourceEnv evalEnv sourceState sourceArguments exprs
    [sa, sb, sc, sd, sourceBytes, sourceWords] decs begin (by simpa using sourceRun) decoded zero
  have flatResult := evaluate_compileEval_timeout flatEnv flatState flatArguments trace compMap exprs
    a b c d bytes words flatDecs
    { flatArguments.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flatArguments.evalConfig.compileOracle }
    flatRun flatDecoded' flatZero
  unfold ExprSim
  rw [sourceResult, flatResult]
  refine ⟨.abort .timeoutError, ?_⟩
  cases states with
  | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi

/-- The expression-list induction hypothesis determines the six flat
operands and their correspondence from six successful source operands. -/
theorem evalOperands_six_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (trace : List VarN) (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState sourceArguments : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (exprs : List AstHOL.Exp) (sa sb sc sd sourceBytes sourceWords : Value)
    (sourceRun : EvaluateHOL.evaluate sourceState sourceEnv exprs.reverse =
      (sourceArguments, .val [sourceWords, sourceBytes, sd, sc, sb, sa]))
    (operandSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState exprs.reverse) :
    ∃ flatArguments a b c d bytes words,
      FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse =
        (flatArguments, .val [words, bytes, d, c, b, a]) ∧
      List.Forall₂ (ValueRel genv) [sa, sb, sc, sd, sourceBytes, sourceWords] [a, b, c, d, bytes, words] ∧
      StateRel genv sourceArguments flatArguments := by
  unfold ExprListSim at operandSim
  rw [compileExps_reverse, sourceRun] at operandSim
  cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse with
  | mk flatArguments flatResult =>
    rw [flatRun] at operandSim
    obtain ⟨resultRel, states⟩ := operandSim
    cases resultRel with
    | value valuesRel =>
      cases valuesRel with
      | cons wordsRel rest =>
        cases rest with
        | cons bytesRel rest =>
          cases rest with
          | cons dRel rest =>
            cases rest with
            | cons cRel rest =>
              cases rest with
              | cons bRel rest =>
                cases rest with
                | cons aRel rest =>
                  cases rest with
                  | nil =>
                    exact ⟨_, _, _, _, _, _, _, rfl,
                      .cons aRel (.cons bRel (.cons cRel (.cons dRel (.cons bytesRel (.cons wordsRel .nil))))), states⟩

/-- The zero-clock Eval simulation directly consumes the expression-list
induction hypothesis; the callback invariant applies at the flat state that
that induction hypothesis produces. -/
theorem exprSim_eval_timeout_from_operands {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (compMap : Environment)
    (trace : List VarN) (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState sourceArguments : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (exprs : List AstHOL.Exp) (sa sb sc sd sourceBytes sourceWords : Value)
    (evalEnv : SemEnv Value) (decs : List Dec) (begin : Option EvalState)
    (sourceRun : EvaluateHOL.evaluate sourceState sourceEnv exprs.reverse =
      (sourceArguments, .val [sourceWords, sourceBytes, sd, sc, sb, sa]))
    (operandSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState exprs.reverse)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv idxs sourceArguments
      (FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse).1)
    (decoded : SemanticPrimitivesHOL.doEval [sa, sb, sc, sd, sourceBytes, sourceWords]
      sourceArguments.evalState = some (evalEnv, decs, begin))
    (zero : sourceArguments.clock = 0) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .eval exprs) := by
  obtain ⟨flatArguments, a, b, c, d, bytes, words, flatRun, valuesRel, _⟩ :=
    evalOperands_six_related genv compMap trace sourceEnv flatEnv sourceState sourceArguments flatState
      exprs sa sb sc sd sourceBytes sourceWords sourceRun operandSim
  have invariant' : OracleInvariant.factoredInvariant interp transform gen genv idxs sourceArguments flatArguments := by
    simpa [flatRun] using invariant
  exact exprSim_eval_timeout interp transform gen genv idxs compMap trace sourceEnv flatEnv
    sourceState sourceArguments flatState flatArguments exprs sa sb sc sd sourceBytes sourceWords
    a b c d bytes words evalEnv decs begin sourceRun flatRun valuesRel invariant' decoded zero

private theorem six_values {α : Type} (xs : List α) (length : xs.length = 6) :
    ∃ a b c d e f, xs = [a, b, c, d, e, f] := by
  cases xs with
  | nil => simp at length
  | cons a xs =>
    cases xs with
    | nil => simp at length
    | cons b xs =>
      cases xs with
      | nil => simp at length
      | cons c xs =>
        cases xs with
        | nil => simp at length
        | cons d xs =>
          cases xs with
          | nil => simp at length
          | cons e xs =>
            cases xs with
            | nil => simp at length
            | cons f xs =>
              cases xs with
              | nil => exact ⟨a, b, c, d, e, f, rfl⟩
              | cons _ _ => simp at length

/-- The successful callback and operand induction hypothesis determine the
operand shape for a zero-clock Eval; no fixed operand list is assumed. -/
theorem exprSim_eval_timeout_from_callback {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (compMap : Environment)
    (trace : List VarN) (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState sourceArguments : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (exprs : List AstHOL.Exp) (sourceValues : List Value)
    (evalEnv : SemEnv Value) (decs : List Dec) (begin : Option EvalState)
    (sourceRun : EvaluateHOL.evaluate sourceState sourceEnv exprs.reverse =
      (sourceArguments, .val sourceValues.reverse))
    (operandSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState exprs.reverse)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv idxs sourceArguments
      (FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse).1)
    (decoded : SemanticPrimitivesHOL.doEval sourceValues sourceArguments.evalState = some (evalEnv, decs, begin))
    (zero : sourceArguments.clock = 0) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .eval exprs) := by
  have operandSim' := operandSim
  unfold ExprListSim at operandSim'
  rw [compileExps_reverse, sourceRun] at operandSim'
  cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap exprs).reverse with
  | mk flatArguments flatResult =>
    rw [flatRun] at operandSim'
    obtain ⟨resultRel, _⟩ := operandSim'
    cases resultRel with
    | @value _ flatValues reversedRel =>
      have valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues.reverse := by
        simpa using List.forall₂_reverse_iff.mpr reversedRel
      have invariant' : OracleInvariant.factoredInvariant interp transform gen genv idxs sourceArguments flatArguments := by
        simpa [flatRun] using invariant
      obtain ⟨_, _, _, _, _, _, _, _, _, _, flatLength, _⟩ :=
        OracleInvariant.doEval_factoredInvariant_sourceShape interp transform sourceArguments flatArguments
          gen genv idxs invariant' sourceValues flatValues.reverse valuesRel (evalEnv, decs, begin) decoded
      have sourceLength : sourceValues.length = 6 := valuesRel.length_eq.trans flatLength
      obtain ⟨sa, sb, sc, sd, bytes, words, rfl⟩ := six_values sourceValues sourceLength
      exact exprSim_eval_timeout_from_operands interp transform gen genv idxs compMap trace sourceEnv flatEnv
        sourceState sourceArguments flatState exprs sa sb sc sd bytes words evalEnv decs begin
        (by simpa using sourceRun) operandSim (by simpa [flatRun] using invariant) decoded zero

/-- Compose the successful declaration induction hypothesis with the whole
generated Eval expression and the stored environment ID. The factored
invariant and value relation still require HOL correspondence review. -/
theorem evaluate_compileEval_declare_success {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (envId : Nat × Nat) (config nextConfig : Config) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (before : Option EvalState) (source : SemanticPrimitivesHOL.State F)
    (flatEnv : FlatSem.Environment FlatSem.Value) (flatInitial flatArguments flatMiddle : FlatSem.State C F)
    (oldGenv newGenv : GlobalEnv) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (sourceEnv sourceNew : SemEnv Value) (value : Value) (after : Option EvalState)
    (n : Nat) (next : NextIndices) (newMap : Environment) (gen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp) (trace : List VarN) (compMap : Environment) (exprs : List AstHOL.Exp)
    (a b c d bytes words : FlatSem.Value) (flatNextConfig : FlatSem.InstallConfig C)
    (operandRun : FlatSem.evaluate flatEnv flatInitial (compileExps trace compMap exprs).reverse =
      (flatArguments, .val [words, bytes, d, c, b, a]))
    (decoded : FlatSem.doEval [bytes, words] flatArguments.evalConfig =
      some (flatDecs, flatNextConfig, FlatSem.unitValue))
    (positive : 0 < flatArguments.clock)
    (compiled : incCompileProg envId config decs = (nextConfig, flatDecs))
    (compiledBody : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, newMap, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { FlatSem.decClock { flatArguments with evalConfig := flatNextConfig } with
        globals := flatArguments.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (flatMiddle, none))
    (nextCfg : OracleInvariant.srcOracNextCfg interp before = some nextConfig)
    (forward : OracleInvariant.oracForwardRel interp before source.evalState)
    (growth : GlobalGrowth oldGenv newGenv)
    (baseInv : GlobalEnvInv oldGenv (lookupEnvId envId config.envs) (fun _ => False) sourceEnv)
    (newDomain : EnvDomainEq newMap sourceNew)
    (newInv : GlobalEnvInv newGenv newMap (fun _ => False) sourceNew)
    (invariant : OracleInvariant.factoredInvariant interp transform gen newGenv idxs source flatMiddle)
    (generation : OracleInvariant.envGenRel gen source.evalState)
    (declared : declareEnv source.evalState (extendDecEnv sourceNew sourceEnv) = some (value, after)) :
    ∃ stored : FlatSem.Value,
      FlatSem.evaluate flatEnv flatInitial [compileExp trace compMap (.app .eval exprs)] =
        ({ flatMiddle with refs := .refv stored :: flatMiddle.refs.tail }, .val [stored]) ∧
      OracleInvariant.factoredInvariant interp transform { gen with next := gen.next + 1 } newGenv idxs
        { source with evalState := after } { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail } ∧
      ValueRel newGenv value stored ∧ OracleInvariant.oracForwardRel interp source.evalState after ∧
      OracleInvariant.envGenRel { gen with next := gen.next + 1 } after := by
  let flatStart := FlatSem.decClock { flatArguments with evalConfig := flatNextConfig }
  have bodyRun' : FlatSem.evaluateDecs
      { flatStart with globals := flatStart.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (flatMiddle, none) := by simpa [flatStart, FlatSem.decClock] using bodyRun
  obtain ⟨stored, declarationRun, nextInvariant, related, nextForward, nextGeneration⟩ :=
    evalDeclare_incremental_success interp transform envId config nextConfig decs flatDecs before source
      flatStart flatMiddle oldGenv newGenv idxs sourceEnv sourceNew value after n next newMap gen body
      compiled compiledBody bodyRun' nextCfg forward growth baseInv newDomain newInv invariant generation declared
  let last := { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail }
  have reserved := nextInvariant.2.2.2.2.2.2.2.1
  obtain ⟨globalsTail, oldValue, refsTail, globalEq, refsEq⟩ :=
    OracleInvariant.evalRefInv_heads last reserved
  have globals : last.globals[0]? = some (some (.loc true 0)) := by simp [globalEq]
  have refs : last.refs[0]? = some (.refv stored) := by simp [last]
  refine ⟨stored, ?_, nextInvariant, related, nextForward, nextGeneration⟩
  exact evaluate_compileEval_success flatEnv flatInitial flatArguments last trace compMap exprs
    a b c d bytes words stored flatDecs flatNextConfig operandRun decoded positive
    (by simpa [flatStart, last] using declarationRun) globals refs

/-- Successful Eval simulation through the declaration induction hypothesis,
including restoration of the caller's oracle invariant and generation. The
factored relations have not yet been reviewed as the original HOL invariant. -/
theorem evaluate_eval_declare_and_restore {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (oldGen : EnvironmentGenerationStore) (oldGenv baseGenv newGenv : GlobalEnv)
    (start finish innerStart innerFinish : NextIndices) (other : Set (Nat × IndexKind))
    (envId : Nat × Nat) (config nextConfig : Config) (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (sourceEnv evalEnv newEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceInitial sourceArguments sourceLast : SemanticPrimitivesHOL.State F)
    (flatInitial flatArguments flatMiddle : FlatSem.State C F)
    (begin after : Option EvalState) (value : Value) (exprs : List AstHOL.Exp)
    (sourceValues : List Value) (a b c d bytes words : FlatSem.Value)
    (flatNextConfig : FlatSem.InstallConfig C) (trace : List VarN) (compMap : Environment)
    (n : Nat) (next : NextIndices) (newMap : Environment) (gen : EnvironmentGenerationStore)
    (body : List FlatLang.Exp)
    (sourceRun : EvaluateHOL.evaluate sourceInitial sourceEnv exprs.reverse =
      (sourceArguments, .val sourceValues.reverse))
    (sourceDecoded : SemanticPrimitivesHOL.doEval sourceValues sourceArguments.evalState =
      some (evalEnv, decs, begin))
    (sourcePositive : 0 < sourceArguments.clock)
    (sourceDeclarations : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { sourceArguments with evalState := begin }) evalEnv decs = (sourceLast, .val newEnv))
    (flatRun : FlatSem.evaluate flatEnv flatInitial (compileExps trace compMap exprs).reverse =
      (flatArguments, .val [words, bytes, d, c, b, a]))
    (flatDecoded : FlatSem.doEval [bytes, words] flatArguments.evalConfig =
      some (flatDecs, flatNextConfig, FlatSem.unitValue))
    (flatPositive : 0 < flatArguments.clock)
    (compiled : incCompileProg envId config decs = (nextConfig, flatDecs))
    (compiledBody : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, newMap, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { FlatSem.decClock { flatArguments with evalConfig := flatNextConfig } with
        globals := flatArguments.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (flatMiddle, none))
    (nextCfg : OracleInvariant.srcOracNextCfg interp begin = some nextConfig)
    (forward : OracleInvariant.oracForwardRel interp begin sourceLast.evalState)
    (growth : GlobalGrowth baseGenv newGenv)
    (baseInv : GlobalEnvInv baseGenv (lookupEnvId envId config.envs) (fun _ => False) evalEnv)
    (newDomain : EnvDomainEq newMap newEnv)
    (newInv : GlobalEnvInv newGenv newMap (fun _ => False) newEnv)
    (invariant : OracleInvariant.factoredInvariant interp transform gen newGenv
      (innerStart, innerFinish, idxBlock start finish ∪ other) sourceLast flatMiddle)
    (generation : OracleInvariant.envGenRel gen sourceLast.evalState)
    (declared : declareEnv sourceLast.evalState (extendDecEnv newEnv evalEnv) = some (value, after))
    (previousInv : OracleInvariant.factoredInvariant interp transform oldGen oldGenv
      (start, finish, other) sourceArguments flatArguments)
    (indices : idxPrev finish innerFinish)
    (initialForward : OracleInvariant.oracConfigEnvsSubspt interp sourceArguments.evalState begin)
    (beginShape : match sourceArguments.evalState with
      | some (.evalOracle prior) => ∃ beginState, begin = some (.evalOracle beginState) ∧
          beginState.envs = (addEnvGeneration prior).envs ∧
          beginState.generation = (addEnvGeneration prior).generation
      | _ => False) :
    ∃ stored : FlatSem.Value,
      EvaluateHOL.evaluate sourceInitial sourceEnv [.app .eval exprs] =
        ({ sourceLast with evalState := resetEnvGeneration sourceArguments.evalState after }, .val [value]) ∧
      FlatSem.evaluate flatEnv flatInitial [compileExp trace compMap (.app .eval exprs)] =
        ({ flatMiddle with refs := .refv stored :: flatMiddle.refs.tail }, .val [stored]) ∧
      ValueRel newGenv value stored ∧
      EvalResultRel newGenv (.val [value]) (.val [stored]) ∧
      StateRel newGenv { sourceLast with evalState := resetEnvGeneration sourceArguments.evalState after }
        { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail } ∧
      OracleInvariant.factoredInvariant interp transform oldGen newGenv (start, finish, other)
        { sourceLast with evalState := resetEnvGeneration sourceArguments.evalState after }
        { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail } ∧
      OracleInvariant.oracForwardRel interp sourceArguments.evalState
        (resetEnvGeneration sourceArguments.evalState after) := by
  obtain ⟨stored, flatResult, nextInvariant, related, nextForward, _⟩ :=
    evaluate_compileEval_declare_success interp transform envId config nextConfig decs flatDecs begin sourceLast
      flatEnv flatInitial flatArguments flatMiddle baseGenv newGenv
      (innerStart, innerFinish, idxBlock start finish ∪ other) evalEnv newEnv value after
      n next newMap gen body trace compMap exprs a b c d bytes words flatNextConfig flatRun flatDecoded
      flatPositive compiled compiledBody bodyRun nextCfg forward growth baseInv newDomain newInv invariant
      generation declared
  have fullForward := OracleInvariant.oracForwardRel_trans interp begin sourceLast.evalState after
    ⟨forward, nextForward⟩
  have restored := OracleInvariant.factoredInvariant_endEval_sourceShape interp transform oldGen
    { gen with next := gen.next + 1 } oldGenv newGenv start finish innerStart innerFinish other
    sourceArguments { sourceLast with evalState := after } flatArguments
    { flatMiddle with refs := .refv stored :: flatMiddle.refs.tail } begin
    nextInvariant previousInv (by simpa using fullForward) indices initialForward beginShape
  refine ⟨stored, ?_, flatResult, related, .value (.cons related .nil), ?_, ?_, ?_⟩
  · exact evaluate_sourceEval_success sourceEnv evalEnv newEnv sourceInitial sourceArguments sourceLast
      exprs sourceValues decs begin after value sourceRun sourceDecoded sourcePositive sourceDeclarations declared
  · simpa using restored.1.2.2.1
  · simpa using restored.1
  · simpa using restored.2.1

/-- At clock zero, dynamic evaluation either propagates an operand error or
reaches the corresponding timeout after decoding. This establishes the Eval
base case of the bounded local simulation without a declaration hypothesis. -/
theorem localEnvBounded_eval_zero {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (exprs : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ exprs → LocalEnvBoundedIH (F := F) interp transform 0 expr) :
    LocalEnvBoundedIH (F := F) interp transform 0 (.app .eval exprs) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := NamespaceHOL.nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv exprs.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .eval exprs] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv exprs.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform 0 exprs.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat
    baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv exprs.reverse = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap exprs).reverse = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · exact exprSim_eval_operand_error nextGenv compMap trace sourceEnv flatEnv source flat exprs nextSource _ sourceRun argsSimCopy
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv exprs.reverse []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · exact exprSim_eval_operand_error nextGenv compMap trace sourceEnv flatEnv source flat exprs nextSource _ sourceRun argsSimCopy
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv exprs.reverse []).1, sourceRun]
      rw [evaluate_compileEval_operand_error flatEnv flat nextFlat trace compMap exprs _ flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    have nextZero : nextSource.clock = 0 := by
      have bound := EvaluateHOL.evaluateClockFull source nextSource sourceEnv exprs.reverse _ sourceRun
      omega
    cases decoded : SemanticPrimitivesHOL.doEval sourceValues.reverse nextSource.evalState with
    | none =>
      exfalso
      apply safe nextSource
      change EvaluateHOL.evaluate source sourceEnv [.app .eval exprs] = _
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv exprs.reverse []).1, sourceRun]
      cases nextSource
      simp [getOpClass, EvaluateHOL.fixClock, EvaluateHOL.doEvalRes, decoded]
    | some decodedValue =>
      obtain ⟨evalEnv, decs, begin⟩ := decodedValue
      refine ⟨nextGenv, ?_, ?_⟩
      · apply exprSim_eval_timeout_from_callback interp transform gen nextGenv (start, finish, other)
          compMap trace sourceEnv flatEnv source nextSource flat exprs sourceValues.reverse evalEnv decs begin
        · simpa using sourceRun
        · exact argsSimCopy
        · simpa [flatRun] using nextInvariant
        · exact decoded
        · exact nextZero
      · have sourceTimeout := evaluate_sourceEval_timeout sourceEnv evalEnv source nextSource exprs
          sourceValues.reverse decs begin (by simpa using sourceRun) decoded nextZero
        rw [sourceTimeout]
        trivial

end Flapjack.Compiler.Backend.SourceToFlat
