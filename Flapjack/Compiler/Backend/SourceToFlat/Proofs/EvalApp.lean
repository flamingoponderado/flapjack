import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EnvironmentDomain
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalPattern
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

end Flapjack.Compiler.Backend.SourceToFlat
