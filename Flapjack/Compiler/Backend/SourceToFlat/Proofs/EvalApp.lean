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
  have bodyRun := evaluate_evalBody_success env arguments last bytes words stored decs nextConfig
    decoded positive declarationRun globals references
  change FlatSem.evaluate env state [.mat .none (.con .none none (compileExps trace compMap exprs))
    [(pattern, body)]] = (last, .val [stored])
  rw [FlatSem.evaluate, tupleRun, fixed]
  simp (config := { zeta := false })
  have selection' := selection
  dsimp only [body] at selection'
  rw [selection']
  simpa [body] using bodyRun

end Flapjack.Compiler.Backend.SourceToFlat
