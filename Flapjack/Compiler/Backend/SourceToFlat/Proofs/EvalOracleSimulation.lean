import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordLists

/-! Source-to-flat Eval callback simulation over the factored value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful source Eval callback has a corresponding flat Eval callback.
This is factored infrastructure: the value relation and surrounding evaluator
state invariant have not yet been reviewed as the full HOL theorem. -/
theorem doEvalOracle_flatCallback {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (compiler : CompilerFun) (state : EvalOracleState) (flatConfig : FlatSem.InstallConfig C)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (oracleRel : oracRelInner decode state compiler transform flatConfig)
    (genv : GlobalEnv) (constructors : genvCOk genv.c)
    (first second third fourth bytesValue wordsValue : Value)
    (flatBytes flatWords : FlatSem.Value)
    (bytesRel : ValueRel genv bytesValue flatBytes) (wordsRel : ValueRel genv wordsValue flatWords)
    (sourceResult : (Nat × Nat) × EvalOracleFun × List Dec)
    (sourceSuccess : SourceEval.Proofs.doEvalOracle compiler transform
      [first, second, third, fourth, bytesValue, wordsValue] state.oracle = some sourceResult) :
    ∃ envId stateValue decs config payload flatDecs,
      state.oracle 0 = (envId, stateValue, decs) ∧
      decode stateValue = some (config, payload) ∧
      sourceResult = (envId, Flapjack.holShiftSeq 1 state.oracle, transform decs) ∧
      flatDecs = (incCompileProg envId config (transform decs)).2 ∧
      FlatSem.doEval [flatBytes, flatWords] flatConfig =
        some (flatDecs, { flatConfig with compileOracle := Flapjack.holShiftSeq 1 flatConfig.compileOracle },
          FlatSem.unitValue) := by
  simp only [srcOracStepInvs] at steps
  cases entry : state.oracle 0 with
  | mk envId rest =>
    cases rest with
    | mk stateValue decs =>
      obtain ⟨nextValue, bytes, words, compiled, decodedBytes, decodedWords, nextValueEq, resultEq⟩ :=
        SourceEval.Proofs.doEvalOracle_six_inv compiler transform state.oracle first second third fourth
          bytesValue wordsValue envId stateValue decs sourceResult entry sourceSuccess
      obtain ⟨config, payload, decoded⟩ := steps.1 0 envId stateValue decs entry
      obtain ⟨nextFlat, flatOracle, flatCompiled, nextRel⟩ :=
        oracRelInner_first decode state compiler transform flatConfig oracleRel envId stateValue nextValue
          decs config payload bytes words entry decoded compiled
      have flatBytesDecoded := valueToWord8List_related genv constructors bytesValue flatBytes bytes decodedBytes bytesRel
      have flatWordsDecoded := valueToWord64List_related genv constructors wordsValue flatWords words decodedWords wordsRel
      cases nextEntry : state.oracle 1 with
      | mk nextId nextRest =>
        cases nextRest with
        | mk nextState nextDecs =>
          have sameState : nextValue = nextState := by simpa [nextEntry] using nextValueEq
          obtain ⟨nextConfig, nextPayload, nextDecoded⟩ := steps.1 1 nextId nextState nextDecs nextEntry
          have nextDecoded' : decode nextValue = some (nextConfig, nextPayload) := by simpa [sameState] using nextDecoded
          have samePayload : nextPayload = nextFlat := nextRel (nextConfig, nextPayload) nextDecoded'
          have nextOracle := oracleRel 1 nextId nextState nextDecs nextEntry
          simp only [nextDecoded, Flapjack.holThe] at nextOracle
          have flatNext : (Flapjack.holShiftSeq 1 flatConfig.compileOracle 0).1 = nextFlat := by
            simp [Flapjack.holShiftSeq, nextOracle.1, samePayload]
          have nonempty : (incCompileProg envId config (transform decs)).2 ≠ [] := by
            apply incCompileProg_nonempty envId config (incCompileProg envId config (transform decs)).1
              (transform decs)
            exact Prod.eta _ |>.symm
          refine ⟨envId, stateValue, decs, config, payload,
            (incCompileProg envId config (transform decs)).2, rfl, decoded, resultEq, rfl, ?_⟩
          simp [FlatSem.doEval, flatBytesDecoded, flatWordsDecoded, flatOracle, flatCompiled, nonempty, flatNext]

/-- A successful source `doEval` in oracle mode yields a successful flat
`doEval` on the corresponding byte and word arguments. The source and flat
evaluator state simulation is still a separate obligation. -/
theorem doEval_oracle_flatCallback {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flatConfig : FlatSem.InstallConfig C)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (oracleRel : oracRel (some decode) transform (some (.evalOracle state)) flatConfig)
    (genv : GlobalEnv) (constructors : genvCOk genv.c)
    (first second third fourth bytesValue wordsValue : Value)
    (flatBytes flatWords : FlatSem.Value)
    (bytesRel : ValueRel genv bytesValue flatBytes) (wordsRel : ValueRel genv wordsValue flatWords)
    (output : SemEnv Value × List Dec × Option EvalState)
    (sourceSuccess : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ envId stateValue decs config payload flatDecs,
      state.oracle 0 = (envId, stateValue, decs) ∧
      decode stateValue = some (config, payload) ∧ output.2.1 = transform decs ∧
      flatDecs = (incCompileProg envId config (transform decs)).2 ∧
      FlatSem.doEval [flatBytes, flatWords] flatConfig =
        some (flatDecs, { flatConfig with compileOracle := Flapjack.holShiftSeq 1 flatConfig.compileOracle },
          FlatSem.unitValue) := by
  obtain ⟨compiler, callback, inner⟩ := oracleRel
  cases called : state.customDoEval [first, second, third, fourth, bytesValue, wordsValue] state.oracle with
  | none => simp [SemanticPrimitivesHOL.doEval, called] at sourceSuccess
  | some result =>
    have success : SourceEval.Proofs.doEvalOracle compiler transform
        [first, second, third, fourth, bytesValue, wordsValue] state.oracle = some result := by
      simpa [callback] using called
    obtain ⟨envId, stateValue, decs, config, payload, flatDecs,
      entry, decoded, resultEq, flatEq, flatSuccess⟩ :=
      doEvalOracle_flatCallback decode transform compiler state flatConfig steps inner genv constructors
        first second third fourth bytesValue wordsValue flatBytes flatWords bytesRel wordsRel result success
    rw [resultEq] at called
    have sourceDecls : output.2.1 = transform decs := by
      cases found : lookupEnv state envId with
      | none => simp [SemanticPrimitivesHOL.doEval, called, found] at sourceSuccess
      | some env =>
        simp [SemanticPrimitivesHOL.doEval, called, found] at sourceSuccess
        rw [← sourceSuccess]
    exact ⟨envId, stateValue, decs, config, payload, flatDecs,
      entry, decoded, sourceDecls, flatEq, flatSuccess⟩

private theorem list_length_six {α : Type} (xs : List α) (length : xs.length = 6) :
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

/-- A successful oracle-mode source Eval on related arguments yields a
successful flat Eval on the last two arguments, with the same source oracle
entry and corresponding incremental compilation result. The later declaration
evaluation and full source-to-flat state invariant are separate obligations. -/
theorem doEval_oracle_related {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flatConfig : FlatSem.InstallConfig C)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (oracleRel : oracRel (some decode) transform (some (.evalOracle state)) flatConfig)
    (genv : GlobalEnv) (constructors : genvCOk genv.c)
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (sourceSuccess : SemanticPrimitivesHOL.doEval sourceValues (some (.evalOracle state)) = some output) :
    ∃ envId stateValue decs config payload flatDecs,
      state.oracle 0 = (envId, stateValue, decs) ∧
      decode stateValue = some (config, payload) ∧ output.2.1 = transform decs ∧
      flatDecs = (incCompileProg envId config (transform decs)).2 ∧ flatValues.length = 6 ∧
      FlatSem.doEval (flatValues.drop 4) flatConfig =
        some (flatDecs, { flatConfig with compileOracle := Flapjack.holShiftSeq 1 flatConfig.compileOracle },
          FlatSem.unitValue) := by
  have oracleRelCopy := oracleRel
  obtain ⟨compiler, callback, _⟩ := oracleRelCopy
  cases called : state.customDoEval sourceValues state.oracle with
  | none => simp [SemanticPrimitivesHOL.doEval, called] at sourceSuccess
  | some result =>
    have success : SourceEval.Proofs.doEvalOracle compiler transform sourceValues state.oracle = some result := by
      simpa [callback] using called
    have length := SourceEval.Proofs.doEvalOracle_success_length compiler transform sourceValues state.oracle result success
    obtain ⟨a, b, c, d, bytes, words, rfl⟩ := list_length_six sourceValues length
    cases valuesRel with
    | cons _ tail1 =>
      cases tail1 with
      | cons _ tail2 =>
        cases tail2 with
        | cons _ tail3 =>
          cases tail3 with
          | cons _ tail4 =>
            cases tail4 with
            | cons bytesRel tail5 =>
              cases tail5 with
              | cons wordsRel tail6 =>
                cases tail6
                obtain ⟨envId, stateValue, decs, config, payload, flatDecs,
                  entry, decoded, sourceDecls, flatEq, flatSuccess⟩ :=
                  doEval_oracle_flatCallback decode transform state flatConfig steps oracleRel genv constructors
                    a b c d bytes words _ _ bytesRel wordsRel output sourceSuccess
                exact ⟨envId, stateValue, decs, config, payload, flatDecs,
                  entry, decoded, sourceDecls, flatEq, rfl, flatSuccess⟩

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
