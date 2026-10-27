import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordLists

/-! Source-to-flat Eval callback simulation over the factored value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Advancing both compiler oracles preserves their pointwise relationship.
Environment generation changes do not affect this relationship. -/
theorem oracRel_advance {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat) :
    oracRel (some decode) transform
      (some (.evalOracle (addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle })))
      { flat with compileOracle := Flapjack.holShiftSeq 1 flat.compileOracle } := by
  obtain ⟨compiler, callback, inner⟩ := related
  refine ⟨compiler, callback, ?_⟩
  intro k envId stateValue decs entry
  simpa [oracRelInner, addEnvGeneration, Flapjack.holShiftSeq] using
    inner (k + 1) envId stateValue decs (by simpa [addEnvGeneration, Flapjack.holShiftSeq] using entry)

/-- The source oracle's decoding and incremental compilation conditions also
survive an Eval step. -/
theorem srcOracStepInvs_advance {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state))) :
    srcOracStepInvs (some decode) transform
      (some (.evalOracle (addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }))) := by
  simp only [srcOracStepInvs] at steps ⊢
  constructor
  · intro k envId stateValue decs entry
    exact steps.1 (k + 1) envId stateValue decs (by simpa [addEnvGeneration, Flapjack.holShiftSeq] using entry)
  · intro k envId stateValue decs entry
    have next := steps.2 (k + 1) envId stateValue decs
      (by simpa [addEnvGeneration, Flapjack.holShiftSeq] using entry)
    simpa [addEnvGeneration, Flapjack.holShiftSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- Starting a fresh Eval generation creates an empty source environment and
therefore satisfies the generation relation for an empty compiler store. -/
theorem envGenRel_advance (state : EvalOracleState) (oracle : EvalOracleFun) :
    let next := addEnvGeneration { state with oracle := oracle }
    srcOracGenInv (some (.evalOracle next)) ∧
      envGenRel ⟨0, state.envs.length, .ln⟩ (some (.evalOracle next)) := by
  simp [srcOracGenInv, envGenRel, addEnvGeneration]

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

/-- Successful source and flat Eval callbacks advance to related oracles and
preserve the source oracle's incremental-step invariant. This establishes the
oracle portion of the postcondition, separately from the remaining global and
environment invariants of the full simulation. -/
theorem doEval_oracle_preserves_oracles {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    let nextState := addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }
    let nextFlat := { flat with compileOracle := Flapjack.holShiftSeq 1 flat.compileOracle }
    output.2.2 = some (.evalOracle nextState) ∧
      srcOracStepInvs (some decode) transform output.2.2 ∧
      oracRel (some decode) transform output.2.2 nextFlat ∧
      srcOracGenInv output.2.2 ∧
      envGenRel ⟨0, state.envs.length, .ln⟩ output.2.2 := by
  have related' := related
  obtain ⟨compiler, callback, _⟩ := related'
  cases called : state.customDoEval [first, second, third, fourth, bytesValue, wordsValue] state.oracle with
  | none => simp [SemanticPrimitivesHOL.doEval, called] at success
  | some result =>
    have compilerSuccess : SourceEval.Proofs.doEvalOracle compiler transform
        [first, second, third, fourth, bytesValue, wordsValue] state.oracle = some result := by
      simpa [callback] using called
    cases entry : state.oracle 0 with
    | mk envId tail =>
      cases tail with
      | mk stateValue decs =>
        obtain ⟨_, _, _, _, _, _, _, resultEq⟩ :=
          SourceEval.Proofs.doEvalOracle_six_inv compiler transform state.oracle first second third fourth
            bytesValue wordsValue envId stateValue decs result entry compilerSuccess
        rw [resultEq] at called
        cases found : lookupEnv state envId with
        | none => simp [SemanticPrimitivesHOL.doEval, called, found] at success
        | some env =>
          simp [SemanticPrimitivesHOL.doEval, called, found] at success
          subst output
          exact ⟨rfl, srcOracStepInvs_advance decode transform state steps,
            oracRel_advance decode transform state flat related,
            (envGenRel_advance state (Flapjack.holShiftSeq 1 state.oracle)).1,
            (envGenRel_advance state (Flapjack.holShiftSeq 1 state.oracle)).2⟩

/-- The compiler configuration selected by a successful source Eval retains
the previous environment-generation map. This isolates the corresponding
postcondition of the full source-to-flat Eval simulation. -/
theorem doEval_oracle_envStoreAdvance {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C) (genv : GlobalEnv)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (envs : srcOracEnvInvs (some decode) genv (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ current next,
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some current ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      current.envs.next = state.envs.length ∧ envStoreInv next.envs ∧
      Flapjack.sptSubspt current.envs.envGens next.envs.envGens ∧
      envGenRel ⟨0, current.envs.next, .ln⟩ output.2.2 := by
  obtain ⟨post, _, _, _, nextGenRel⟩ :=
    doEval_oracle_preserves_oracles decode transform state flat steps related
      first second third fourth bytesValue wordsValue output success
  obtain ⟨current, next, currentCfg, nextCfg, length, _, valid, submap⟩ :=
    sourceOracle_envStoreAdvance decode transform genv state steps envs
  refine ⟨current, next, currentCfg, ?_, length, valid, submap, ?_⟩
  · simpa [post] using nextCfg
  · simpa [length] using nextGenRel

/-- Successful Eval preserves the combined source oracle invariants, including
the stored environments, when the global environment grows. The relation is
the factored source-to-flat relation, not the full reviewed HOL invariant. -/
theorem doEval_oracle_preserves_sourceInvs {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (invs : srcOracInvs (some decode) transform old (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    srcOracInvs (some decode) transform new output.2.2 ∧
      oracRel (some decode) transform output.2.2
        { flat with compileOracle := Flapjack.holShiftSeq 1 flat.compileOracle } := by
  obtain ⟨post, nextSteps, nextRelated, nextGen, _⟩ :=
    doEval_oracle_preserves_oracles decode transform state flat invs.1 related
      first second third fourth bytesValue wordsValue output success
  have nextEnvs := srcOracEnvInvs_advance decode transform old state invs.1 invs.2.1
  rw [post]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [post] using nextSteps
  · exact srcOracEnvInvs_growth (some decode) old new growth _ nextEnvs
  · simpa [post] using nextGen
  · simpa [post] using nextRelated

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
          FlatSem.unitValue) ∧
      srcOracStepInvs (some decode) transform output.2.2 ∧
      oracRel (some decode) transform output.2.2
        { flatConfig with compileOracle := Flapjack.holShiftSeq 1 flatConfig.compileOracle } ∧
      srcOracGenInv output.2.2 ∧
      envGenRel ⟨0, state.envs.length, .ln⟩ output.2.2 := by
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
                obtain ⟨_, nextSteps, nextRelated, nextGenInv, nextGenRel⟩ :=
                  doEval_oracle_preserves_oracles decode transform state flatConfig steps oracleRel
                    a b c d bytes words output sourceSuccess
                exact ⟨envId, stateValue, decs, config, payload, flatDecs,
                  entry, decoded, sourceDecls, flatEq, rfl, flatSuccess, nextSteps, nextRelated,
                  nextGenInv, nextGenRel⟩

/-- Related Eval arguments and the combined source oracle invariant yield a
successful flat callback and preserve the combined oracle invariant under
global growth. Full source-to-flat evaluator and allocation invariants remain
separate obligations. -/
theorem doEval_oracle_related_invs {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (invs : srcOracInvs (some decode) transform old (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (constructors : genvCOk old.c) (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel old) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues (some (.evalOracle state)) = some output) :
    ∃ envId stateValue decs config payload flatDecs,
      state.oracle 0 = (envId, stateValue, decs) ∧
      decode stateValue = some (config, payload) ∧ output.2.1 = transform decs ∧
      flatDecs = (incCompileProg envId config (transform decs)).2 ∧ flatValues.length = 6 ∧
      FlatSem.doEval (flatValues.drop 4) flat =
        some (flatDecs, { flat with compileOracle := Flapjack.holShiftSeq 1 flat.compileOracle },
          FlatSem.unitValue) ∧
      srcOracInvs (some decode) transform new output.2.2 ∧
      oracRel (some decode) transform output.2.2
        { flat with compileOracle := Flapjack.holShiftSeq 1 flat.compileOracle } := by
  obtain ⟨envId, stateValue, decs, config, payload, flatDecs, entry, decoded, sourceDecls,
    flatEq, flatLength, flatSuccess, _, _, _, _⟩ :=
    doEval_oracle_related decode transform state flat invs.1 related old constructors
      sourceValues flatValues valuesRel output success
  have sourceLength : sourceValues.length = 6 := valuesRel.length_eq.trans flatLength
  obtain ⟨a, b, c, d, bytes, words, rfl⟩ := list_length_six sourceValues sourceLength
  obtain ⟨nextInvs, nextRelated⟩ :=
    doEval_oracle_preserves_sourceInvs decode transform state flat old new growth invs related
      a b c d bytes words output success
  exact ⟨envId, stateValue, decs, config, payload, flatDecs, entry, decoded, sourceDecls,
    flatEq, flatLength, flatSuccess, nextInvs, nextRelated⟩

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
