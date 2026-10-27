import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordLists
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalPattern
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreEnvId

/-! Source-to-flat Eval callback simulation over the factored value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Factored source-to-flat invariant for the proof-side evaluator. Its value,
state, and global-environment relations still require HOL correspondence
review, so this is not tagged as the original `invariant` definition. -/
noncomputable def factoredInvariant {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) : Prop :=
  genvCOk genv.c ∧ genvCTysOk genv.c genv.tys ∧ StateRel genv source flat ∧
  idxRangeRel interp genv source.nextTypeStamp source.nextExnStamp source.evalState idxs ∧
  srcOracInvs interp transform genv source.evalState ∧
  oracRel interp transform source.evalState flat.evalConfig ∧ genv.v = flat.globals ∧
  evalRefInv (flat.globals.take 1) (flat.refs.take 1) ∧ envGenInv gen ∧
  finIdxMatch flat.globals.length idxs.2.1 (srcOracNextCfg interp source.evalState)

/-- Replacing the reserved first reference preserves the factored simulation
invariant. The relations underlying it still require HOL correspondence
review, so this is not tagged as the original invariant theorem. -/
theorem factoredInvariant_changeEvalRef {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (value : FlatSem.Value)
    (valid : factoredInvariant interp transform gen genv idxs source flat) :
    factoredInvariant interp transform gen genv idxs source
      { flat with refs := .refv value :: flat.refs.tail } := by
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := valid
  have newStates : StateRel genv source { flat with refs := .refv value :: flat.refs.tail } := by
    cases states with
    | intro nonempty refs clock ffi => exact .intro _ _ (by simp) (by simpa using refs) clock ffi
  have newReserved : evalRefInv (flat.globals.take 1) ((.refv value :: flat.refs.tail).take 1) := by
    exact ⟨reserved.1, ⟨value, by simp⟩⟩
  exact ⟨cOk, tysOk, newStates, range, invs, orac, globals, newReserved, genInv, fin⟩

/-- Returning from an Eval call restores the caller's generation relation:
the call relation preserves every generation that preceded the fresh one. -/
theorem envGenRel_resetAfterEval (gen : EnvironmentGenerationStore)
    (prior begin : EvalOracleState) (after : Option EvalState)
    (priorRel : envGenRel gen (some (.evalOracle prior)))
    (beginEnvs : begin.envs = (addEnvGeneration prior).envs)
    (beginGeneration : begin.generation = (addEnvGeneration prior).generation)
    (called : evalStateCallRel (some (.evalOracle begin)) after) :
    envGenRel gen (resetEnvGeneration (some (.evalOracle prior)) after) := by
  obtain ⟨last, rfl, _, length, earlier⟩ := called
  have priorBound : prior.generation < prior.envs.length := priorRel.2.1
  have beforeFresh : prior.generation < begin.generation := by
    simpa [addEnvGeneration, beginGeneration] using priorBound
  have beginBound : prior.generation < begin.envs.length := by
    simp [beginEnvs, addEnvGeneration]
    omega
  have lastBound : prior.generation < last.envs.length := by omega
  have same := earlier prior.generation beforeFresh
  rw [Flapjack.holEl_eq_getElem _ _ lastBound, Flapjack.holEl_eq_getElem _ _ beginBound] at same
  have beginEntry : begin.envs[prior.generation] = prior.envs[prior.generation] := by
    simp [beginEnvs, addEnvGeneration, List.getElem_append_left, priorBound]
  have sameLookup : last.envs[prior.generation]? = prior.envs[prior.generation]? := by
    simp [lastBound, priorBound, same, beginEntry]
  change gen.generation = prior.generation ∧ prior.generation < last.envs.length ∧
    gen.next = (last.envs[prior.generation]?.getD []).length
  exact ⟨priorRel.1, lastBound, by rw [sameLookup]; exact priorRel.2.2⟩

/-- Resetting to the caller's generation preserves its earlier environments
after a call that started from a freshly appended generation. -/
theorem evalStateCallRel_resetAfterEval (prior begin : EvalOracleState) (after : Option EvalState)
    (priorBound : prior.generation < prior.envs.length)
    (beginEnvs : begin.envs = (addEnvGeneration prior).envs)
    (beginGeneration : begin.generation = (addEnvGeneration prior).generation)
    (called : evalStateCallRel (some (.evalOracle begin)) after) :
    evalStateCallRel (some (.evalOracle prior))
      (resetEnvGeneration (some (.evalOracle prior)) after) := by
  obtain ⟨last, rfl, _, length, earlier⟩ := called
  refine ⟨{ last with generation := prior.generation }, rfl, rfl, ?_, ?_⟩
  · simp [beginEnvs, addEnvGeneration] at length
    change prior.envs.length ≤ last.envs.length
    omega
  · intro i bound
    have priorIndex : i < prior.envs.length := by omega
    have freshBound : i < begin.generation := by simpa [beginGeneration, addEnvGeneration] using priorIndex
    have beginIndex : i < begin.envs.length := by simp [beginEnvs, addEnvGeneration]; omega
    have lastIndex : i < last.envs.length := by omega
    have same := earlier i freshBound
    rw [Flapjack.holEl_eq_getElem _ _ lastIndex, Flapjack.holEl_eq_getElem _ _ beginIndex] at same
    rw [Flapjack.holEl_eq_getElem _ _ lastIndex, Flapjack.holEl_eq_getElem _ _ priorIndex]
    simpa [beginEnvs, addEnvGeneration, List.getElem_append_left, priorIndex] using same

/-- The forward oracle relation composes through the fresh Eval generation
and the subsequent reset to the caller's generation. -/
theorem oracForwardRel_resetAfterEval {C : Type}
    (interp : Option (Value → Option (Config × C))) (prior begin : EvalOracleState)
    (after : Option EvalState) (priorBound : prior.generation < prior.envs.length)
    (beginEnvs : begin.envs = (addEnvGeneration prior).envs)
    (beginGeneration : begin.generation = (addEnvGeneration prior).generation)
    (first : oracConfigEnvsSubspt interp (some (.evalOracle prior)) (some (.evalOracle begin)))
    (second : oracForwardRel interp (some (.evalOracle begin)) after) :
    oracForwardRel interp (some (.evalOracle prior))
      (resetEnvGeneration (some (.evalOracle prior)) after) := by
  have stable : srcOracNextCfg interp (resetEnvGeneration (some (.evalOracle prior)) after) =
      srcOracNextCfg interp after := by
    cases after with
    | none => rfl
    | some state => cases state <;> rfl
  have related := oracConfigEnvsSubspt_trans interp (some (.evalOracle prior))
    (some (.evalOracle begin)) after ⟨first, second.1⟩
  refine ⟨?_, evalStateCallRel_resetAfterEval prior begin after priorBound beginEnvs beginGeneration second.2⟩
  simpa [oracConfigEnvsSubspt, stable] using related

/-- Resetting an oracle state's generation preserves its decoded oracle,
step conditions, and stored environment invariants when the restored index
is in range. -/
theorem srcOracInvs_resetOracle {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (prior last : EvalOracleState)
    (current : srcOracInvs interp transform genv (some (.evalOracle last)))
    (priorBound : prior.generation < last.envs.length) :
    srcOracInvs interp transform genv
      (resetEnvGeneration (some (.evalOracle prior)) (some (.evalOracle last))) := by
  refine ⟨?_, ?_, ?_⟩
  · cases interp <;> simpa [srcOracStepInvs, resetEnvGeneration] using current.1
  · simpa [srcOracEnvInvs, srcOracNextCfg, resetEnvGeneration] using current.2.1
  · simpa [srcOracGenInv, resetEnvGeneration] using priorBound

/-- The flat oracle relation depends on the source oracle and callback, which
are unchanged by resetting the generation. -/
theorem oracRel_resetOracle {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (prior last : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (related : oracRel interp transform (some (.evalOracle last)) flat) :
    oracRel interp transform
      (resetEnvGeneration (some (.evalOracle prior)) (some (.evalOracle last))) flat := by
  cases interp with
  | none => simp [oracRel] at related
  | some decode => simpa [oracRel, oracRelInner, resetEnvGeneration] using related

/-- Resetting an oracle generation keeps the factored invariant at the
current index block and generation store. Restoring the caller's earlier
index block is a separate obligation. -/
theorem factoredInvariant_resetOracle {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (prior last : EvalOracleState)
    (mode : source.evalState = some (.evalOracle last))
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (priorBound : prior.generation < last.envs.length) :
    factoredInvariant interp transform gen genv idxs
      { source with evalState := resetEnvGeneration (some (.evalOracle prior)) source.evalState } flat := by
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := valid
  have srcInvs := srcOracInvs_resetOracle interp transform genv prior last (by simpa [mode] using invs) priorBound
  have oracle := oracRel_resetOracle interp transform prior last flat.evalConfig (by simpa [mode] using orac)
  refine ⟨cOk, tysOk, ?_, ?_, ?_, ?_, globals, reserved, genInv, ?_⟩
  · cases states with
    | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi
  · simpa [idxRangeRel, mode, srcOracNextCfg, resetEnvGeneration] using range
  · simpa [mode] using srcInvs
  · simpa [mode] using oracle
  · simpa [mode, srcOracNextCfg, resetEnvGeneration] using fin

/-- Restore the caller's factored invariant, forward-oracle relation, and
generation relation after an incremental Eval execution. The underlying
factored relations still need HOL correspondence review. -/
theorem factoredInvariant_endEval {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen innerGen : EnvironmentGenerationStore) (oldGenv genv : GlobalEnv)
    (start finish innerStart innerFinish : NextIndices) (other : Set (Nat × IndexKind))
    (prevSource source : SemanticPrimitivesHOL.State F) (prevFlat flat : FlatSem.State C F)
    (prior begin : EvalOracleState)
    (priorMode : prevSource.evalState = some (.evalOracle prior))
    (current : factoredInvariant interp transform innerGen genv
      (innerStart, innerFinish, idxBlock start finish ∪ other) source flat)
    (previousInv : factoredInvariant interp transform gen oldGenv (start, finish, other) prevSource prevFlat)
    (forward : oracForwardRel interp (some (.evalOracle begin)) source.evalState)
    (indices : idxPrev finish innerFinish)
    (initialForward : oracConfigEnvsSubspt interp prevSource.evalState (some (.evalOracle begin)))
    (beginEnvs : begin.envs = (addEnvGeneration prior).envs)
    (beginGeneration : begin.generation = (addEnvGeneration prior).generation) :
    let reset := resetEnvGeneration prevSource.evalState source.evalState
    factoredInvariant interp transform gen genv (start, finish, other)
      { source with evalState := reset } flat ∧
    oracForwardRel interp prevSource.evalState reset ∧
    (envGenRel gen prevSource.evalState → envGenRel gen reset) := by
  have ⟨_, _, _, oldRange, oldInvs, _, _, _, oldGenInv, _⟩ := previousInv
  have priorBound : prior.generation < prior.envs.length := by
    simpa [priorMode, srcOracGenInv] using oldInvs.2.2
  obtain ⟨last, lastMode, _, length, _⟩ := forward.2
  have lastBound : prior.generation < last.envs.length := by
    simp [beginEnvs, addEnvGeneration] at length
    omega
  have resetInv := factoredInvariant_resetOracle interp transform innerGen genv
    (innerStart, innerFinish, idxBlock start finish ∪ other) source flat prior last lastMode current lastBound
  have ⟨cOk, tysOk, states, currentRange, invs, oracle, globals, reserved, _, final⟩ := resetInv
  have restoredRange := idxRangeRel_restore interp oldGenv genv prevSource.nextTypeStamp prevSource.nextExnStamp
    source.nextTypeStamp source.nextExnStamp prevSource.evalState
    (resetEnvGeneration (some (.evalOracle prior)) source.evalState) start finish innerStart innerFinish other
    oldRange currentRange indices
  have restoredFin : finIdxMatch flat.globals.length finish
      (srcOracNextCfg interp (resetEnvGeneration (some (.evalOracle prior)) source.evalState)) := by
    cases cfg : srcOracNextCfg interp (resetEnvGeneration (some (.evalOracle prior)) source.evalState) with
    | none =>
      have bound : innerFinish.vidx ≤ flat.globals.length := by simpa [finIdxMatch, cfg] using final
      simpa [finIdxMatch, cfg] using Nat.le_trans indices.1 bound
    | some next => simpa [finIdxMatch, cfg] using final
  have resetForward := oracForwardRel_resetAfterEval interp prior begin source.evalState priorBound beginEnvs
    beginGeneration (by simpa [priorMode] using initialForward) forward
  refine ⟨?_, ?_, ?_⟩
  · simpa [priorMode] using (show factoredInvariant interp transform gen genv (start, finish, other)
        { source with evalState := resetEnvGeneration (some (.evalOracle prior)) source.evalState } flat from
      ⟨cOk, tysOk, states, restoredRange, invs, oracle, globals, reserved, oldGenInv, restoredFin⟩)
  · simpa [priorMode] using resetForward
  · intro genRel
    simpa [priorMode] using envGenRel_resetAfterEval gen prior begin source.evalState
      (by simpa [priorMode] using genRel) beginEnvs beginGeneration forward.2

/-- Source-shaped Eval return lemma over the factored invariant. It retains
the original oracle-shape premise; the factored relations remain unreviewed. -/
theorem factoredInvariant_endEval_sourceShape {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen innerGen : EnvironmentGenerationStore) (oldGenv genv : GlobalEnv)
    (start finish innerStart innerFinish : NextIndices) (other : Set (Nat × IndexKind))
    (prevSource source : SemanticPrimitivesHOL.State F) (prevFlat flat : FlatSem.State C F)
    (begin : Option EvalState)
    (current : factoredInvariant interp transform innerGen genv
      (innerStart, innerFinish, idxBlock start finish ∪ other) source flat)
    (previousInv : factoredInvariant interp transform gen oldGenv (start, finish, other) prevSource prevFlat)
    (forward : oracForwardRel interp begin source.evalState)
    (indices : idxPrev finish innerFinish)
    (initialForward : oracConfigEnvsSubspt interp prevSource.evalState begin)
    (beginShape : match prevSource.evalState with
      | some (.evalOracle prior) => ∃ beginState, begin = some (.evalOracle beginState) ∧
          beginState.envs = (addEnvGeneration prior).envs ∧
          beginState.generation = (addEnvGeneration prior).generation
      | _ => False) :
    let reset := resetEnvGeneration prevSource.evalState source.evalState
    factoredInvariant interp transform gen genv (start, finish, other)
      { source with evalState := reset } flat ∧
    oracForwardRel interp prevSource.evalState reset ∧
    (envGenRel gen prevSource.evalState → envGenRel gen reset) := by
  cases priorMode : prevSource.evalState with
  | none => simp [priorMode] at beginShape
  | some mode =>
    cases mode with
    | evalDecs prior => simp [priorMode] at beginShape
    | evalOracle prior =>
      obtain ⟨beginState, beginEq, beginEnvs, beginGeneration⟩ := by simpa [priorMode] using beginShape
      subst begin
      simpa [priorMode] using factoredInvariant_endEval interp transform gen innerGen oldGenv genv
        start finish innerStart innerFinish other prevSource source prevFlat flat prior beginState priorMode
        current previousInv forward indices initialForward beginEnvs beginGeneration

/-- Declaring an oracle environment preserves the factored simulation
invariant, provided the next compiler configuration contains the new map.
This is a partial step toward the HOL declaration theorem; the factored
relations still require source correspondence review. -/
theorem factoredInvariant_declareEnv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (state : EvalOracleState) (env : SemEnv Value) (storedEnvs : List (SemEnv Value))
    (sourceState : source.evalState = some (.evalOracle state))
    (found : state.envs[state.generation]? = some storedEnvs)
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (newMap : ∀ config, srcOracNextCfg interp (some (.evalOracle state)) = some config →
      ∃ mapGen compMap, Flapjack.sptLookup state.generation config.envs.envGens = some mapGen ∧
        Flapjack.sptLookup storedEnvs.length mapGen = some compMap ∧
        GlobalEnvInv genv compMap (fun _ => False) env) :
    factoredInvariant interp transform { gen with next := gen.next + 1 } genv idxs
      { source with evalState := some (.evalOracle
        { state with envs := state.envs.set state.generation (storedEnvs ++ [env]) }) } flat := by
  rcases valid with ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩
  have nextEq : srcOracNextCfg interp (some (.evalOracle
      { state with envs := state.envs.set state.generation (storedEnvs ++ [env]) })) =
      srcOracNextCfg interp (some (.evalOracle state)) := by rfl
  have envs := srcOracEnvInvs_declare interp genv state env storedEnvs found (by simpa [sourceState] using invs.2.1) newMap
  refine ⟨cOk, tysOk, ?_, ?_, ?_, ?_, globals, reserved, ?_, ?_⟩
  · cases states with
    | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi
  · simpa [idxRangeRel, sourceState, ← nextEq] using range
  · refine ⟨?_, envs, ?_⟩
    · cases interp <;> simpa [srcOracStepInvs, sourceState] using invs.1
    · simpa [srcOracGenInv, sourceState] using invs.2.2
  · cases interp with
    | none => simp [oracRel, sourceState] at orac
    | some decode => simpa [oracRel, oracRelInner, sourceState] using orac
  · intro i member
    have h := genInv i member
    change i < gen.next + 1
    omega
  · simpa [sourceState, nextEq] using fin

/-- Oracle-mode declaration and the generated flat store satisfy the
declaration step over the factored invariant. This is not yet the complete
HOL theorem: the no-Eval case and correspondence of the factored relations
remain to be established. -/
theorem declareEnv_storeEnvId_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (state : EvalOracleState) (env : SemEnv Value) (value : Value) (after : Option EvalState)
    (sourceState : source.evalState = some (.evalOracle state))
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (newMap : ∀ config, srcOracNextCfg interp source.evalState = some config →
      ∃ mapGen compMap, Flapjack.sptLookup gen.generation config.envs.envGens = some mapGen ∧
        Flapjack.sptLookup gen.next mapGen = some compMap ∧
        GlobalEnvInv genv compMap (fun _ => False) env) :
    ∃ stored : FlatSem.Value,
      FlatSem.evaluateDecs flat [storeEnvId gen.generation gen.next] =
        ({ flat with refs := .refv stored :: flat.refs.tail }, none) ∧
      factoredInvariant interp transform { gen with next := gen.next + 1 } genv idxs
        { source with evalState := after } flat ∧
      (∃ globals, flat.globals = some (.loc true 0) :: globals) ∧
      ValueRel genv value stored ∧ oracForwardRel interp source.evalState after ∧
      envGenRel { gen with next := gen.next + 1 } after := by
  have genRel : envGenRel gen (some (.evalOracle state)) := by simpa [sourceState] using generation
  have decl : declareEnv (some (.evalOracle state)) env = some (value, after) := by
    simpa [sourceState] using declared
  have ⟨_, _, _, _, _, _, _, reserved, _, _⟩ := valid
  obtain ⟨globals, old, refs, globalEq, refsEq⟩ := evalRefInv_heads flat reserved
  obtain ⟨stored, execution, valueRel, forward, nextGen, _⟩ :=
    declareEnv_storeEnvId_oracle interp state flat genv gen env value after genRel reserved decl
  refine ⟨stored, execution, ?_, ⟨globals, globalEq⟩, valueRel, ?_, nextGen⟩
  · cases found : state.envs[state.generation]? with
    | none => simp [declareEnv, found] at decl
    | some storedEnvs =>
      have genEq : gen.generation = state.generation := genRel.1
      have idEq : gen.next = storedEnvs.length := by simpa [found] using genRel.2.2
      have map : ∀ config, srcOracNextCfg interp (some (.evalOracle state)) = some config →
          ∃ mapGen compMap, Flapjack.sptLookup state.generation config.envs.envGens = some mapGen ∧
            Flapjack.sptLookup storedEnvs.length mapGen = some compMap ∧
            GlobalEnvInv genv compMap (fun _ => False) env := by
        intro config next
        simpa [sourceState, genEq, idEq] using newMap config (by simpa [sourceState] using next)
      simp [declareEnv, found] at decl
      obtain ⟨_, afterEq⟩ := decl
      subst after
      exact factoredInvariant_declareEnv interp transform gen genv idxs source flat state env storedEnvs
        sourceState found valid map
  · simpa [sourceState] using forward

/-- Declaration and the generated store satisfy the original theorem's
control-flow cases over the factored invariant. The relations underlying that
invariant have not yet been reviewed as HOL-equivalent. -/
theorem declareEnv_storeEnvId_factored_all {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (env : SemEnv Value) (value : Value) (after : Option EvalState)
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (newMap : ∀ config, srcOracNextCfg interp source.evalState = some config →
      ∃ mapGen compMap, Flapjack.sptLookup gen.generation config.envs.envGens = some mapGen ∧
        Flapjack.sptLookup gen.next mapGen = some compMap ∧
        GlobalEnvInv genv compMap (fun _ => False) env) :
    ∃ stored : FlatSem.Value,
      FlatSem.evaluateDecs flat [storeEnvId gen.generation gen.next] =
        ({ flat with refs := .refv stored :: flat.refs.tail }, none) ∧
      factoredInvariant interp transform { gen with next := gen.next + 1 } genv idxs
        { source with evalState := after } flat ∧
      (∃ globals, flat.globals = some (.loc true 0) :: globals) ∧
      ValueRel genv value stored ∧ oracForwardRel interp source.evalState after ∧
      envGenRel { gen with next := gen.next + 1 } after := by
  have ⟨_, _, _, _, _, oracle, _, _, _, _⟩ := valid
  cases sourceState : source.evalState with
  | none => simp [sourceState, declareEnv] at declared
  | some mode =>
    obtain ⟨_, state, _, modeEq⟩ := oracRel_some interp transform mode flat.evalConfig
      (by simpa [sourceState] using oracle)
    subst mode
    simpa [sourceState] using
      declareEnv_storeEnvId_factored interp transform gen genv idxs source flat state
        env value after sourceState valid generation declared newMap

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

/-- The declaration compiler's environment generation survives in the next
oracle configuration selected by a successful source Eval. -/
theorem doEval_oracle_envGenFuture {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ envId value decs config payload next flatDecs,
      state.oracle 0 = (envId, value, decs) ∧ decode value = some (config, payload) ∧
      output.2.1 = transform decs ∧ lookupEnv state envId = some output.1 ∧
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some config ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧
      idxPrev config.next next.next ∧
      envGenFutureRel (some decode)
        (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 := by
  obtain ⟨_, envId, value, decs, flatDecs, config, payload, nextId, nextValue, nextDecs,
    next, nextPayload, decoderEq, entry, nextEntry, decoded, nextDecoded, compiled, currentCfg⟩ :=
    sourceOracle_firstStep (some decode) transform state steps
  cases decoderEq
  obtain ⟨compiler, callback, _⟩ := related
  cases called : state.customDoEval [first, second, third, fourth, bytesValue, wordsValue] state.oracle with
  | none => simp [SemanticPrimitivesHOL.doEval, called] at success
  | some result =>
    have compilerSuccess : SourceEval.Proofs.doEvalOracle compiler transform
        [first, second, third, fourth, bytesValue, wordsValue] state.oracle = some result := by
      simpa [callback] using called
    obtain ⟨_, _, _, _, _, _, _, resultEq⟩ :=
      SourceEval.Proofs.doEvalOracle_six_inv compiler transform state.oracle first second third fourth
        bytesValue wordsValue envId value decs result entry compilerSuccess
    rw [resultEq] at called
    cases found : lookupEnv state envId with
    | none => simp [SemanticPrimitivesHOL.doEval, called, found] at success
    | some env =>
      simp [SemanticPrimitivesHOL.doEval, called, found] at success
      subst output
      have nextCfg : srcOracNextCfg (some decode)
          (some (.evalOracle (addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }))) = some next := by
        simp [srcOracNextCfg, srcOracNextCfgInner, addEnvGeneration, Flapjack.holShiftSeq, nextEntry, nextDecoded]
      refine ⟨envId, value, decs, config, payload, next, flatDecs, entry, decoded, rfl, found,
        currentCfg, nextCfg, compiled,
        incCompileProg_idxPrev envId config next (transform decs) flatDecs compiled, ?_⟩
      have future := incCompileProg_envGenFuture envId config (transform decs)
      rw [compiled] at future
      simpa [envGenFutureRel, nextCfg] using future

/-- Appending the slots reserved by successful incremental Eval preserves the
global environment and establishes the final-index length condition for the
next oracle configuration. -/
theorem doEval_oracle_globalSlots {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C) (genv : GlobalEnv)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (finish : NextIndices)
    (lengthMatch : finIdxMatch genv.v.length finish
      (srcOracNextCfg (some decode) (some (.evalOracle state))))
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ envId config next flatDecs,
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some config ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧
      idxPrev config.next next.next ∧
      let expanded := { genv with v := genv.v ++ List.replicate (next.next.vidx - config.next.vidx) none }
      GlobalGrowth genv expanded ∧ genvAllocatedIndices expanded = genvAllocatedIndices genv ∧
      finIdxMatch expanded.v.length next.next (srcOracNextCfg (some decode) output.2.2) := by
  obtain ⟨envId, _, _, config, _, next, flatDecs, _, _, _, _, currentCfg, nextCfg, compiled, prev, _⟩ :=
    doEval_oracle_envGenFuture decode transform state flat steps related
      first second third fourth bytesValue wordsValue output success
  refine ⟨envId, config, next, flatDecs, currentCfg, nextCfg, compiled, prev, ?_⟩
  have length : config.next.vidx = genv.v.length := by simpa [currentCfg, finIdxMatch] using lengthMatch
  refine ⟨GlobalGrowth.append genv _, genvAllocatedIndices_append_none genv _, ?_⟩
  simp only [nextCfg, finIdxMatch, List.length_append, List.length_replicate]
  have bound : config.next.vidx ≤ next.next.vidx := prev.1
  omega

/-- Successful Eval advances the index-range invariant to the block reserved
by the next incremental compilation. -/
theorem doEval_oracle_idxRange {C : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (flat : FlatSem.InstallConfig C) (genv : GlobalEnv)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat)
    (nextType nextExn : Nat) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel (some decode) genv nextType nextExn (some (.evalOracle state)) (start, finish, other))
    (lengthMatch : finIdxMatch genv.v.length finish
      (srcOracNextCfg (some decode) (some (.evalOracle state))))
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ envId config next flatDecs,
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧
      idxRangeRel (some decode)
        { genv with v := genv.v ++ List.replicate (next.next.vidx - config.next.vidx) none }
        nextType nextExn output.2.2 (config.next, next.next, idxBlock start finish ∪ other) := by
  obtain ⟨envId, config, next, flatDecs, currentCfg, nextCfg, compiled, prev, _⟩ :=
    doEval_oracle_globalSlots decode transform state flat genv steps related finish lengthMatch
      first second third fourth bytesValue wordsValue output success
  refine ⟨envId, config, next, flatDecs, nextCfg, compiled, ?_⟩
  exact idxRangeRel_advance (some decode) genv nextType nextExn _ _ start finish other config next _
    range currentCfg nextCfg prev

/-- The factored state relation survives the Eval state updates and global
slot allocation. This does not yet establish the remaining full evaluator
invariant or execution of the compiled declarations. -/
theorem doEval_oracle_stateRel {C F : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (genv : GlobalEnv) (states : StateRel genv source flat)
    (steps : srcOracStepInvs (some decode) transform (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat.evalConfig)
    (finish : NextIndices)
    (lengthMatch : finIdxMatch genv.v.length finish
      (srcOracNextCfg (some decode) (some (.evalOracle state))))
    (first second third fourth bytesValue wordsValue : Value)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval
      [first, second, third, fourth, bytesValue, wordsValue] (some (.evalOracle state)) = some output) :
    ∃ envId config next flatDecs,
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧
      let extra := List.replicate (next.next.vidx - config.next.vidx) none
      let expanded := { genv with v := genv.v ++ extra }
      let source' := { source with evalState := output.2.2 }
      let flat' := { flat with globals := flat.globals ++ extra, evalConfig :=
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } }
      GlobalGrowth genv expanded ∧ StateRel expanded source' flat' ∧
      genvAllocatedIndices expanded = genvAllocatedIndices genv ∧
      finIdxMatch expanded.v.length next.next (srcOracNextCfg (some decode) output.2.2) := by
  obtain ⟨envId, config, next, flatDecs, _, nextCfg, compiled, _, growth, indices, length⟩ :=
    doEval_oracle_globalSlots decode transform state flat.evalConfig genv steps related finish lengthMatch
      first second third fourth bytesValue wordsValue output success
  refine ⟨envId, config, next, flatDecs, nextCfg, compiled, growth, ?_, indices, length⟩
  cases states with
  | intro nonempty refs clock ffi =>
    exact .intro _ _ nonempty (storeList_growth genv _ growth _ _ refs) clock ffi

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

/-- Combined oracle-mode Eval simulation over the factored value and state
relations. This establishes the callback, source oracle, generation,
environment, state, and index-range postconditions with common witnesses.
The original HOL `do_eval` theorem additionally depends on the full reviewed
source-to-flat invariant and is not claimed by this infrastructure. -/
theorem doEval_oracle_combined {C F : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (genv : GlobalEnv) (states : StateRel genv source flat)
    (invs : srcOracInvs (some decode) transform genv (some (.evalOracle state)))
    (related : oracRel (some decode) transform (some (.evalOracle state)) flat.evalConfig)
    (constructors : genvCOk genv.c) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel (some decode) genv source.nextTypeStamp source.nextExnStamp
      (some (.evalOracle state)) (start, finish, other))
    (lengthMatch : finIdxMatch genv.v.length finish
      (srcOracNextCfg (some decode) (some (.evalOracle state))))
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues (some (.evalOracle state)) = some output) :
    ∃ envId config next flatDecs,
      srcOracNextCfg (some decode) (some (.evalOracle state)) = some config ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧ flatDecs ≠ [] ∧
      flatValues.length = 6 ∧
      FlatSem.doEval (flatValues.drop 4) flat.evalConfig =
        some (flatDecs, { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
          FlatSem.unitValue) ∧
      let extra := List.replicate (next.next.vidx - config.next.vidx) none
      let expanded := { genv with v := genv.v ++ extra }
      let source' := { source with evalState := output.2.2 }
      let flat' := { flat with globals := flat.globals ++ extra, evalConfig :=
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } }
      GlobalGrowth genv expanded ∧ StateRel expanded source' flat' ∧
      srcOracInvs (some decode) transform expanded output.2.2 ∧
      oracRel (some decode) transform output.2.2 flat'.evalConfig ∧
      idxRangeRel (some decode) expanded source.nextTypeStamp source.nextExnStamp output.2.2
        (config.next, next.next, idxBlock start finish ∪ other) ∧
      finIdxMatch expanded.v.length next.next (srcOracNextCfg (some decode) output.2.2) ∧
      envGenRel ⟨0, config.envs.next, .ln⟩ output.2.2 ∧
      envGenFutureRel (some decode)
        (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 ∧
      GlobalEnvInv expanded (lookupEnvId envId config.envs) (fun _ => False) output.1 ∧
      idxPrev finish next.next ∧ Flapjack.sptSubspt config.envs.envGens next.envs.envGens := by
  obtain ⟨envId, value, decs, config, payload, flatDecs, entry, decoded, sourceDecls,
    flatEq, flatLength, flatSuccess, _, _, _, _⟩ :=
    doEval_oracle_related decode transform state flat.evalConfig invs.1 related genv constructors
      sourceValues flatValues valuesRel output success
  have sourceLength : sourceValues.length = 6 := valuesRel.length_eq.trans flatLength
  obtain ⟨a, b, c, d, bytes, words, rfl⟩ := list_length_six sourceValues sourceLength
  obtain ⟨envId', value', decs', config', payload', next, flatDecs', entry', decoded', decls', lookup,
    currentCfg, nextCfg, compiled, prev, future⟩ :=
    doEval_oracle_envGenFuture decode transform state flat.evalConfig invs.1 related
      a b c d bytes words output success
  rw [entry] at entry'
  cases entry'
  rw [decoded] at decoded'
  cases decoded'
  have sameFlat : flatDecs = flatDecs' := by
    rw [← sourceDecls, compiled] at flatEq
    exact flatEq
  subst flatDecs'
  let expanded := { genv with v := genv.v ++ List.replicate (next.next.vidx - config.next.vidx) none }
  have growth : GlobalGrowth genv expanded := GlobalGrowth.append genv _
  obtain ⟨nextInvs, nextRelated⟩ :=
    doEval_oracle_preserves_sourceInvs decode transform state flat.evalConfig genv expanded growth invs related
      a b c d bytes words output success
  have nextRange := idxRangeRel_advance (some decode) genv source.nextTypeStamp source.nextExnStamp
    (some (.evalOracle state)) output.2.2 start finish other config next
    (next.next.vidx - config.next.vidx) range currentCfg nextCfg prev
  have currentLength : config.next.vidx = genv.v.length := by simpa [currentCfg, finIdxMatch] using lengthMatch
  have nextLength : finIdxMatch expanded.v.length next.next (srcOracNextCfg (some decode) output.2.2) := by
    simp only [nextCfg, finIdxMatch, expanded, List.length_append, List.length_replicate]
    have bound : config.next.vidx ≤ next.next.vidx := prev.1
    omega
  obtain ⟨configStore, nextStore, storeCfg, storeNext, _, _, submap, genRel⟩ :=
    doEval_oracle_envStoreAdvance decode transform state flat.evalConfig genv invs.1 invs.2.1 related
      a b c d bytes words output success
  rw [currentCfg] at storeCfg
  cases storeCfg
  rw [nextCfg] at storeNext
  cases storeNext
  obtain ⟨decode', config', payload', chosen, decoded', envInv⟩ :=
    srcOracEnvInvs_lookupEnvId (some decode) genv state envId output.1 value decs lookup invs.2.1 entry
  cases chosen
  rw [decoded] at decoded'
  cases decoded'
  have newEnvInv := globalEnvInv_growth genv expanded growth _ _ _ envInv
  have finishPrev : idxPrev finish config.next := by
    obtain ⟨_, _, final, _, tuple, finalCfg, order, _, _, _⟩ := range
    cases tuple
    simp [currentCfg] at finalCfg
    simpa [finalCfg] using order
  refine ⟨envId, config, next, flatDecs, currentCfg, nextCfg, compiled,
    incCompileProg_nonempty envId config next output.2.1 flatDecs compiled,
    flatLength, flatSuccess, growth, ?_, nextInvs, nextRelated, nextRange, nextLength, genRel, future, newEnvInv,
    idxPrev_trans finish config.next next.next ⟨finishPrev, prev⟩, submap⟩
  cases states with
  | intro nonempty refs clock ffi =>
    exact .intro _ _ nonempty (storeList_growth genv _ growth _ _ refs) clock ffi

/-- Oracle-mode Eval preserves the factored source-to-flat invariant and
provides the same compilation and environment witnesses for both evaluators.
This is not the HOL `do_eval` port: its component relations remain under
source review and its hypotheses explicitly select oracle mode. -/
theorem doEval_factoredInvariant {C F : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (state : EvalOracleState) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (sourceMode : source.evalState = some (.evalOracle state))
    (invariant : factoredInvariant (some decode) transform gen genv (start, finish, other) source flat)
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues source.evalState = some output) :
    ∃ envId config next flatDecs,
      FlatSem.doEval (flatValues.drop 4) flat.evalConfig =
        some (flatDecs, { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
          FlatSem.unitValue) ∧ flatValues.length = 6 ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧ flatDecs ≠ [] ∧
      let extra := List.replicate (next.next.vidx - config.next.vidx) none
      let expanded := { genv with v := genv.v ++ extra }
      let source' := { source with evalState := output.2.2 }
      let flat' := { flat with globals := flat.globals ++ extra, evalConfig :=
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } }
      factoredInvariant (some decode) transform ⟨0, config.envs.next, .ln⟩ expanded
        (config.next, next.next, idxBlock start finish ∪ other) source' flat' ∧
      envGenRel ⟨0, config.envs.next, .ln⟩ output.2.2 ∧
      envGenFutureRel (some decode)
        (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 ∧
      GlobalEnvInv expanded (lookupEnvId envId config.envs) (fun _ => False) output.1 ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧ idxPrev finish next.next ∧
      GlobalGrowth genv expanded ∧ oracConfigEnvsSubspt (some decode) source.evalState output.2.2 ∧
      (match source.evalState with
       | some (.evalOracle prior) => ∃ after, output.2.2 = some (.evalOracle after) ∧
           after.envs = (addEnvGeneration prior).envs ∧ after.generation = (addEnvGeneration prior).generation
       | _ => False) := by
  obtain ⟨constructors, typesOk, states, range, invs, related, globals, refs, _, lengthMatch⟩ := invariant
  rw [sourceMode] at range invs related lengthMatch success
  have lengthMatch' : finIdxMatch genv.v.length finish
      (srcOracNextCfg (some decode) (some (.evalOracle state))) := by
    simpa [globals] using lengthMatch
  obtain ⟨envId, config, next, flatDecs, currentCfg, nextCfg, compiled, nonempty,
    flatLength, flatSuccess, growth, states', invs', related', range', length', genRel, future, envInv,
    finishPrev, submap⟩ :=
    doEval_oracle_combined decode transform state source flat genv states invs related constructors
      start finish other range lengthMatch' sourceValues flatValues valuesRel output success
  refine ⟨envId, config, next, flatDecs, flatSuccess, flatLength, compiled, nonempty, ?_, genRel,
    future, envInv, nextCfg, finishPrev, growth, ?_, ?_⟩
  · refine ⟨constructors, typesOk, states', range', invs', related', ?_, ?_, ?_, ?_⟩
    · simp [globals]
    · exact evalRefInv_append flat.globals flat.refs _ refs
    · simp [envGenInv]
    · simpa [globals] using length'
  · simp [oracConfigEnvsSubspt, sourceMode, currentCfg, nextCfg, submap]
  · have sourceLength : sourceValues.length = 6 := valuesRel.length_eq.trans flatLength
    obtain ⟨a, b, c, d, bytes, words, rfl⟩ := list_length_six sourceValues sourceLength
    obtain ⟨post, _, _, _, _⟩ :=
      doEval_oracle_preserves_oracles decode transform state flat.evalConfig invs.1 related
        a b c d bytes words output success
    simp only [sourceMode]
    refine ⟨addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }, post, ?_, ?_⟩ <;>
      rfl

/-- A successful Eval under the factored invariant necessarily uses oracle
mode and preserves that invariant. The component relations are still under
HOL correspondence review, so this is not tagged as `do_eval`. -/
theorem doEval_factoredInvariant_any {C F : Type} [Nonempty C]
    (decode : Value → Option (Config × C)) (transform : List Dec → List Dec)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (invariant : factoredInvariant (some decode) transform gen genv (start, finish, other) source flat)
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues source.evalState = some output) :
    ∃ envId config next flatDecs,
      FlatSem.doEval (flatValues.drop 4) flat.evalConfig =
        some (flatDecs, { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
          FlatSem.unitValue) ∧ flatValues.length = 6 ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧ flatDecs ≠ [] ∧
      let extra := List.replicate (next.next.vidx - config.next.vidx) none
      let expanded := { genv with v := genv.v ++ extra }
      let source' := { source with evalState := output.2.2 }
      let flat' := { flat with globals := flat.globals ++ extra, evalConfig :=
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } }
      factoredInvariant (some decode) transform ⟨0, config.envs.next, .ln⟩ expanded
        (config.next, next.next, idxBlock start finish ∪ other) source' flat' ∧
      envGenRel ⟨0, config.envs.next, .ln⟩ output.2.2 ∧
      envGenFutureRel (some decode)
        (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 ∧
      GlobalEnvInv expanded (lookupEnvId envId config.envs) (fun _ => False) output.1 ∧
      srcOracNextCfg (some decode) output.2.2 = some next ∧ idxPrev finish next.next ∧
      GlobalGrowth genv expanded ∧ oracConfigEnvsSubspt (some decode) source.evalState output.2.2 ∧
      (match source.evalState with
       | some (.evalOracle prior) => ∃ after, output.2.2 = some (.evalOracle after) ∧
           after.envs = (addEnvGeneration prior).envs ∧ after.generation = (addEnvGeneration prior).generation
       | _ => False) := by
  cases mode : source.evalState with
  | none => simp [SemanticPrimitivesHOL.doEval, mode] at success
  | some evalState =>
    have related : oracRel (some decode) transform (some evalState) flat.evalConfig := by
      simpa [mode] using invariant.2.2.2.2.2.1
    obtain ⟨decode', state, decoderEq, stateEq⟩ :=
      oracRel_some (some decode) transform evalState flat.evalConfig related
    cases decoderEq
    subst evalState
    simpa [mode] using doEval_factoredInvariant decode transform state source flat gen genv start finish other
      mode invariant sourceValues flatValues valuesRel output success

/-- Successful Eval under the factored invariant determines whether the optional
decoder is present; its postconditions use the same optional interface as HOL. -/
theorem doEval_factoredInvariant_optional {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues source.evalState = some output) :
    ∃ envId config next flatDecs,
      FlatSem.doEval (flatValues.drop 4) flat.evalConfig =
        some (flatDecs, { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
          FlatSem.unitValue) ∧ flatValues.length = 6 ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧ flatDecs ≠ [] ∧
      let extra := List.replicate (next.next.vidx - config.next.vidx) none
      let expanded := { genv with v := genv.v ++ extra }
      let source' := { source with evalState := output.2.2 }
      let flat' := { flat with globals := flat.globals ++ extra, evalConfig :=
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } }
      factoredInvariant interp transform ⟨0, config.envs.next, .ln⟩ expanded
        (config.next, next.next, idxBlock start finish ∪ other) source' flat' ∧
      envGenRel ⟨0, config.envs.next, .ln⟩ output.2.2 ∧
      envGenFutureRel interp
        (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 ∧
      GlobalEnvInv expanded (lookupEnvId envId config.envs) (fun _ => False) output.1 ∧
      srcOracNextCfg interp output.2.2 = some next ∧ idxPrev finish next.next ∧
      GlobalGrowth genv expanded ∧ oracConfigEnvsSubspt interp source.evalState output.2.2 ∧
      (match source.evalState with
       | some (.evalOracle prior) => ∃ after, output.2.2 = some (.evalOracle after) ∧
           after.envs = (addEnvGeneration prior).envs ∧ after.generation = (addEnvGeneration prior).generation
       | _ => False) := by
  cases interp with
  | none =>
    cases mode : source.evalState with
    | none => simp [SemanticPrimitivesHOL.doEval, mode] at success
    | some evalState =>
      have related : oracRel none transform (some evalState) flat.evalConfig := by
        simpa [mode] using invariant.2.2.2.2.2.1
      cases evalState <;> simp [oracRel] at related
  | some decode =>
    exact doEval_factoredInvariant_any decode transform source flat gen genv start finish other
      invariant sourceValues flatValues valuesRel output success

/-- The source-shaped Eval simulation, with an explicit resulting global
environment and componentwise map and slot preservation. This is untagged:
the component value, environment, and state relations still require HOL
correspondence review. -/
theorem doEval_factoredInvariant_sourceShape {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (invariant : factoredInvariant interp transform gen genv idxs source flat)
    (sourceValues : List Value) (flatValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sourceValues flatValues)
    (output : SemEnv Value × List Dec × Option EvalState)
    (success : SemanticPrimitivesHOL.doEval sourceValues source.evalState = some output) :
    ∃ genv' envId config next flatDecs start finish other,
      idxs = (start, finish, other) ∧
      FlatSem.doEval (flatValues.drop 4) flat.evalConfig =
        some (flatDecs, { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
          FlatSem.unitValue) ∧ flatValues.length = 6 ∧
      incCompileProg envId config output.2.1 = (next, flatDecs) ∧ flatDecs ≠ [] ∧
      factoredInvariant interp transform ⟨0, config.envs.next, .ln⟩ genv'
        (config.next, next.next, idxBlock start finish ∪ other)
        { source with evalState := output.2.2 }
        { flat with globals := flat.globals ++ List.replicate (next.next.vidx - config.next.vidx) none, evalConfig :=
          { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle } } ∧
      envGenRel ⟨0, config.envs.next, .ln⟩ output.2.2 ∧
      envGenFutureRel interp (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
        ⟨0, config.envs.next, .ln⟩ output.2.1).2.2.2.1 output.2.2 ∧
      GlobalEnvInv genv' (lookupEnvId envId config.envs) (fun _ => False) output.1 ∧
      srcOracNextCfg interp output.2.2 = some next ∧ idxPrev finish next.next ∧
      finiteSubmap genv.c genv'.c ∧ finiteSubmap genv.tys genv'.tys ∧ subglobals genv.v genv'.v ∧
      oracConfigEnvsSubspt interp source.evalState output.2.2 ∧
      (match source.evalState with
       | some (.evalOracle prior) => ∃ after, output.2.2 = some (.evalOracle after) ∧
           after.envs = (addEnvGeneration prior).envs ∧ after.generation = (addEnvGeneration prior).generation
       | _ => False) := by
  rcases idxs with ⟨start, finish, other⟩
  obtain ⟨envId, config, next, flatDecs, flatEval, length, compiled, nonempty, postInv,
    genRel, future, envInv, nextCfg, previous, growth, oracleSubmap, oracleShape⟩ :=
    doEval_factoredInvariant_optional interp transform source flat gen genv start finish other
      invariant sourceValues flatValues valuesRel output success
  let genv' := { genv with v := genv.v ++ List.replicate (next.next.vidx - config.next.vidx) none }
  have components := (globalGrowth_iff genv genv').mp growth
  exact ⟨genv', envId, config, next, flatDecs, start, finish, other, rfl, flatEval, length,
    compiled, nonempty, postInv, genRel, future, envInv, nextCfg, previous,
    components.2.1, components.2.2, components.1, oracleSubmap, oracleShape⟩

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
