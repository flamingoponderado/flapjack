import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordLists
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalPattern
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreEnvId

/-! Source-to-flat Eval callback simulation over the factored value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace InvariantPort

/-- Roundtrip for the global carrier's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env

end InvariantPort

/-- Source-to-flat invariant for evaluator simulations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_def"
  (fmap_as_finite_support := [c, tys])]
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

/-- The full invariant entails the environment-generation invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_env_gen_inv"
  (fmap_as_finite_support := [c, tys])]
theorem invariantEnvGenInv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idx endIdx : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv (idx, endIdx, other) source flat) :
    envGenInv gen := by
  obtain ⟨_, _, _, _, _, _, _, _, genInv, _⟩ := valid
  exact genInv

/-- Replacing both clocks by the same value preserves the simulation invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_change_clock"
  (fmap_as_finite_support := [c, tys])]
theorem invariantChangeClock {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (clock : Nat)
    (valid : factoredInvariant interp transform gen genv idxs source flat) :
    factoredInvariant interp transform gen genv idxs
      { source with clock := clock } { flat with clock := clock } := by
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := valid
  have updated : StateRel genv { source with clock := clock } { flat with clock := clock } := by
    cases states with
    | intro nonempty refs _ ffi => exact .intro _ _ nonempty refs rfl ffi
  exact ⟨cOk, tysOk, updated, range, invs, orac, globals, reserved, genInv, fin⟩

/-- Related states have equal clocks and remain related after decrementing both. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_dec_clock"
  (fmap_as_finite_support := [c, tys])]
theorem invariantDecClock {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv idxs source flat) :
    source.clock = flat.clock ∧
      factoredInvariant interp transform gen genv idxs (EvaluateHOL.decClock source) (FlatSem.decClock flat) := by
  have same := (stateRel_iff genv source flat).mp valid.2.2.1 |>.2.2.1
  refine ⟨same, ?_⟩
  simpa [EvaluateHOL.decClock, FlatSem.decClock, same] using
    invariantChangeClock interp transform gen genv idxs source flat (flat.clock - 1) valid

/-- The invariant identifies the flat global vector with the related globals. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_globals"
  (fmap_as_finite_support := [c, tys])]
theorem invariantGlobals {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv idxs source flat) :
    flat.globals = genv.v := valid.2.2.2.2.2.2.1.symm

/-- The invariant implies the global constructor-map condition. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_genv_c_ok"
  (fmap_as_finite_support := [c, tys])]
theorem invariantGenvCOk {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv idxs source flat) :
    genvCOk genv.c := valid.1

/-- Shrinking the index block preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_idx_range_shrink"
  (fmap_as_finite_support := [c, tys])]
theorem invariantIdxRangeShrink {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start next finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (premises : factoredInvariant interp transform gen genv (start, finish, other) source flat ∧
      idxPrev start next ∧ idxPrev next finish) :
    factoredInvariant interp transform gen genv (next, finish, other) source flat := by
  obtain ⟨valid, previous, bounded⟩ := premises
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := valid
  exact ⟨cOk, tysOk, states, idxRangeRel_shrink interp genv _ _ _ start next finish other
    ⟨range, previous, bounded⟩, invs, orac, globals, reserved, genInv, fin⟩

/-- Shrinking the index block and replacing a valid generation preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_idx_range_shrink_gen"
  (fmap_as_finite_support := [c, tys])]
theorem invariantIdxRangeShrinkGen {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen newGen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start next finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (premises : factoredInvariant interp transform gen genv (start, finish, other) source flat ∧
      idxPrev start next ∧ idxPrev next finish ∧ (envGenInv gen → envGenInv newGen)) :
    factoredInvariant interp transform newGen genv (next, finish, other) source flat := by
  obtain ⟨valid, previous, bounded, generations⟩ := premises
  have shrunk := invariantIdxRangeShrink interp transform gen genv start next finish other
    source flat ⟨valid, previous, bounded⟩
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := shrunk
  exact ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, generations genInv, fin⟩

/-- Replacing the reserved first reference preserves the simulation invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "invariant_change_eval_ref"
  (fmap_as_finite_support := [c, tys])]
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

/-- Replacing the ordinary source and flat stores preserves the factored
invariant when the new stores are related and the reserved flat entry is
unchanged. This is preliminary Flapjack infrastructure. -/
theorem factoredInvariant_changeStores {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceRefs : Store Value) (flatRefs : Store FlatSem.Value)
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (states : StateRel genv { source with refs := sourceRefs } { flat with refs := flatRefs })
    (reserved : flatRefs.take 1 = flat.refs.take 1) :
    factoredInvariant interp transform gen genv idxs
      { source with refs := sourceRefs } { flat with refs := flatRefs } := by
  obtain ⟨cOk, tysOk, _, range, invs, orac, globals, oldReserved, genInv, fin⟩ := valid
  refine ⟨cOk, tysOk, states, range, invs, orac, globals, ?_, genInv, fin⟩
  simpa only [reserved] using oldReserved

/-- An external call can change the FFI state as well as the two stores.
The remaining components of the factored invariant do not observe FFI. -/
theorem factoredInvariant_changeStoresFfi {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceRefs : Store Value) (flatRefs : Store FlatSem.Value) (ffi : HolFfiState F)
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (states : StateRel genv { source with refs := sourceRefs, ffi := ffi }
      { flat with refs := flatRefs, ffi := ffi })
    (reserved : flatRefs.take 1 = flat.refs.take 1) :
    factoredInvariant interp transform gen genv idxs
      { source with refs := sourceRefs, ffi := ffi } { flat with refs := flatRefs, ffi := ffi } := by
  obtain ⟨cOk, tysOk, _, range, invs, orac, globals, oldReserved, genInv, fin⟩ := valid
  refine ⟨cOk, tysOk, states, range, invs, orac, globals, ?_, genInv, fin⟩
  simpa only [reserved] using oldReserved

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

/-- Declaring an environment agrees with execution of the generated store. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "declare_env_store_env_id"
  (fmap_as_finite_support := [c, tys])]
theorem declareEnv_storeEnvId {C F : Type} [Nonempty C]
    (source : SemanticPrimitivesHOL.State F) (env : SemEnv Value) (value : Value)
    (after : Option EvalState) (interp : Option (Value → Option (Config × C)))
    (transform : List Dec → List Dec) (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (flat : FlatSem.State C F) (genId id : Nat)
    (premises : declareEnv source.evalState env = some (value, after) ∧
      factoredInvariant interp transform gen genv idxs source flat ∧
      envGenRel gen source.evalState ∧ genId = gen.generation ∧ id = gen.next ∧
      (match srcOracNextCfg interp source.evalState with
      | none => True
      | some config =>
        match Flapjack.sptLookup genId config.envs.envGens with
        | none => False
        | some mapGen =>
          match Flapjack.sptLookup id mapGen with
          | none => False
          | some compMap => GlobalEnvInv genv compMap (fun _ => False) env)) :
    ∃ stored : FlatSem.Value,
      FlatSem.evaluateDecs flat [storeEnvId genId id] =
        ({ flat with refs := .refv stored :: flat.refs.tail }, none) ∧
      factoredInvariant interp transform { gen with next := gen.next + 1 } genv idxs
        { source with evalState := after } flat ∧
      (∃ globals, flat.globals = some (.loc true 0) :: globals) ∧
      ValueRel genv value stored ∧ oracForwardRel interp source.evalState after := by
  obtain ⟨declared, valid, generation, rfl, rfl, mapCase⟩ := premises
  have newMap : ∀ config, srcOracNextCfg interp source.evalState = some config →
      ∃ mapGen compMap, Flapjack.sptLookup gen.generation config.envs.envGens = some mapGen ∧
        Flapjack.sptLookup gen.next mapGen = some compMap ∧
        GlobalEnvInv genv compMap (fun _ => False) env := by
    intro config cfg
    rw [cfg] at mapCase
    cases genLookup : Flapjack.sptLookup gen.generation config.envs.envGens with
    | none => simp [genLookup] at mapCase
    | some mapGen =>
      cases mapLookup : Flapjack.sptLookup gen.next mapGen with
      | none => simp [genLookup, mapLookup] at mapCase
      | some compMap => exact ⟨mapGen, compMap, rfl, mapLookup, by simpa [genLookup, mapLookup] using mapCase⟩
  have ⟨_, _, _, _, _, oracle, _, _, _, _⟩ := valid
  cases sourceState : source.evalState with
  | none => simp [sourceState, declareEnv] at declared
  | some mode =>
    obtain ⟨_, state, _, modeEq⟩ := oracRel_some interp transform mode flat.evalConfig
      (by simpa [sourceState] using oracle)
    subst mode
    have genRel : envGenRel gen (some (.evalOracle state)) := by
      simpa [sourceState] using generation
    have decl : declareEnv (some (.evalOracle state)) env = some (value, after) := by
      simpa [sourceState] using declared
    have ⟨_, _, _, _, _, _, _, reserved, _, _⟩ := valid
    obtain ⟨globals, old, refs, globalEq, refsEq⟩ := evalRefInv_heads flat reserved
    have forward := declareEnv_oracle_forward interp state env value after decl
    cases found : state.envs[state.generation]? with
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
      obtain ⟨valueEq, afterEq⟩ := decl
      subst value
      subst after
      let stored : FlatSem.Value := .conv none
        [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
      refine ⟨stored, ?_, ?_, ⟨globals, globalEq⟩, ?_, forward⟩
      · simpa [stored, refsEq] using evaluateStoreEnvId flat gen.generation gen.next globals old refs globalEq refsEq
      · exact factoredInvariant_declareEnv interp transform gen genv idxs source flat state env storedEnvs
          sourceState found valid map
      · dsimp [stored, natToValue]
        rw [genEq, idEq]
        apply valueRel_tuple
        exact .cons (.literal genv _) (.cons (.literal genv _) .nil)

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
      have flatBytesDecoded := valueToWord8List_related genv bytesValue flatBytes bytes ⟨decodedBytes, bytesRel, constructors⟩
      have flatWordsDecoded := valueToWord64List_related genv wordsValue flatWords words ⟨decodedWords, wordsRel, constructors⟩
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

/-- Flapjack list infrastructure: expose the six operands used by the Eval proof. -/
theorem list_length_six {α : Type} (xs : List α) (length : xs.length = 6) :
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
  obtain ⟨config', payload', mapGen, compMap, decoded', generation, mapping, mapInv⟩ :=
    srcOracEnvInvs_lookup (some decode) genv state envId output.1 value decs ⟨lookup, invs.2.1, entry⟩
  have envInv : GlobalEnvInv genv (lookupEnvId envId config'.envs) (fun _ => False) output.1 := by
    simpa [lookupEnvId, generation, mapping] using mapInv
  change decode value = some (config', payload') at decoded'
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

/-- A successful source Eval has a corresponding flat Eval and preserves the
compiler invariants and global-environment relationships. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_eval"
  (fmap_as_finite_support := [c, tys])]
theorem doEval_correct {C F Fin : Type} [Nonempty C] [Nonempty Fin]
    (sourceValues : List Value) (source : SemanticPrimitivesHOL.State F)
    (env : SemEnv Value) (decs : List Dec) (after : Option EvalState)
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (flat : FlatSem.State C F) :
    ∀ flatValues : List FlatSem.Value,
      SemanticPrimitivesHOL.doEval sourceValues source.evalState = some (env, decs, after) ∧
      factoredInvariant interp transform gen genv idxs source flat ∧
      List.Forall₂ (ValueRel genv) sourceValues flatValues →
      ∃ (genv' : GlobalEnv) (envId : Nat × Nat) (config : Config) (flatDecs : List FlatLang.Exp)
        (evalConfig : FlatSem.InstallConfig C) (next : Config) (start finish : NextIndices)
        (_finIdx : Fin) (other : Set (Nat × IndexKind)),
        idxs = (start, finish, other) ∧
        FlatSem.doEval (flatValues.drop 4) flat.evalConfig = some (flatDecs, evalConfig, FlatSem.unitValue) ∧
        flatValues.length = 6 ∧ incCompileProg envId config decs = (next, flatDecs) ∧ flatDecs ≠ [] ∧
        factoredInvariant interp transform ⟨0, config.envs.next, .ln⟩ genv'
          (config.next, next.next, idxBlock start finish ∪ other)
          { source with evalState := after }
          { flat with globals := flat.globals ++ List.replicate (next.next.vidx - config.next.vidx) none, evalConfig := evalConfig } ∧
        envGenRel ⟨0, config.envs.next, .ln⟩ after ∧
        envGenFutureRel interp (compileDecs [] 1 config.next (lookupEnvId envId config.envs)
          ⟨0, config.envs.next, .ln⟩ decs).2.2.2.1 after ∧
        GlobalEnvInv genv' (lookupEnvId envId config.envs) (fun _ => False) env ∧
        srcOracNextCfg interp after = some next ∧ idxPrev finish next.next ∧
        finiteSubmap genv.c genv'.c ∧ finiteSubmap genv.tys genv'.tys ∧ subglobals genv.v genv'.v ∧
        oracConfigEnvsSubspt interp source.evalState after ∧
        (match source.evalState with
         | some (.evalOracle prior) => ∃ state', after = some (.evalOracle state') ∧
             state'.envs = (addEnvGeneration prior).envs ∧
             state'.generation = (addEnvGeneration prior).generation
         | _ => False) := by
  intro flatValues ⟨success, invariant, valuesRel⟩
  rcases idxs with ⟨start, finish, other⟩
  cases interp with
  | none =>
    cases mode : source.evalState with
    | none => simp [SemanticPrimitivesHOL.doEval, mode] at success
    | some evalState =>
      have related : oracRel none transform (some evalState) flat.evalConfig := by
        simpa [mode] using invariant.2.2.2.2.2.1
      cases evalState <;> simp [oracRel] at related
  | some decode =>
    cases mode : source.evalState with
    | none => simp [SemanticPrimitivesHOL.doEval, mode] at success
    | some evalState =>
      have related : oracRel (some decode) transform (some evalState) flat.evalConfig := by
        simpa [mode] using invariant.2.2.2.2.2.1
      obtain ⟨decode', state, decoderEq, stateEq⟩ :=
        oracRel_some (some decode) transform evalState flat.evalConfig related
      cases decoderEq
      subst evalState
      obtain ⟨constructors, typesOk, states, range, invs, related, globals, refs, _, lengthMatch⟩ := invariant
      rw [mode] at range invs related lengthMatch success
      have lengthMatch' : finIdxMatch genv.v.length finish
          (srcOracNextCfg (some decode) (some (.evalOracle state))) := by
        simpa [globals] using lengthMatch
      obtain ⟨envId, config, next, flatDecs, currentCfg, nextCfg, compiled, nonempty,
        flatLength, flatSuccess, growth, states', invs', related', range', length', genRel, future, envInv,
        finishPrev, submap⟩ :=
        doEval_oracle_combined decode transform state source flat genv states invs related constructors
          start finish other range lengthMatch' sourceValues flatValues valuesRel (env, decs, after) success
      let genv' := { genv with v := genv.v ++ List.replicate (next.next.vidx - config.next.vidx) none }
      have components := (globalGrowth_iff genv genv').mp growth
      refine ⟨genv', envId, config, flatDecs,
        { flat.evalConfig with compileOracle := Flapjack.holShiftSeq 1 flat.evalConfig.compileOracle },
        next, start, finish, Classical.choice inferInstance, other, rfl, flatSuccess, flatLength,
        compiled, nonempty, ?_, genRel, future, envInv, nextCfg, finishPrev,
        components.2.1, components.2.2, components.1, ?_, ?_⟩
      · refine ⟨constructors, typesOk, states', range', invs', related', ?_, ?_, ?_, ?_⟩
        · simp [globals, genv']
        · exact evalRefInv_append flat.globals flat.refs _ refs
        · simp [envGenInv]
        · simpa [globals, genv'] using length'
      · simp [oracConfigEnvsSubspt, currentCfg, nextCfg, submap]
      · have sourceLength : sourceValues.length = 6 := valuesRel.length_eq.trans flatLength
        obtain ⟨a, b, c, d, bytes, words, rfl⟩ := list_length_six sourceValues sourceLength
        obtain ⟨post, _, _, _, _⟩ :=
          doEval_oracle_preserves_oracles decode transform state flat.evalConfig invs.1 related
            a b c d bytes words (env, decs, after) success
        refine ⟨addEnvGeneration { state with oracle := Flapjack.holShiftSeq 1 state.oracle }, post, ?_, ?_⟩ <;>
          rfl

/-- Successful flat Eval advances its compiler oracle by one. This is a
consequence of the flat evaluator definition used by the Eval simulation;
it has no separate HOL declaration. -/
theorem flatDoEval_config {C : Type} (vs : List FlatSem.Value) (cfg next : FlatSem.InstallConfig C)
    (decs : List FlatLang.Exp) (value : FlatSem.Value)
    (success : FlatSem.doEval vs cfg = some (decs, next, value)) :
    next = { cfg with compileOracle := Flapjack.holShiftSeq 1 cfg.compileOracle } := by
  classical
  simp only [FlatSem.doEval] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  all_goals simp_all

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
