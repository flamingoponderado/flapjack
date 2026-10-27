import Flapjack.Compiler.Backend.SourceToFlat.Proofs.IndexInvariant
import Flapjack.Misc.Sptree.Subspt
import Flapjack.Misc.ListEl

/-! Source-oracle configuration and index-range conditions. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
namespace OracleInvariant

/-- Decode the source compiler configuration in one oracle entry. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "src_orac_next_cfg_inner_def"]
def srcOracNextCfgInner {A S D R C : Type} (interp : Option (S → Option (R × C)))
    (entry : A × S × D) : Option R :=
  match interp with
  | none => none
  | some decode => (decode entry.2.1).map Prod.fst

/-- Read the next configuration from the source evaluation oracle. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "src_orac_next_cfg_def"]
def srcOracNextCfg {R C : Type} (interp : Option (Value → Option (R × C)))
    (evalState : Option EvalState) : Option R :=
  match evalState with
  | some (.evalOracle state) => srcOracNextCfgInner interp (state.oracle 0)
  | _ => none

/-- The reserved global points to the first flat reference cell. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "eval_ref_inv_def"]
def evalRefInv {α : Type} (firstGlobal : List (Option FlatSem.Value)) (firstRef : List (StoreValue α)) : Prop :=
  firstGlobal = [some (.loc true 0)] ∧ ∃ v, firstRef = [.refv v]

/-- Extending the global list does not change the reserved first reference. -/
theorem evalRefInv_append {α : Type} (globals : List (Option FlatSem.Value))
    (refs : List (StoreValue α)) (extra : List (Option FlatSem.Value))
    (valid : evalRefInv (globals.take 1) (refs.take 1)) :
    evalRefInv ((globals ++ extra).take 1) (refs.take 1) := by
  cases globals with
  | nil => simp [evalRefInv] at valid
  | cons first rest => simpa using valid

/-- Future source-oracle configurations retain the preceding environment
generation store. Missing configurations correspond only to missing ones. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_config_envs_subspt_def"]
def oracConfigEnvsSubspt {C : Type} (interp : Option (Value → Option (Config × C)))
    (before after : Option EvalState) : Prop :=
  match srcOracNextCfg interp before, srcOracNextCfg interp after with
  | none, none => True
  | some a, some b => Flapjack.sptSubspt a.envs.envGens b.envs.envGens
  | _, _ => False

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_config_envs_subspt_refl"]
theorem oracConfigEnvsSubspt_refl {C : Type} (interp : Option (Value → Option (Config × C)))
    (state : Option EvalState) : oracConfigEnvsSubspt interp state state := by
  unfold oracConfigEnvsSubspt
  cases srcOracNextCfg interp state with
  | none => trivial
  | some config => intro key member; exact ⟨member, rfl⟩

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_config_envs_subspt_trans"]
theorem oracConfigEnvsSubspt_trans {C : Type} (interp : Option (Value → Option (Config × C)))
    (first middle last : Option EvalState)
    (relations : oracConfigEnvsSubspt interp first middle ∧ oracConfigEnvsSubspt interp middle last) :
    oracConfigEnvsSubspt interp first last := by
  unfold oracConfigEnvsSubspt at *
  cases h1 : srcOracNextCfg interp first <;> cases h2 : srcOracNextCfg interp middle <;>
    cases h3 : srcOracNextCfg interp last <;> simp [h1, h2, h3] at relations ⊢
  exact Flapjack.sptSubsptTrans _ _ _ ⟨relations.1, relations.2⟩

/-- Calls return to the same source environment generation, preserving the
earlier generations while allowing the environment store to grow. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "eval_state_call_rel_def"]
def evalStateCallRel (before after : Option EvalState) : Prop :=
  match before with
  | some (.evalOracle first) => ∃ last, after = some (.evalOracle last) ∧
      last.generation = first.generation ∧ first.envs.length ≤ last.envs.length ∧
      ∀ i, i < first.generation → Flapjack.holEl i last.envs = Flapjack.holEl i first.envs
  | _ => True

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "eval_state_call_rel_refl"]
theorem evalStateCallRel_refl (state : Option EvalState) : evalStateCallRel state state := by
  cases state with
  | none => trivial
  | some state =>
    cases state with
    | evalDecs state => trivial
    | evalOracle state => exact ⟨state, rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "eval_state_call_rel_trans"]
theorem evalStateCallRel_trans (first middle last : Option EvalState)
    (relations : evalStateCallRel first middle ∧ evalStateCallRel middle last) :
    evalStateCallRel first last := by
  cases first with
  | none => trivial
  | some first =>
    cases first with
    | evalDecs state => trivial
    | evalOracle first =>
      obtain ⟨middleState, rfl, generation, length, earlier⟩ := relations.1
      obtain ⟨lastState, lastEq, generation', length', earlier'⟩ := relations.2
      refine ⟨lastState, lastEq, generation'.trans generation, Nat.le_trans length length', ?_⟩
      intro i bound
      exact (earlier' i (by simpa [generation] using bound)).trans (earlier i bound)

/-- Successful calls preserve both oracle configuration stores and source
environment generations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_forward_rel_def"]
def oracForwardRel {C : Type} (interp : Option (Value → Option (Config × C)))
    (before after : Option EvalState) : Prop :=
  oracConfigEnvsSubspt interp before after ∧ evalStateCallRel before after

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_forward_rel_refl"]
theorem oracForwardRel_refl {C : Type} (interp : Option (Value → Option (Config × C)))
    (state : Option EvalState) : oracForwardRel interp state state :=
  ⟨oracConfigEnvsSubspt_refl interp state, evalStateCallRel_refl state⟩

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_forward_rel_trans"]
theorem oracForwardRel_trans {C : Type} (interp : Option (Value → Option (Config × C)))
    (first middle last : Option EvalState)
    (relations : oracForwardRel interp first middle ∧ oracForwardRel interp middle last) :
    oracForwardRel interp first last :=
  ⟨oracConfigEnvsSubspt_trans interp first middle last ⟨relations.1.1, relations.2.1⟩,
    evalStateCallRel_trans first middle last ⟨relations.1.2, relations.2.2⟩⟩

/-- Canonical roundtrip for the imported global environment's finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

/-- Source index ranges, including oracle configuration and stamp freshness. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_range_rel_def"
  (fmap_as_finite_support := [c, tys])]
def idxRangeRel {C : Type} (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) : Prop :=
  ∃ start finish final other,
    idxs = (start, finish, other) ∧
    (match srcOracNextCfg interp evalState with | none => True | some config => final = config.next) ∧
    idxPrev finish final ∧
    allDisjoint [idxBlock start finish, idxFinalBlock final, other, genvAllocatedIndices genv] ∧
    (∀ cn t, nextType ≤ t → ¬ ∃ key, genv.c.lookup key = some (.typeStamp cn t)) ∧
    (∀ cn, nextExn ≤ cn → ¬ ∃ key, genv.c.lookup key = some (.exnStamp cn))

/-- Filling the next reserved variable slot advances the start of the
current block while preserving the source index-range invariant. -/
theorem idxRangeRel_fillSlot {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind)) (value : FlatSem.Value)
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (empty : genv.v[start.vidx]? = some none) (fits : start.vidx + 1 ≤ finish.vidx) :
    idxRangeRel interp { genv with v := genv.v.set start.vidx (some value) }
      nextType nextExn evalState ({ start with vidx := start.vidx + 1 }, finish, other) := by
  obtain ⟨_, _, final, _, tuple, nextMatch, previous, disjoint, types, exceptions⟩ := range
  cases tuple
  refine ⟨_, _, final, other, rfl, nextMatch, previous, ?_, types, exceptions⟩
  rw [genvAllocatedIndices_fillSlot genv start.vidx value empty]
  apply allDisjoint_consume (idxBlock start finish)
    (idxBlock { start with vidx := start.vidx + 1 } finish) (idxFinalBlock final)
    other (genvAllocatedIndices genv) (start.vidx, .variable) disjoint
  · intro ⟨i, kind⟩ member
    change idxBlock { start with vidx := start.vidx + 1 } finish (i, kind) at member
    change idxBlock start finish (i, kind)
    cases kind <;> simp only [idxBlock] at member ⊢ <;> omega
  · change idxBlock start finish (start.vidx, .variable)
    simp only [idxBlock]
    omega
  · change ¬ idxBlock { start with vidx := start.vidx + 1 } finish (start.vidx, .variable)
    simp only [idxBlock]
    omega

/-- Advancing the compiler's next configuration moves the old current block
into the reserved set and splits the old future range at the new counters.
Appending blank globals leaves allocated indices and stamp maps unchanged. -/
theorem idxRangeRel_advance {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (oldState newState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (config next : Config) (count : Nat)
    (range : idxRangeRel interp genv nextType nextExn oldState (start, finish, other))
    (currentCfg : srcOracNextCfg interp oldState = some config)
    (nextCfg : srcOracNextCfg interp newState = some next)
    (prev : idxPrev config.next next.next) :
    idxRangeRel interp { genv with v := genv.v ++ List.replicate count none } nextType nextExn newState
      (config.next, next.next, idxBlock start finish ∪ other) := by
  obtain ⟨_, _, final, _, tuple, finalCfg, _, disjoint, types, exceptions⟩ := range
  cases tuple
  simp [currentCfg] at finalCfg
  subst final
  refine ⟨config.next, next.next, next.next, idxBlock start finish ∪ other,
    rfl, ?_, idxPrev_refl _, ?_, types, exceptions⟩
  · simp [nextCfg]
  · rw [genvAllocatedIndices_append_none]
    apply allDisjoint_four_advance (idxBlock start finish) (idxFinalBlock config.next)
      other (genvAllocatedIndices genv) (idxBlock config.next next.next) (idxFinalBlock next.next)
      disjoint
    · intro ⟨i, kind⟩ member
      cases kind <;> exact member.1
    · intro ⟨i, kind⟩ member
      cases kind with
      | «variable» => exact Nat.le_trans prev.1 member
      | «type» => exact Nat.le_trans prev.2.1 member
      | «exception» => exact Nat.le_trans prev.2.2 member
    · intro ⟨i, kind⟩ block future
      cases kind <;> exact (Nat.not_le_of_gt block.2) future

/-- The original index-range invariant reserves the block of blank globals
needed for the next declaration. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_range_rel_v_REPLICATE_NONE"
  (fmap_as_finite_support := [c, tys])]
theorem idxRangeRel_blank {C : Type} (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState) (start finish : NextIndices)
    (other : Set (Nat × IndexKind)) (count : Nat)
    (premises : idxRangeRel interp genv nextType nextExn evalState (start, finish, other) ∧
      finIdxMatch genv.v.length finish (srcOracNextCfg interp evalState) ∧
      count + start.vidx ≤ finish.vidx) :
    ∃ pre post, genv.v = pre ++ (List.replicate count none ++ post) ∧ pre.length = start.vidx := by
  obtain ⟨range, lengthMatch, fits⟩ := premises
  obtain ⟨i, e, final, rest, tuple, nextMatch, previous, disjoint, _, _⟩ := range
  cases tuple
  apply indexInvariant_blank_block genv start finish final other (srcOracNextCfg interp evalState) count
    previous nextMatch lengthMatch disjoint
  omega

/-- The original index-range relation supplies the reserved slots for the
factored declaration initialization. The full invariant's remaining oracle,
state, and index postconditions are still separate obligations. -/
theorem evaluate_makeVarls_idxRange {C F R : Type}
    (interp : Option (Value → Option (Config × R))) (genv : GlobalEnv)
    (sourceEnv : List (VarN × Value)) (flatEnv : List (VarN × FlatSem.Value))
    (related : EnvRel genv (Flapjack.NamespaceHOL.alistToNs sourceEnv) flatEnv)
    (distinct : (sourceEnv.map Prod.fst).Nodup)
    (sourceState : State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv sourceState.nextTypeStamp sourceState.nextExnStamp
      sourceState.evalState (start, finish, other))
    (lengthMatch : finIdxMatch genv.v.length finish (srcOracNextCfg interp sourceState.evalState))
    (fits : flatEnv.length + start.vidx ≤ finish.vidx) (n : Nat) (trace : BackendCommon.Tra) :
    ∃ pre post, pre.length = start.vidx ∧
      flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post) ∧
      let values := flatEnv.reverse.map Prod.snd
      let finalSlots := pre ++ (values.map some ++ post)
      let finalEnv := { genv with v := finalSlots }
      let finalState := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatEnv⟩ flatState
          [makeVarls n trace start.vidx (flatEnv.reverse.map Prod.fst)] =
          (finalState, .val [FlatSem.unitValue]) ∧
        GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
        GlobalEnvInv finalEnv
          { emptyEnv with v := Flapjack.NamespaceHOL.alistToNs (allocDefs n start.vidx (flatEnv.reverse.map Prod.fst)) }
          (fun _ => False) ⟨Flapjack.NamespaceHOL.alistToNs sourceEnv, Flapjack.NamespaceHOL.nsEmpty⟩ := by
  obtain ⟨pre, post, slots, size⟩ := idxRangeRel_blank interp genv sourceState.nextTypeStamp
    sourceState.nextExnStamp sourceState.evalState start finish other flatEnv.length ⟨range, lengthMatch, fits⟩
  have flatSlots : flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post) := globals.trans slots
  refine ⟨pre, post, size, flatSlots, ?_⟩
  simpa [size] using evaluate_makeVarls_globalEnvInv genv sourceEnv flatEnv related distinct sourceState flatState
    stateRel globals pre post flatSlots n trace

end OracleInvariant
end Flapjack.Compiler.Backend.SourceToFlat
