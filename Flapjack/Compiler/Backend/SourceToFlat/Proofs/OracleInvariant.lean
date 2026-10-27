import Flapjack.Compiler.Backend.SourceToFlat.Proofs.IndexInvariant

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
