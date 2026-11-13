module

public import Flapjack.Compiler.Backend.BviToData.CompileSource
public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.BviSem.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Code and state relations for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- The data code tree has exactly the compiled bodies at the BVI labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "code_rel_def"]
def codeRel (bviCode : Spt (Nat × Bvi.Exp)) (dataCode : Spt (Nat × DataLang.Prog)) : Prop :=
  sptWf bviCode = true ∧ sptWf dataCode = true ∧
  sptDomain bviCode = sptDomain dataCode ∧
  ∀ label exp argc, sptLookup label bviCode = some (argc, exp) →
    sptLookup label dataCode = some (argc, compileExp argc exp)

/-- BVI's canonical finite-map carrier roundtrips through its broad view. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The source relation between BVI and data states; data locals and resource
accounting do not occur in this relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [BviState.refs])]
def stateRel {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F) : Prop :=
  source.clock = target.clock ∧ codeRel source.code target.code ∧
  target.compileOracle = (fun n => let (config, program) := source.compileOracle n; (config, compileProg program)) ∧
  source.compile = (fun config program => target.compile config (compileProg program)) ∧
  (∀ n, source.refs.lookup n = sptLookup n (sptMap dataToBviRef target.refs)) ∧
  source.ffi = target.ffi ∧ source.global = target.global

/-- The state relation ignores local-size and resource bookkeeping fields. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "state_rel_peak_safe"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem stateRel_peakSafe {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (safe : Bool) (peak : Nat) (localsSize stackMax : Option Nat) :
    stateRel source target ↔
      stateRel source { target with localsSize := localsSize, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } := by
  rfl

/-- Decrementing both related clocks preserves the state relation.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "state_rel_dec_clock" (fmap_as_finite_support_relation := [BviState.refs])] -/
theorem stateRel_decClock {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) : stateRel (BviSem.decClock 1 source) (DataSem.decClock target) := by
  rcases related with ⟨clocks, rest⟩
  simp only [stateRel, BviSem.decClock, DataSem.decClock]
  exact ⟨by rw [clocks], rest⟩

/-- Inserting corresponding references on both sides preserves the state
relation. This is Flapjack infrastructure for primitive simulations. -/
theorem stateRel_insertRef {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (key : Nat) (value : BvlSem.Ref DataSem.Value) :
    stateRel { source with refs := source.refs.updateEq (key, dataToBviRef value) }
      { target with refs := sptInsert key value target.refs } := by
  rcases related with ⟨clock, code, oracle, compiler, refs, ffi, global⟩
  refine ⟨clock, code, oracle, compiler, ?_, ffi, global⟩
  intro n
  rw [HolFiniteMapExact.lookup_updateEq, sptLookup_sptMap]
  by_cases same : n = key
  · subst n
    simp [FUPDATE_HOL, sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne key n value target.refs same]
    simp [FUPDATE_HOL, same, ← sptLookup_sptMap, refs]

end Flapjack.Compiler.Backend.BviToData
