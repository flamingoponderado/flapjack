import Flapjack.Compiler.Backend.BviTmc.Proofs.HeapRelation
import Flapjack.Compiler.Backend.Semantics.BviSem.State
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! State relation for TMC evaluation and compiler callbacks. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BviSem

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The source state relation tracks pointer renaming, code, namespaces,
and future compilation obligations. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
def stateRel {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) : Prop :=
  stateRefRel f source.refs target.refs ∧
  target.clock = source.clock ∧
  (match source.global, target.global with
   | none, none => True
   | some p, some q => f.lookup p = some q
   | _, _ => False) ∧
  target.ffi = source.ffi ∧
  target.compileOracle = BackendProps.stateCo compileEachSource source.compileOracle ∧
  source.compile = BackendProps.stateCc compileEachSource target.compile ∧
  codeRel source.code target.code ∧
  namespaceRel source.code target.code ∧
  (∀ n, inputCondition (source.compileOracle n).1.1 (source.compileOracle n).2) ∧
  (∀ n, sptMem n target.code ∧ inWorkerNamespace n → n < (source.compileOracle 0).1.1) ∧
  fmapInj f

/-- Clock replacement preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem stateRel_with_clock {C F : Type} (n : Nat) (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (related : stateRel f source target) :
    stateRel f { source with clock := n } { target with clock := n } := by
  exact ⟨related.1, rfl, related.2.2⟩

/-- Equal clock decrements preserve the state relation under the source
clock side conditions. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_dec"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem stateRel_dec {C F : Type} (n t : Nat) (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (related : stateRel f source target) (sourceClock : source.clock = n + 1)
    (targetClock : target.clock = n + 1) (_bound : t ≤ n + 1) :
    stateRel f (BviSem.decClock t source) (BviSem.decClock t target) := by
  simpa [BviSem.decClock, sourceClock, targetClock] using stateRel_with_clock (n + 1 - t) f source target related

/-- The state relation contains the original code relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_code_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem stateRel_codeRel {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (related : stateRel f source target) :
    codeRel source.code target.code := related.2.2.2.2.2.2.1

/-- Updating a target reference outside the pointer-map range preserves the
state relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_filled"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem stateRel_filled {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (key : Nat) (value : BvlSem.Ref BvlSem.Value)
    (related : stateRel f source target) (fresh : ∀ i, f.lookup i ≠ some key) :
    stateRel f source { target with refs := target.refs.updateEq (key, value) } := by
  exact ⟨stateRefRel_filled f source.refs target.refs key value related.1 fresh, related.2⟩

/-- Flapjack installation helper: disjoint source and transformed code can be
installed together while both compiler oracles advance. -/
theorem stateRel_install_code_and_oracle {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (related : stateRel f source target)
    (sourceAbsent : ∀ n ∈ ((source.compileOracle 0).2.map Prod.fst), ¬sptMem n source.code)
    (nextEq : (source.compileOracle 1).1.1 =
      (compileEachSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).1) :
    stateRel f
      { source with code := sptUnion source.code (sptFromAList (source.compileOracle 0).2), compileOracle := fun n => source.compileOracle (n + 1) }
      { target with code := sptUnion target.code (sptFromAList
          (compileEachSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2), compileOracle := fun n => target.compileOracle (n + 1) } := by
  rcases related with ⟨heap, clock, global, ffi, oracle, compiler, oldCode, oldNames, conditions, workerBound, injective⟩
  let next := (source.compileOracle 0).1.1
  let code := (source.compileOracle 0).2
  have condition : inputCondition next code := conditions 0
  obtain ⟨newCode, newNames, _⟩ := compileEachSource_install_relations next code condition
  have disjoint := compileEachSource_install_disjoint next code source.code target.code condition oldNames workerBound sourceAbsent
  have bounds := compileEachSource_install_worker_bound next code condition
  let result := compileEachSource next code
  have run : compileEachSource next code = (result.1, result.2) := by exact (Prod.eta result).symm
  obtain ⟨steps, advance⟩ := compileEachSource_next_mono next result.1 code result.2 run
  have nextMono : next ≤ result.1 := by rw [advance]; omega
  refine ⟨heap, clock, global, ffi, ?_, compiler, ?_, ?_, ?_, ?_, injective⟩
  · funext n
    change target.compileOracle (n + 1) = BackendProps.stateCo compileEachSource (fun n => source.compileOracle (n + 1)) n
    rw [oracle]
    rfl
  · exact codeRel_union _ _ _ _ oldCode newCode disjoint
  · exact namespaceRel_union _ _ _ _ oldNames newNames disjoint
  · intro n
    exact conditions (n + 1)
  · intro n ⟨member, worker⟩
    change n < (source.compileOracle 1).1.1
    rw [nextEq]
    change n < result.1
    change sptMem n (sptUnion target.code (sptFromAList result.2)) at member
    rw [sptMem_sptUnion] at member
    rcases member with old | new
    · have oldBound := workerBound n ⟨old, worker⟩
      omega
    · exact bounds n ⟨new, worker⟩

end Flapjack.Compiler.Backend.BviTmc
