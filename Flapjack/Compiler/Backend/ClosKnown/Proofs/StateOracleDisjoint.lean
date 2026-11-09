import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleMonotonic
import Flapjack.Compiler.Backend.ClosKnown.Proofs.EvaluateGlobalsTotal

/-! Disjointness of initialized globals and future oracle writes. -/
namespace Flapjack.Compiler.Backend.ClosKnown.StateOracleDisjoint
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- Initialized globals are disjoint from each future oracle program. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_oracle_mglobals_disjoint_def"
  (fmap_as_finite_support := [refs, code])]
def stateOracleMglobalsDisjoint {C F : Type} (s : State C F) : Prop :=
  ∀ n, mglobalsDisjoint s.globals (s.compileOracle n).2.1

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- A future write in a unique oracle cannot also occur in the initial program
or an already-consumed oracle prefix. This is Flapjack induction infrastructure. -/
private theorem futureWritesSeparate {A B : Type} (xs : List ClosLang.Exp)
    (co : Nat → A × List ClosLang.Exp × B) (consumed i key : Nat)
    (unique : uniqueSetGlobals xs co)
    (future : elistGlobals (co (i + consumed)).2.1 key ≠ 0) :
    elistGlobals xs key = 0 ∧ elistGlobals (List.flatten (firstNExps co consumed)) key = 0 := by
  have shifted : elistGlobals ((Flapjack.holShiftSeq consumed co) i).2.1 key ≠ 0 := future
  have later := elistGlobalsFirstNExps key i (Flapjack.holShiftSeq consumed co) shifted (i + 1) (by omega)
  have bound := unique (consumed + (i + 1)) key
  rw [elistGlobals_append, Nat.add_comm consumed (i + 1), firstNExpsShiftSeq co (i + 1) consumed] at bound
  simp only [List.flatten_append, elistGlobals_append] at bound
  omega

/-- Safe evaluation preserves disjointness of initialized globals from every
future oracle program. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_oracle_mglobals_disjoint_evaluate_suff"
  (fmap_as_finite_support := [refs, code])]
theorem stateOracleMglobalsDisjointEvaluate {C F : Type} (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F)
    (h : evaluate xs env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ xs, esgcFree e) ∧ (∀ v ∈ env, vsgcFree v) ∧
      uniqueSetGlobals xs s0.compileOracle ∧ mglobalsDisjoint s0.globals xs ∧
      stateOracleMglobalsDisjoint s0) : stateOracleMglobalsDisjoint s := by
  rcases h with ⟨run, safe, exprSafe, envSafe, unique, _, oldDisjoint⟩
  obtain ⟨_, _, consumed, oracle, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env s0 res s ⟨run, safe, exprSafe, envSafe⟩
  intro i
  apply Set.disjoint_left.mpr
  intro key mapped written
  have future : elistGlobals (s0.compileOracle (i + consumed)).2.1 key ≠ 0 := by
    simpa [oracle, Flapjack.holShiftSeq] using written
  have separate := futureWritesSeparate xs s0.compileOracle consumed i key unique future
  rcases frame.1 mapped with old | changed
  · exact (Set.disjoint_left.mp (oldDisjoint (i + consumed))) old future
  · rcases changed with programWrite | priorWrite
    · exact programWrite separate.1
    · exact priorWrite separate.2

end Flapjack.Compiler.Backend.ClosKnown.StateOracleDisjoint
