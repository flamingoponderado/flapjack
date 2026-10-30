import Flapjack.Compiler.Backend.BvlInline.Proofs.ApplySimulation
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Case factoring for the BVL tick-removal evaluator simulation. The full
source theorem remains open until all cases are assembled. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

namespace EvaluationSimulationCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvaluationSimulationCarrier

/-- The empty-list simulation case. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_nil {C F : Type} (clock : Nat) (env : List BvlSem.Value)
    (s t final : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : stateRel t s) (_clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp [removeTicks, removeTicksList, evaluateTuple, evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨0, t, by simp [evaluateTuple, evaluate], related⟩

/-- The variable simulation case. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_var {C F : Type} (clock index : Nat) (env : List BvlSem.Value)
    (s t final : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : stateRel t s) (_clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.var index], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.var index], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  cases found : env[index]? <;> simp [evaluate, found] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals exact ⟨0, t, by simp [evaluateTuple, evaluate, found], related⟩

/-- The tick case follows from the body simulation with one extra tick. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_tick {C F : Type} (clock : Nat) (body : Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks [body], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([body], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.tick body], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.tick body], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  have bodyRun : evaluateTuple (removeTicks [body], env, s) = (result, final) := by
    simpa [removeTicks, removeTicksList, removeTicksSing] using run
  obtain ⟨extra, sourceFinal, bodyRun, finalRel⟩ := bodyIH s t final result related clockEq bodyRun
  refine ⟨extra + 1, sourceFinal, ?_, finalRel⟩
  have nonzero : t.clock + (extra + 1) ≠ 0 := by omega
  have dec : decClock 1 { t with clock := t.clock + (extra + 1) } =
      { t with clock := t.clock + extra } := by
    simp only [decClock]
    congr 1
  simpa [evaluateTuple, evaluate, nonzero, dec] using bodyRun

/-- The raise case preserves either the operand error or its raised value. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_raise {C F : Type} (clock : Nat) (body : Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks [body], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([body], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.raise body], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.raise body], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  rw [evaluate] at run
  cases bodyRun : evaluate [removeTicksSing body] env s with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at run
    have bodyRunTuple : evaluateTuple (removeTicks [body], env, s) = (bodyResult, bodyFinal) := by
      simpa [removeTicks, removeTicksList, evaluateTuple] using bodyRun
    obtain ⟨extra, sourceFinal, sourceRun, finalRel⟩ := bodyIH s t bodyFinal bodyResult related clockEq bodyRunTuple
    refine ⟨extra, sourceFinal, ?_, ?_⟩
    · rw [evaluateTuple, evaluate]
      change evaluate [body] env { t with clock := t.clock + extra } = _ at sourceRun
      rw [sourceRun]
      cases bodyResult <;> simp_all
    · cases bodyResult <;> simp_all

/-- The operator case uses the argument simulation and the full primitive
simulation, including dynamic installation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_op {C F : Type} (clock : Nat) (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (argsIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks args, env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple (args, env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.op op args], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.op op args], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate (removeTicksList args) env s with
  | mk argsResult argsFinal =>
    rw [argsRun] at run
    have argsRunTuple : evaluateTuple (removeTicks args, env, s) = (argsResult, argsFinal) := by
      simpa [removeTicks, evaluateTuple] using argsRun
    obtain ⟨extra, sourceArgsFinal, sourceArgsRun, argsRel⟩ :=
      argsIH s t argsFinal argsResult related clockEq argsRunTuple
    change evaluate args env { t with clock := t.clock + extra } = _ at sourceArgsRun
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨extra, sourceArgsFinal, ?_, argsRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, sourceArgsRun]
    | val values =>
      have simulated := doAppLemma sourceArgsFinal argsFinal argsRel op values
      cases appRun : doApp op values.reverse argsFinal with
      | err error =>
        simp [appRun] at run simulated
        rcases run with ⟨rfl, rfl⟩
        refine ⟨extra, sourceArgsFinal, ?_, argsRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, sourceArgsRun]
        simp [simulated]
      | val pair =>
        obtain ⟨value, next⟩ := pair
        simp [appRun] at run simulated
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨sourceFinal, finalRel, sourceApp⟩ := simulated
        refine ⟨extra, sourceFinal, ?_, finalRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, sourceArgsRun]
        simp [sourceApp]

end Flapjack.Compiler.Backend.BvlInline.Proofs
