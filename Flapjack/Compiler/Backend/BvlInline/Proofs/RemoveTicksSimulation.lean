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

/-- The nonempty-list case composes head and tail simulations, extending the
successful head's clock to accommodate the tail. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_cons {C F : Type} (clock : Nat) (first second : Bvl.Exp) (tail : List Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (headIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks [first], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([first], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (tailIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock ≤ clock → evaluateTuple (removeTicks (second :: tail), env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple (second :: tail, env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks (first :: second :: tail), env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple (first :: second :: tail, env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, evaluateTuple] at run
  rw [evaluate, fixClock_evaluate] at run
  cases headRun : evaluate [removeTicksSing first] env s with
  | mk headResult headFinal =>
    rw [headRun] at run
    have bound : headFinal.clock ≤ clock := by
      have h := evaluate_clock_le [removeTicksSing first] env s
      simpa [headRun, clockEq] using h
    have headRunTuple : evaluateTuple (removeTicks [first], env, s) = (headResult, headFinal) := by
      simpa [removeTicks, removeTicksList, evaluateTuple] using headRun
    obtain ⟨headExtra, sourceHeadFinal, sourceHeadRun, headRel⟩ :=
      headIH s t headFinal headResult related clockEq headRunTuple
    change evaluate [first] env { t with clock := t.clock + headExtra } = _ at sourceHeadRun
    cases headResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨headExtra, sourceHeadFinal, ?_, headRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, sourceHeadRun]
    | val values =>
      cases tailRun : evaluate (removeTicksList (second :: tail)) env headFinal with
      | mk tailResult tailFinal =>
        dsimp only at run
        simp only [removeTicksList] at tailRun
        rw [tailRun] at run
        have tailRunTuple : evaluateTuple (removeTicks (second :: tail), env, headFinal) =
            (tailResult, tailFinal) := by simpa [removeTicks, removeTicksList, evaluateTuple] using tailRun
        obtain ⟨tailExtra, sourceTailFinal, sourceTailRun, tailRel⟩ :=
          tailIH headFinal sourceHeadFinal tailFinal tailResult headRel bound tailRunTuple
        have headShift := evaluate_addClock [first] env { t with clock := t.clock + headExtra }
          sourceHeadFinal (.val values) tailExtra sourceHeadRun (by simp)
        have headShift' : evaluate [first] env { t with clock := t.clock + (headExtra + tailExtra) } =
            (.val values, { sourceHeadFinal with clock := sourceHeadFinal.clock + tailExtra }) := by
          simpa [Nat.add_assoc] using headShift
        change evaluate (second :: tail) env
          { sourceHeadFinal with clock := sourceHeadFinal.clock + tailExtra } = _ at sourceTailRun
        refine ⟨headExtra + tailExtra, sourceTailFinal, ?_, ?_⟩
        · rw [evaluateTuple, evaluate, fixClock_evaluate, headShift', sourceTailRun]
          cases tailResult <;> simp_all
        · cases tailResult <;> simp_all

/-- Let-bindings compose binding and body simulations with a shared clock. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_let {C F : Type} (clock : Nat) (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (bindingsIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks bindings, env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple (bindings, env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (bodyIH : ∀ (bodyEnv : List BvlSem.Value) (s t final : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value), stateRel t s → s.clock ≤ clock →
      evaluateTuple (removeTicks [body], bodyEnv, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([body], bodyEnv, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.let bindings body], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.let bindings body], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate (removeTicksList bindings) env s with
  | mk bindingsResult bindingsFinal =>
    rw [bindingsRun] at run
    have bound : bindingsFinal.clock ≤ clock := by
      have h := evaluate_clock_le (removeTicksList bindings) env s
      simpa [bindingsRun, clockEq] using h
    have bindingsRunTuple : evaluateTuple (removeTicks bindings, env, s) = (bindingsResult, bindingsFinal) := by
      simpa [removeTicks, evaluateTuple] using bindingsRun
    obtain ⟨bindingsExtra, sourceBindingsFinal, sourceBindingsRun, bindingsRel⟩ :=
      bindingsIH s t bindingsFinal bindingsResult related clockEq bindingsRunTuple
    change evaluate bindings env { t with clock := t.clock + bindingsExtra } = _ at sourceBindingsRun
    cases bindingsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨bindingsExtra, sourceBindingsFinal, ?_, bindingsRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, sourceBindingsRun]
    | val values =>
      have bodyRun : evaluateTuple (removeTicks [body], values ++ env, bindingsFinal) = (result, final) := by
        simpa [removeTicks, removeTicksList, evaluateTuple] using run
      obtain ⟨bodyExtra, sourceFinal, sourceBodyRun, finalRel⟩ :=
        bodyIH (values ++ env) bindingsFinal sourceBindingsFinal final result bindingsRel bound bodyRun
      have shifted := evaluate_addClock bindings env { t with clock := t.clock + bindingsExtra }
        sourceBindingsFinal (.val values) bodyExtra sourceBindingsRun (by simp)
      have shifted' : evaluate bindings env { t with clock := t.clock + (bindingsExtra + bodyExtra) } =
          (.val values, { sourceBindingsFinal with clock := sourceBindingsFinal.clock + bodyExtra }) := by
        simpa [Nat.add_assoc] using shifted
      change evaluate [body] (values ++ env)
        { sourceBindingsFinal with clock := sourceBindingsFinal.clock + bodyExtra } = _ at sourceBodyRun
      refine ⟨bindingsExtra + bodyExtra, sourceFinal, ?_, finalRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, shifted']
      exact sourceBodyRun

/-- Handler simulation carries a raised value into the simulated handler. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_handle {C F : Type} (clock : Nat) (body handler : Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks [body], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([body], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (handlerIH : ∀ (handlerEnv : List BvlSem.Value) (s t final : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value), stateRel t s → s.clock ≤ clock →
      evaluateTuple (removeTicks [handler], handlerEnv, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([handler], handlerEnv, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.handle body handler], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.handle body handler], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [removeTicksSing body] env s with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at run
    have bound : bodyFinal.clock ≤ clock := by
      have h := evaluate_clock_le [removeTicksSing body] env s
      simpa [bodyRun, clockEq] using h
    have bodyRunTuple : evaluateTuple (removeTicks [body], env, s) = (bodyResult, bodyFinal) := by
      simpa [removeTicks, removeTicksList, evaluateTuple] using bodyRun
    obtain ⟨bodyExtra, sourceBodyFinal, sourceBodyRun, bodyRel⟩ :=
      bodyIH s t bodyFinal bodyResult related clockEq bodyRunTuple
    change evaluate [body] env { t with clock := t.clock + bodyExtra } = _ at sourceBodyRun
    cases bodyResult with
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨bodyExtra, sourceBodyFinal, ?_, bodyRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, sourceBodyRun]
    | err error =>
      cases error with
      | abort reason =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨bodyExtra, sourceBodyFinal, ?_, bodyRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, sourceBodyRun]
      | raise value =>
        have handlerRun : evaluateTuple (removeTicks [handler], value :: env, bodyFinal) = (result, final) := by
          simpa [removeTicks, removeTicksList, evaluateTuple] using run
        obtain ⟨handlerExtra, sourceFinal, sourceHandlerRun, finalRel⟩ :=
          handlerIH (value :: env) bodyFinal sourceBodyFinal final result bodyRel bound handlerRun
        have shifted := evaluate_addClock [body] env { t with clock := t.clock + bodyExtra }
          sourceBodyFinal (.err (.raise value)) handlerExtra sourceBodyRun (by simp)
        have shifted' : evaluate [body] env { t with clock := t.clock + (bodyExtra + handlerExtra) } =
            (.err (.raise value), { sourceBodyFinal with clock := sourceBodyFinal.clock + handlerExtra }) := by
          simpa [Nat.add_assoc] using shifted
        change evaluate [handler] (value :: env)
          { sourceBodyFinal with clock := sourceBodyFinal.clock + handlerExtra } = _ at sourceHandlerRun
        refine ⟨bodyExtra + handlerExtra, sourceFinal, ?_, finalRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, shifted']
        exact sourceHandlerRun

/-- Conditional simulation follows the selected simulated branch. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicks_if {C F : Type} (clock : Nat) (condition yes no : Bvl.Exp)
    (env : List BvlSem.Value) (s t final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (conditionIH : ∀ (s t final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      stateRel t s → s.clock = clock → evaluateTuple (removeTicks [condition], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([condition], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (branchIH : ∀ (choice : Bool) (s t final : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value), stateRel t s → s.clock ≤ clock →
      evaluateTuple (removeTicks [if choice then yes else no], env, s) = (result, final) →
      ∃ extra sourceFinal, evaluateTuple ([if choice then yes else no], env, { t with clock := t.clock + extra }) =
        (result, sourceFinal) ∧ stateRel sourceFinal final)
    (related : stateRel t s) (clockEq : s.clock = clock)
    (run : evaluateTuple (removeTicks [.ifThenElse condition yes no], env, s) = (result, final)) :
    ∃ extra sourceFinal, evaluateTuple ([.ifThenElse condition yes no], env, { t with clock := t.clock + extra }) =
      (result, sourceFinal) ∧ stateRel sourceFinal final := by
  simp only [removeTicks, removeTicksList, removeTicksSing, evaluateTuple] at run
  rw [evaluate, fixClock_evaluate] at run
  cases conditionRun : evaluate [removeTicksSing condition] env s with
  | mk conditionResult conditionFinal =>
    rw [conditionRun] at run
    have bound : conditionFinal.clock ≤ clock := by
      have h := evaluate_clock_le [removeTicksSing condition] env s
      simpa [conditionRun, clockEq] using h
    have conditionRunTuple : evaluateTuple (removeTicks [condition], env, s) = (conditionResult, conditionFinal) := by
      simpa [removeTicks, removeTicksList, evaluateTuple] using conditionRun
    obtain ⟨conditionExtra, sourceConditionFinal, sourceConditionRun, conditionRel⟩ :=
      conditionIH s t conditionFinal conditionResult related clockEq conditionRunTuple
    change evaluate [condition] env { t with clock := t.clock + conditionExtra } = _ at sourceConditionRun
    cases conditionResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨conditionExtra, sourceConditionFinal, ?_, conditionRel⟩
      rw [evaluateTuple, evaluate, fixClock_evaluate, sourceConditionRun]
    | val values =>
      change (match asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
        | none => (.err (.abort .typeError), conditionFinal)
        | some true => evaluate [removeTicksSing yes] env conditionFinal
        | some false => evaluate [removeTicksSing no] env conditionFinal) = (result, final) at run
      cases test : asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
      | none =>
        simp [test] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨conditionExtra, sourceConditionFinal, ?_, conditionRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, sourceConditionRun]
        change (match asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
          | none => ((Result.err (.abort .typeError) : Result (List BvlSem.Value) BvlSem.Value), sourceConditionFinal)
          | some true => evaluate [yes] env sourceConditionFinal
          | some false => evaluate [no] env sourceConditionFinal) = _
        simp [test]
      | some choice =>
        have branchRun : evaluateTuple (removeTicks [if choice then yes else no], env, conditionFinal) =
            (result, final) := by
          cases choice <;> simpa [test, removeTicks, removeTicksList, evaluateTuple] using run
        obtain ⟨branchExtra, sourceFinal, sourceBranchRun, finalRel⟩ :=
          branchIH choice conditionFinal sourceConditionFinal final result conditionRel bound branchRun
        have shifted := evaluate_addClock [condition] env { t with clock := t.clock + conditionExtra }
          sourceConditionFinal (.val values) branchExtra sourceConditionRun (by simp)
        have shifted' : evaluate [condition] env { t with clock := t.clock + (conditionExtra + branchExtra) } =
            (.val values, { sourceConditionFinal with clock := sourceConditionFinal.clock + branchExtra }) := by
          simpa [Nat.add_assoc] using shifted
        change evaluate [if choice then yes else no] env
          { sourceConditionFinal with clock := sourceConditionFinal.clock + branchExtra } = _ at sourceBranchRun
        refine ⟨conditionExtra + branchExtra, sourceFinal, ?_, finalRel⟩
        rw [evaluateTuple, evaluate, fixClock_evaluate, shifted']
        change (match asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
          | none => ((Result.err (.abort .typeError) : Result (List BvlSem.Value) BvlSem.Value), { sourceConditionFinal with clock := sourceConditionFinal.clock + branchExtra })
          | some true => evaluate [yes] env { sourceConditionFinal with clock := sourceConditionFinal.clock + branchExtra }
          | some false => evaluate [no] env { sourceConditionFinal with clock := sourceConditionFinal.clock + branchExtra }) = _
        cases choice <;> simpa [test] using sourceBranchRun

end Flapjack.Compiler.Backend.BvlInline.Proofs
