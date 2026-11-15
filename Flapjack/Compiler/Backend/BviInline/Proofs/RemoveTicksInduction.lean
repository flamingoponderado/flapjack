module

public import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksCalls

@[expose] public section

/-! Assembly of the BVI tick-removal evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

namespace TickSimulationCarrier
/-- The BVI reference-map representation has a canonical roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end TickSimulationCarrier

/-- A positive clock bounded by a limit becomes strictly smaller after one tick. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "clock_sub_lt"]
theorem clockSubLt (x clock : Nat) (premises : x ≠ 0 ∧ x ≤ clock) : x - 1 < clock := by
  omega

/-- A non-timeout evaluation remains stable when another clock increment is
added. The evaluator inherits the real-model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_add_extra_clock"
  (fmap_as_finite_support := [refs])]
theorem evaluateAddExtraClock {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) (result : BviResult) (next : BviState C F) (extra more : Nat)
    (premises : evaluateTuple (expressions, env, { state with clock := extra + state.clock }) = (result, next) ∧
      result ≠ .err (.abort .timeoutError)) :
    evaluateTuple (expressions, env, { state with clock := extra + more + state.clock }) =
      (result, { next with clock := more + next.clock }) := by
  obtain ⟨run, notTimeout⟩ := premises
  have shifted := BviProps.evaluate_addClock expressions env { state with clock := extra + state.clock }
    next result more run notTimeout
  simpa [evaluateTuple, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shifted

/-- Flapjack infrastructure: smaller expression induction hypothesis. -/
def SmallerWeight {C F : Type} (clock weight : Nat) : Prop :=
  ∀ (xs : List Bvi.Exp) (env : List Value) (state : BviState C F),
    state.clock ≤ clock → expsWeight xs < weight → Property xs env state

/-- Flapjack infrastructure: smaller clock induction hypothesis. -/
def SmallerClock {C F : Type} (clock : Nat) : Prop :=
  ∀ (xs : List Bvi.Exp) (env : List Value) (state : BviState C F),
    state.clock < clock → Property xs env state

/-- Flapjack infrastructure: all evaluator cases follow from the structural
and clock induction hypotheses. -/
theorem step {C F : Type} (xs : List Bvi.Exp) (env : List Value) (state : BviState C F)
    (weightIH : SmallerWeight (C := C) (F := F) state.clock (expsWeight xs))
    (clockIH : SmallerClock (C := C) (F := F) state.clock) : Property xs env state := by
  cases xs with
  | nil =>
    intro source result targetNext states run
    simp [removeTicksListSource, evaluate] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate], states⟩
  | cons e rest =>
    cases rest with
    | cons second rest =>
      have headWeight : expsWeight [e] < expsWeight (e :: second :: rest) := by
        simp only [expsWeight]
        have pos := BviSem.expWeight_pos second
        omega
      have tailWeight : expsWeight (second :: rest) < expsWeight (e :: second :: rest) := by
        simp only [expsWeight]
        omega
      apply consCons e second rest env state (weightIH [e] env state (Nat.le_refl _) headWeight)
      intro values next run
      have clock := evaluate_clock_le [removeTicksSource e] env state
      rw [run] at clock
      exact weightIH (second :: rest) env next clock tailWeight
    | nil =>
      cases e with
      | var index =>
        intro source result targetNext states run
        cases found : env[index]? <;> simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
        all_goals obtain ⟨rfl, rfl⟩ := run.symm
        all_goals exact ⟨0, source, by simp [evaluate, found], states⟩
      | force location index =>
        apply force location index env state
        intro args body nonzero
        apply clockIH [body] args (BviSem.decClock 1 state)
        simp [BviSem.decClock]
        omega
      | tick body =>
        apply tick body env state
        apply weightIH [body] env state (Nat.le_refl _)
        simp [expsWeight, expWeight]
      | raise body =>
        apply raiseExp body env state
        apply weightIH [body] env state (Nat.le_refl _)
        simp [expsWeight, expWeight]
      | «return» args =>
        apply returnExp args env state
        apply weightIH args env state (Nat.le_refl _)
        simp [expsWeight, expWeight]
        omega
      | op operator args =>
        apply op operator args env state
        apply weightIH args env state (Nat.le_refl _)
        simp [expsWeight, expWeight]
        omega
      | «let» bindings body =>
        have bindingsWeight : expsWeight bindings < expsWeight [.let bindings body] := by
          simp [expsWeight, expWeight]; omega
        have bodyWeight : expsWeight [body] < expsWeight [.let bindings body] := by
          simp [expsWeight, expWeight]; omega
        apply letExp bindings body env state (weightIH bindings env state (Nat.le_refl _) bindingsWeight)
        intro values next run
        have clock := evaluate_clock_le (removeTicksListSource bindings) env state
        rw [run] at clock
        exact weightIH [body] (values ++ env) next clock bodyWeight
      | ifThenElse condition yes no =>
        have conditionWeight : expsWeight [condition] < expsWeight [.ifThenElse condition yes no] := by
          simp [expsWeight, expWeight]; omega
        have yesWeight : expsWeight [yes] < expsWeight [.ifThenElse condition yes no] := by
          simp [expsWeight, expWeight]; omega
        have noWeight : expsWeight [no] < expsWeight [.ifThenElse condition yes no] := by
          simp [expsWeight, expWeight]; omega
        apply ifThenElse condition yes no env state (weightIH [condition] env state (Nat.le_refl _) conditionWeight)
        intro value next run
        have clock := evaluate_clock_le [removeTicksSource condition] env state
        rw [run] at clock
        exact ⟨weightIH [yes] env next clock yesWeight, weightIH [no] env next clock noWeight⟩
      | call ticks destination args handler =>
        have argsWeight : expsWeight args < expsWeight [.call ticks destination args handler] := by
          cases handler <;> simp [expsWeight, expWeight] <;> omega
        have calleeIH : ∀ values next, evaluate (removeTicksListSource args) env state = (.val values, next) →
            ∀ callArgs body, BvlSem.findCode destination values next.code = some (callArgs, removeTicksSource body) →
              next.clock ≠ 0 → Property [body] callArgs (BviSem.decClock 1 next) := by
          intro values next run callArgs body _ nonzero
          have clock := evaluate_clock_le (removeTicksListSource args) env state
          rw [run] at clock
          simp only at clock
          apply clockIH [body] callArgs (BviSem.decClock 1 next)
          simp [BviSem.decClock]
          omega
        cases handler with
        | none => exact callNone ticks destination args env state (weightIH args env state (Nat.le_refl _) argsWeight) calleeIH
        | some handler =>
          cases destination with
          | none =>
            intro source result next states run
            simp [removeTicksListSource, removeTicksSource, evaluate] at run
            obtain ⟨rfl, rfl⟩ := run.symm
            exact ⟨0, source, by simp [evaluate], states⟩
          | some destination =>
            have handlerWeight : expsWeight [handler] < expsWeight [.call ticks (some destination) args (some handler)] := by
              simp [expsWeight, expWeight]; omega
            apply callSome ticks destination args handler env state
              (weightIH args env state (Nat.le_refl _) argsWeight) calleeIH
            intro value next clock
            exact weightIH [handler] (value :: env) next clock handlerWeight
      | letCall rets ticks destination args body =>
        have argsWeight : expsWeight args < expsWeight [.letCall rets ticks destination args body] := by
          simp [expsWeight, expWeight]; omega
        have bodyWeight : expsWeight [body] < expsWeight [.letCall rets ticks destination args body] := by
          simp [expsWeight, expWeight]; omega
        apply letCall rets ticks destination args body env state
          (weightIH args env state (Nat.le_refl _) argsWeight)
        · intro values next run callArgs callee _ nonzero
          have clock := evaluate_clock_le (removeTicksListSource args) env state
          rw [run] at clock
          simp only at clock
          apply clockIH [callee] callArgs (BviSem.decClock 1 next)
          simp [BviSem.decClock]
          omega
        · intro values next clock
          exact weightIH [body] (values ++ env) next clock bodyWeight

/-- Every tick-cleaned evaluation is simulated by the original expression
list with an additional clock and related final states. The evaluator inherits
the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs])]
theorem evaluate_removeTicks {C F : Type} (clock : Nat) (xs : List Bvi.Exp) (env : List Value)
    (target source : BviState C F) (result : BviResult) (targetNext : BviState C F)
    (premises : RemoveStateRel source target ∧ target.clock = clock ∧
      evaluateTuple (removeTicksListSource xs, env, target) = (result, targetNext)) :
    ∃ extra sourceNext,
      evaluateTuple (xs, env, { source with clock := source.clock + extra }) = (result, sourceNext) ∧
        RemoveStateRel sourceNext targetNext := by
  have all : ∀ clock weight, ∀ (xs : List Bvi.Exp) (env : List Value) (state : BviState C F),
      state.clock ≤ clock → expsWeight xs ≤ weight → Property xs env state := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock clockIH =>
      intro weight
      induction weight using Nat.strong_induction_on with
      | h weight weightIH =>
        intro xs env state clockBound weightBound
        have smallerClock : SmallerClock (C := C) (F := F) state.clock := by
          intro ys a s lt
          have earlier : s.clock < clock := by omega
          exact clockIH s.clock earlier (expsWeight ys) ys a s (Nat.le_refl _) (Nat.le_refl _)
        have smallerWeight : SmallerWeight (C := C) (F := F) state.clock (expsWeight xs) := by
          intro ys a s bound smaller
          by_cases earlier : s.clock < clock
          · exact clockIH s.clock earlier (expsWeight ys) ys a s (Nat.le_refl _) (Nat.le_refl _)
          · have lessWeight : expsWeight ys < weight := by omega
            exact weightIH (expsWeight ys) lessWeight ys a s (by omega) (Nat.le_refl _)
        exact step xs env state smallerWeight smallerClock
  obtain ⟨states, _, run⟩ := premises
  exact all target.clock (expsWeight xs) xs env target (Nat.le_refl _) (Nat.le_refl _)
    source result targetNext states run

/-- Clock-bounded singleton and list simulations for tick removal. The
evaluator inherits the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_remove_ticks_mutual"
  (fmap_as_finite_support := [refs])]
theorem evaluateRemoveTicksMutual {C F : Type} (clock : Nat) :
    (∀ (expression : Bvi.Exp) (env : List Value) (target source : BviState C F)
        (result : BviResult) (targetNext : BviState C F),
      RemoveStateRel source target ∧ target.clock ≤ clock ∧
        evaluateTuple ([removeTicksSource expression], env, target) = (result, targetNext) →
      ∃ extra sourceNext,
        evaluateTuple ([expression], env, { source with clock := source.clock + extra }) =
          (result, sourceNext) ∧ RemoveStateRel sourceNext targetNext) ∧
    (∀ (expressions : List Bvi.Exp) (env : List Value) (target source : BviState C F)
        (result : BviResult) (targetNext : BviState C F),
      RemoveStateRel source target ∧ target.clock ≤ clock ∧
        evaluateTuple (removeTicksListSource expressions, env, target) = (result, targetNext) →
      ∃ extra sourceNext,
        evaluateTuple (expressions, env, { source with clock := source.clock + extra }) =
          (result, sourceNext) ∧ RemoveStateRel sourceNext targetNext) := by
  constructor
  · intro expression env target source result targetNext ⟨states, _, run⟩
    apply evaluate_removeTicks target.clock [expression] env target source result targetNext
    exact ⟨states, rfl, by simpa [removeTicksListSource] using run⟩
  · intro expressions env target source result targetNext ⟨states, _, run⟩
    exact evaluate_removeTicks target.clock expressions env target source result targetNext ⟨states, rfl, run⟩

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
