import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksCalls

/-! Assembly of the BVI tick-removal evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

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
  | nil => exact nil env state
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
      | var index => exact var index env state
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

/-- Flapjack infrastructure: every tick-cleaned expression list can be
simulated by the original list with some extra clock and related states. The
HOL evaluator and carrier comparison remains pending. -/
theorem evaluate_removeTicks {C F : Type} (xs : List Bvi.Exp) (env : List Value)
    (target : BviState C F) : Property xs env target := by
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
  exact all target.clock (expsWeight xs) xs env target (Nat.le_refl _) (Nat.le_refl _)

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
