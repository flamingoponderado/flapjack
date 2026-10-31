import Flapjack.Compiler.Backend.BviInline.Proofs.ExpandEnv

/-! Assembly of BVI environment-extension cases. -/
namespace Flapjack.Compiler.Backend.BviInline.ExpandEnv
open BviSem BvlSem

/-- Flapjack infrastructure: same-clock structural induction hypothesis for
environment extension. -/
def SmallerWeight {C F : Type} (clock weight : Nat) : Prop :=
  ∀ (xs : List Bvi.Exp) (env : List Value) (state : BviState C F),
    state.clock ≤ clock → expsWeight xs < weight → Property xs env state

/-- Flapjack infrastructure: smaller-clock induction hypothesis for
environment extension. -/
def SmallerClock {C F : Type} (clock : Nat) : Prop :=
  ∀ (xs : List Bvi.Exp) (env : List Value) (state : BviState C F), state.clock < clock → Property xs env state

/-- Flapjack infrastructure: every evaluator case follows from the two
environment-extension induction hypotheses. -/
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
      have clock := evaluate_clock_le [e] env state
      rw [run] at clock
      exact weightIH (second :: rest) env next clock tailWeight
    | nil =>
      cases e with
      | var index => exact var index env state
      | force location index => exact force location index env state
      | tick body =>
        apply tick body env state
        intro nonzero
        have clock : (BviSem.decClock 1 state).clock < state.clock := by
          simp [BviSem.decClock]
          omega
        exact clockIH [body] env (BviSem.decClock 1 state) clock
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
        have clock := evaluate_clock_le bindings env state
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
        intro values next run
        have clock := evaluate_clock_le [condition] env state
        rw [run] at clock
        exact ⟨weightIH [yes] env next clock yesWeight, weightIH [no] env next clock noWeight⟩
      | call ticks destination args handler =>
        cases handler with
        | none =>
          have weight : expsWeight args < expsWeight [.call ticks destination args none] := by
            simp [expsWeight, expWeight]; omega
          exact callNone ticks destination args env state (weightIH args env state (Nat.le_refl _) weight)
        | some handler =>
          cases destination with
          | none =>
            intro extra notType
            simp [evaluate] at notType
          | some destination =>
            have argsWeight : expsWeight args < expsWeight [.call ticks (some destination) args (some handler)] := by
              simp [expsWeight, expWeight]; omega
            have handlerWeight : expsWeight [handler] < expsWeight [.call ticks (some destination) args (some handler)] := by
              simp [expsWeight, expWeight]; omega
            apply callSome ticks destination args handler env state (weightIH args env state (Nat.le_refl _) argsWeight)
            intro raised next clock
            exact weightIH [handler] (raised :: env) next clock handlerWeight
      | letCall rets ticks destination args body =>
        have argsWeight : expsWeight args < expsWeight [.letCall rets ticks destination args body] := by
          simp [expsWeight, expWeight]; omega
        have bodyWeight : expsWeight [body] < expsWeight [.letCall rets ticks destination args body] := by
          simp [expsWeight, expWeight]; omega
        apply letCall rets ticks destination args body env state (weightIH args env state (Nat.le_refl _) argsWeight)
        intro returned next clock
        exact weightIH [body] (returned ++ env) next clock bodyWeight

/-- Flapjack infrastructure: appending an environment cannot change a BVI
evaluation that does not produce a type error. This source-shaped result
remains untagged pending the evaluator and carrier review. -/
theorem evaluate_expand_env {C F : Type} (xs : List Bvi.Exp) (env extra : List Value)
    (state : BviState C F) (notType : (evaluate xs env state).1 ≠ .err (.abort .typeError)) :
    evaluate xs (env ++ extra) state = evaluate xs env state := by
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
  exact all state.clock (expsWeight xs) xs env state (Nat.le_refl _) (Nat.le_refl _) extra notType

end Flapjack.Compiler.Backend.BviInline.ExpandEnv
