module

public import Flapjack.Compiler.Backend.BviToData.Proofs.LetCall
public import Flapjack.Compiler.Backend.BviToData.Proofs.Op
public import Flapjack.Compiler.Backend.BviToData.Proofs.Force

@[expose] public section

/-! Full BVI-to-data compiler simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem simulationFor_all {C F : Type} (xs : List Bvi.Exp) (env : List BvlSem.Value)
    (state : BviSem.BviState C F) : simulationFor xs env state := by
  cases xs with
  | nil => exact simulationFor_nil env state
  | cons exp rest =>
    cases rest with
    | cons second rest =>
      apply compileCorrect_cons exp second rest env state
      · exact simulationFor_all [exp] env state
      · intro value mid run
        have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le [exp] env state
        exact simulationFor_all (second :: rest) env mid
    | nil =>
      cases exp with
      | var index => exact simulationFor_var index env state
      | force location index =>
        apply simulationFor_force location index env state
        intro thunk function args body lookup inspect found nonzero
        exact simulationFor_all [body] args (BviSem.decClock 1 state)
      | ifThenElse condition yes no =>
        apply simulationFor_if condition yes no env state
        · exact simulationFor_all [condition] env state
        · intro value mid choice run decoded
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le [condition] env state
          exact simulationFor_all [if choice then yes else no] env mid
      | «let» bindings body =>
        apply simulationFor_let bindings body env state
        · exact simulationFor_all bindings env state
        · intro values mid run
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le bindings env state
          exact simulationFor_all [body] (values ++ env) mid
      | raise body => exact simulationFor_raise body env state (simulationFor_all [body] env state)
      | tick body =>
        apply simulationFor_tick body env state
        intro nonzero
        exact simulationFor_all [body] env (BviSem.decClock 1 state)
      | «return» args => exact simulationFor_return args env state (simulationFor_all args env state)
      | op op args => exact simulationFor_op op args env state (simulationFor_all args env state)
      | call ticks dest args handler =>
        apply simulationFor_call ticks dest args handler env state
        · intro valid
          exact simulationFor_all args env state
        · intro values mid callArgs body valid run found clock
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le args env state
          exact simulationFor_all [body] callArgs (BviSem.decClock (ticks + 1) mid)
        · intro values mid callArgs body last value expression valid run found clock calleeRun handlerEq
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le args env state
          have lastBound : last.clock ≤ (BviSem.decClock (ticks + 1) mid).clock := by
            simpa [calleeRun] using BviSem.evaluate_clock_le [body] callArgs (BviSem.decClock (ticks + 1) mid)
          exact simulationFor_all [expression] (value :: env) last
      | letCall rets ticks dest args body =>
        apply simulationFor_letCall rets ticks dest args body env state
        · exact simulationFor_all args env state
        · intro values mid callArgs callee run found clock
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le args env state
          exact simulationFor_all [callee] callArgs (BviSem.decClock (ticks + 1) mid)
        · intro values mid callArgs callee last returned run found clock calleeRun length
          have midBound : mid.clock ≤ state.clock := by simpa [run] using BviSem.evaluate_clock_le args env state
          have lastBound : last.clock ≤ (BviSem.decClock (ticks + 1) mid).clock := by
            simpa [calleeRun] using BviSem.evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) mid)
          exact simulationFor_all [body] (returned ++ env) last
termination_by (state.clock, BviSem.expsWeight xs)
decreasing_by
  all_goals simp only [Prod.lex_def, BviSem.expsWeight, BviSem.expWeight, BviSem.decClock]
  all_goals try (have := BviSem.expWeight_pos exp)
  all_goals try (have := BviSem.expWeight_pos condition)
  all_goals try (have := BviSem.expWeight_pos yes)
  all_goals try (have := BviSem.expWeight_pos no)
  all_goals try (have := BviSem.expWeight_pos body)
  all_goals try simp only [lt_self_iff_false, false_or, true_and]
  all_goals try (simp only [BviSem.decClock] at lastBound)
  all_goals try omega
  all_goals try (cases choice <;> simp_all <;> omega)
  all_goals try (cases handler <;> simp [BviSem.expWeight] <;> omega)

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace SimulationCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end SimulationCarrier

/-- The full BVI-to-data compiler simulation for arbitrary expression lists,
source results, target states, and compiler parameters. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem compileCorrect {C F : Type} (xs : List Bvi.Exp) (env : List BvlSem.Value)
    (s1 : BviSem.BviState C F) (res : BviSem.BviResult) (s2 : BviSem.BviState C F)
    (t1 : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (run : BviSem.evaluate xs env s1 = (res, s2))
    (notTypeError : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue t1.locals))
    (tailShape : xs.length ≠ 1 → tail = false)
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1)
    (livePresent : ∀ v ∈ live, sptLookup v t1.locals ≠ none)
    (exceptionJump : isException res → DataSem.jumpExc t1 ≠ none) :
    ∃ t2 prog pres vs next ls,
      compileSource n corr tail live xs = (prog, vs, next) ∧
      DataSem.evaluate prog t1 = (pres, t2) ∧ stateRel s2 t2 ∧
      correctOutcome res t1 t2 n next corr live vs env tail pres ls := by
  exact simulationFor_all xs env s1 res s2 t1 n corr tail live run notTypeError vars
    tailShape fresh related livePresent exceptionJump

end Flapjack.Compiler.Backend.BviToData
