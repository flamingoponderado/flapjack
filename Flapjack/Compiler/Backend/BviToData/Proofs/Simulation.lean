import Flapjack.Compiler.Backend.BviToData.Proofs.Call
import Flapjack.Compiler.Backend.BviToData.Proofs.Force
import Flapjack.Compiler.Backend.BviToData.Proofs.Op

/-! Assembly of the BVI-to-data simulation using the evaluator's clock and
structural measure. This infrastructure remains untagged pending review of the
source evaluator and the complete HOL theorem statement. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Every expression list satisfies the compiler simulation. Recursive calls
use a smaller clock; ordinary subexpressions use a smaller structural weight. -/
theorem simulationFor_all {C F : Type} (expressions : List Bvi.Exp)
    (env : List BvlSem.Value) (state : BviSem.BviState C F) :
    simulationFor expressions env state := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvi.Exp)
      (env : List BvlSem.Value) (state : BviSem.BviState C F), state.clock = clock →
      BviSem.expsWeight expressions = weight → simulationFor expressions env state := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvi.Exp) (env : List BvlSem.Value)
            (state : BviSem.BviState C F), state.clock ≤ clock → BviSem.expsWeight expressions < weight →
            simulationFor expressions env state := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (BviSem.expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (BviSem.expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvi.Exp) (env : List BvlSem.Value)
            (state : BviSem.BviState C F), state.clock < clock → simulationFor expressions env state := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (BviSem.expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => exact simulationFor_nil env state
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply compileCorrect_cons first second tail env state
            · apply exprIH [first] env state (by omega)
              simp only [BviSem.expsWeight] at measure ⊢
              have positive := BviSem.expWeight_pos second
              omega
            · intro head smid run
              have bound := BviSem.evaluate_clock_le [first] env state
              rw [run] at bound
              change smid.clock ≤ state.clock at bound
              apply exprIH (second :: tail) env smid (by omega)
              simp only [BviSem.expsWeight] at measure ⊢
              have positive := BviSem.expWeight_pos first
              omega
          | nil =>
            cases first with
            | var index => exact simulationFor_var index env state
            | raise body =>
              apply simulationFor_raise body env state
              apply exprIH [body] env state (by omega)
              simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
              omega
            | «let» bindings body =>
              apply simulationFor_let bindings body env state
              · apply exprIH bindings env state (by omega)
                simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
                omega
              · intro values smid run
                have bound := BviSem.evaluate_clock_le bindings env state
                rw [run] at bound
                change smid.clock ≤ state.clock at bound
                apply exprIH [body] (values ++ env) smid (by omega)
                simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
                omega
            | ifThenElse condition yes no =>
              apply simulationFor_if condition yes no env state
              · apply exprIH [condition] env state (by omega)
                simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
                omega
              · intro value smid choice run bool
                have bound := BviSem.evaluate_clock_le [condition] env state
                rw [run] at bound
                change smid.clock ≤ state.clock at bound
                apply exprIH [if choice then yes else no] env smid (by omega)
                cases choice <;> simp only [Bool.false_eq_true, if_false, if_true, BviSem.expsWeight, BviSem.expWeight] at measure ⊢ <;> omega
            | tick body =>
              apply simulationFor_tick body env state
              intro positive
              apply smaller [body] env (BviSem.decClock 1 state)
              simp only [BviSem.decClock]
              omega
            | «return» args =>
              apply simulationFor_return args env state
              apply exprIH args env state (by omega)
              simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
              omega
            | op op args =>
              apply simulationFor_op op args env state
              apply exprIH args env state (by omega)
              simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
              omega
            | force label index =>
              apply simulationFor_force label index env state
              intro thunk function callArgs body var thunkRun code positive
              apply smaller [body] callArgs (BviSem.decClock 1 state)
              simp only [BviSem.decClock]
              omega
            | call ticks dest args handler =>
              apply simulationFor_call ticks dest args handler env state
              · apply exprIH args env state (by omega)
                cases handler <;> simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢ <;> omega
              · intro values smid callArgs body argsRun code available
                have bound := BviSem.evaluate_clock_le args env state
                rw [argsRun] at bound
                apply smaller [body] callArgs (BviSem.decClock (ticks + 1) smid)
                simp only [BviSem.decClock] at bound ⊢
                omega
              · intro h values smid callArgs body value caughtSource handlerEq argsRun code available bodyRun
                have argsBound := BviSem.evaluate_clock_le args env state
                rw [argsRun] at argsBound
                have bodyBound := BviSem.evaluate_clock_le [body] callArgs (BviSem.decClock (ticks + 1) smid)
                rw [bodyRun] at bodyBound
                apply smaller [h] (value :: env) caughtSource
                simp only [BviSem.decClock] at argsBound bodyBound
                omega
            | letCall rets ticks dest args body =>
              apply simulationFor_letCall rets ticks dest args body env state
              · apply exprIH args env state (by omega)
                simp only [BviSem.expsWeight, BviSem.expWeight] at measure ⊢
                omega
              · intro values smid callArgs callee argsRun code available
                have bound := BviSem.evaluate_clock_le args env state
                rw [argsRun] at bound
                apply smaller [callee] callArgs (BviSem.decClock (ticks + 1) smid)
                simp only [BviSem.decClock] at bound ⊢
                omega
              · intro values smid callArgs callee returned calleeState argsRun code available calleeRun
                have argsBound := BviSem.evaluate_clock_le args env state
                rw [argsRun] at argsBound
                have calleeBound := BviSem.evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) smid)
                rw [calleeRun] at calleeBound
                apply smaller [body] (returned ++ env) calleeState
                simp only [BviSem.decClock] at argsBound calleeBound
                omega
  exact allRanks state.clock (BviSem.expsWeight expressions) expressions env state rfl rfl

/-- The optimized executable traversal at a sufficient structural fuel bound
satisfies the assembled simulation for an arbitrary function body. The
unoptimized final state carries the result invariant; optimization may change
the four resource fields displayed in the executed state. This is a Lean-side
composition, pending HOL evaluator and carrier correspondence review. -/
theorem compileExpBounded_correct {C F : Type} (fuel : Nat) (body : Bvi.Exp)
    (env : List BvlSem.Value) (source nextSource : BviSem.BviState C F)
    (res : BviSem.BviResult) (target : DataSem.State C F)
    (bound : Bvi.expBudget body < fuel)
    (run : BviSem.evaluate [body] env source = (res, nextSource))
    (notType : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env (List.range env.length) (sptMap dataToBviValue target.locals))
    (fresh : ∀ k, env.length ≤ k → sptLookup k target.locals = none)
    (related : stateRel source target)
    (exceptionJump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ prog result final names next ls localsSize stackMax safe peak,
      compileExpBounded fuel env.length body = some prog ∧
      DataSem.evaluate prog target =
        (some result, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) ∧
      stateRel nextSource final ∧
      stateRel nextSource { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak } ∧
      correctOutcome res target final env.length next (List.range env.length) [] names env true (some result) ls := by
  obtain ⟨result, final, names, next, ls, localsSize, stackMax, safe, peak, runTarget,
      finalRel, optimisedRel, outcome⟩ :=
    compileExp_of_simulation body env source nextSource res target
      (simulationFor_all [body] env source) run notType vars fresh related exceptionJump
  exact ⟨compileExp env.length body, result, final, names, next, ls, localsSize, stackMax, safe, peak,
    compileExpBounded_agrees fuel env.length body bound, runTarget, finalRel, optimisedRel, outcome⟩

end Flapjack.Compiler.Backend.BviToData
