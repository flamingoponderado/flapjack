import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileInstall
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileIfCase
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileHandle
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileCall

/-! Induction assembling BVL-to-BVI expression simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value expWeight expsWeight)

/-- The simulation precondition rules out expressions that violate the
source handler-shape invariant. -/
theorem simulation_invalidHandler {C F : Type} (xs : List Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (invalid : ¬ BvlHandle.Proofs.handleOk xs) :
    simulation xs env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  exact (invalid handlers).elim

/-- BVL evaluation is simulated by the BVI code produced for the same
expression list. The proof uses the source clock for dynamically selected
function and thunk bodies, and expression weight for structural cases.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_all {C F : Type} (xs : List Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : simulation xs env source := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (environment : List Value) (state : BvlSem.State (Nat × C) F),
      state.clock = clock → expsWeight expressions = weight → simulation expressions environment state := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (environment : List Value)
            (state : BvlSem.State (Nat × C) F), state.clock ≤ clock → expsWeight expressions < weight →
            simulation expressions environment state := by
          intro expressions environment state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions environment state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions environment state clockEq rfl
        have smaller : ∀ (expressions : List Bvl.Exp) (environment : List Value)
            (state : BvlSem.State (Nat × C) F), state.clock < clock → simulation expressions environment state := by
          intro expressions environment state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions environment state rfl rfl
        intro expressions environment state stateClock measure
        cases expressions with
        | nil => exact simulation_nil environment state
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply simulation_cons first second tail environment state
            · apply exprIH [first] environment state (by omega)
              simp only [expsWeight] at measure ⊢
              have positive := BvlSem.expWeight_pos second
              omega
            · intro mid midClock
              apply exprIH (second :: tail) environment mid (by omega)
              simp only [expsWeight] at measure ⊢
              omega
          | nil =>
            cases first with
            | var index => exact simulation_var index environment state
            | raise body =>
              apply simulation_raise body environment state
              apply exprIH [body] environment state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | tick body =>
              apply simulation_tick body environment state
              apply exprIH [body] environment (BvlSem.decClock 1 state)
              · simp [BvlSem.decClock]; omega
              · simp only [expsWeight, expWeight] at measure ⊢
                omega
            | op op args =>
              apply simulation_op op args environment state
              apply exprIH args environment state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | call ticks dest args =>
              apply simulation_call ticks dest args environment state
              · apply exprIH args environment state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro body values mid clockLt
                exact smaller [body] values mid (by omega)
            | force loc index =>
              apply simulation_force loc index environment state
              intro body values mid clockLt
              exact smaller [body] values mid (by omega)
            | ifThenElse condition yes no =>
              apply simulation_if condition yes no environment state
              · apply exprIH [condition] environment state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro mid midClock
                apply exprIH [yes] environment mid (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro mid midClock
                apply exprIH [no] environment mid (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | «let» bindings body =>
              cases bindings with
              | cons first rest =>
                apply simulation_let_cons first rest body environment state
                · apply exprIH (first :: rest) environment state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro mid values midClock
                  apply exprIH [body] (values ++ environment) mid (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
              | nil =>
                cases body with
                | «let» innerBindings innerBody =>
                  apply simulation_let_empty innerBindings innerBody environment state
                  · apply exprIH innerBindings environment state (by omega)
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
                  · intro values
                    apply exprIH [innerBody] values state (by omega)
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
                | _ =>
                  all_goals
                    apply simulation_invalidHandler
                    simp [BvlHandle.Proofs.handleOk, BvlHandle.Proofs.letOk]
            | handle body handler =>
              cases body with
              | «let» bindings inner =>
                apply simulation_handle bindings inner handler environment state
                · apply exprIH bindings environment state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro values
                  apply exprIH [inner] values state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro exception mid midClock
                  apply exprIH [handler] (exception :: environment) mid (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
              | _ =>
                all_goals
                  apply simulation_invalidHandler
                  simp [BvlHandle.Proofs.handleOk]
  exact allRanks source.clock (expsWeight xs) xs env source rfl rfl

/-- BVL-to-BVI expression compilation simulates source evaluation while
preserving the state relation and the existing relocation map. This has the
source theorem's hypotheses and conclusion, but remains untagged until the
BVI evaluator and dispatcher have been reviewed against their HOL originals. -/
theorem compileExpsCorrect {C F : Type} (xs : List Bvl.Exp) (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (run : BvlSem.evaluate xs env source = (res, next))
    (notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n xs = (ys, aux, n2))
    (related : stateRel relocate source target)
    (sourceOk : stateOk source) (envOk : bvOkList source.refs env)
    (installed : auxCodeInstalled (appListAppend aux) target.code)
    (handlers : BvlHandle.Proofs.handleOk xs) (global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key :=
  simulation_all xs env source n res next target n2 ys aux relocate run notTypeError compiled related
    sourceOk envOk installed handlers global

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
