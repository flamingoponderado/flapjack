import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateForce
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateIf
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateHandle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateRaise
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateTick
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateCall
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateClosure
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLetrecMutual

/-! Assembly of the closure-to-BVL expression simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

mutual

/-- Assemble the successor-clock cases for one expression. The hypothesis
for arbitrary expressions at the preceding bound handles dynamic calls. -/
theorem expressionSimulationBelow_single_succ {C F : Type} (clockBound : Nat)
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (expression : ClosLang.Exp) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [expression] := by
  cases expression with
  | var trace index =>
    exact expressionSimulation_below _ _ (expressionSimulation_var trace index)
  | ifThenElse trace condition yes no =>
    exact expressionSimulationBelow_if _ trace condition yes no
      (expressionSimulationBelow_single_succ clockBound bodyIH condition)
      (expressionSimulationBelow_single_succ clockBound bodyIH yes)
      (expressionSimulationBelow_single_succ clockBound bodyIH no)
  | «let» trace bindings body =>
    exact expressionSimulationBelow_let _ trace bindings body
      (expressionSimulationBelow_list_succ clockBound bodyIH bindings)
      (expressionSimulationBelow_single_succ clockBound bodyIH body)
  | raise trace body =>
    exact expressionSimulationBelow_raise _ trace body (expressionSimulationBelow_single_succ clockBound bodyIH body)
  | handle trace body handler =>
    exact expressionSimulationBelow_handle _ trace body handler
      (expressionSimulationBelow_single_succ clockBound bodyIH body)
      (expressionSimulationBelow_single_succ clockBound bodyIH handler)
  | tick trace body =>
    exact expressionSimulationBelow_tick_succ clockBound trace body (bodyIH body)
  | call trace ticks location args =>
    exact expressionSimulationBelow_call clockBound trace ticks location args
      (expressionSimulationBelow_list_succ clockBound bodyIH args) bodyIH
  | app trace location function args =>
    exact expressionSimulationBelow_app_any_succ clockBound trace location args function
      (expressionSimulationBelow_list_succ clockBound bodyIH args)
      (expressionSimulationBelow_single_succ clockBound bodyIH function) bodyIH
  | fn name location selected arity body =>
    exact expressionSimulation_below _ _ (expressionSimulation_fn name location selected arity body)
  | letrec names location selected functions body =>
    exact expressionSimulationBelow_letrec _ names location selected functions body
      (expressionSimulationBelow_single_succ clockBound bodyIH body)
  | op trace op args =>
    exact expressionSimulationBelow_op_succ clockBound trace op args
      (expressionSimulationBelow_list_succ clockBound bodyIH args) bodyIH
termination_by sizeOf expression

/-- Assemble a list from its structurally smaller expression simulations. -/
theorem expressionSimulationBelow_list_succ {C F : Type} (clockBound : Nat)
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (expressions : List ClosLang.Exp) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) expressions := by
  cases expressions with
  | nil => exact expressionSimulation_below _ _ expressionSimulation_nil
  | cons first rest =>
    cases rest with
    | nil => exact expressionSimulationBelow_single_succ clockBound bodyIH first
    | cons second tail =>
      exact expressionSimulationBelow_cons _ first second tail
        (expressionSimulationBelow_single_succ clockBound bodyIH first)
        (expressionSimulationBelow_list_succ clockBound bodyIH (second :: tail))
termination_by sizeOf expressions

end

/-- Every expression satisfies the bounded candidate simulation. This does
not claim that the candidate's semantic carriers have been reviewed as the
corresponding HOL carriers. -/
theorem expressionSimulationBelow_all {C F : Type} (clockBound : Nat)
    (expressions : List ClosLang.Exp) :
    expressionSimulationBelow (C := C) (F := F) clockBound expressions := by
  induction clockBound generalizing expressions with
  | zero =>
    intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result bound
    omega
  | succ clockBound ih =>
    exact expressionSimulationBelow_list_succ clockBound (fun body => ih [body]) expressions

/-- The unrestricted candidate simulation follows by choosing a clock bound
larger than the initial source clock. -/
theorem expressionSimulation_all {C F : Type} (expressions : List ClosLang.Exp) :
    expressionSimulation (C := C) (F := F) expressions :=
  (expressionSimulation_iff_below expressions).2 (fun bound => expressionSimulationBelow_all bound expressions)

/-- Indirect closure application is simulated for every nonempty argument
list, discharging the body-simulation premise of the application induction. -/
theorem applicationSimulation_all {C F : Type} (args : List ClosSem.Value) :
    applicationSimulation (C := C) (F := F) args :=
  applicationSimulation_of_body_simulation (fun body => expressionSimulation_all [body]) args

end Flapjack.Compiler.Backend.ClosToBvl
