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
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

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

/-- Source-shaped application simulation for both indirect and known-location
calls. When no arguments are supplied, the source returns the closure and the
target execution premise is vacuous. This remains untagged pending review of
the candidate evaluators and carriers against the HOL statement. -/
theorem applicationSimulation_any {C F : Type}
    (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (target : BvlSem.Value)
    (targetArgs rest : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluateApp location function args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (annotations : codeAnnotations s) (functionRel : vRel s.maxApp f t.refs t.code function target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (states : stateRel f s t) :
    ∃ extra targetResult tFinal fFinal,
      (targetArgs ≠ [] →
        (match location with
        | none => BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
            (targetArgs ++ [target] ++ rest) { t with clock := s.clock + extra }
        | some address =>
          match BvlSem.findCode (some (address + numStubs s.maxApp)) (targetArgs ++ [target]) t.code with
          | none => (.err (.abort .typeError), tFinal)
          | some (env, body) =>
            if s.clock + extra < targetArgs.length then (.err (.abort .timeoutError), { t with clock := 0 })
            else BvlSem.evaluate [body] env { t with clock := s.clock + extra - targetArgs.length }) =
          (targetResult, tFinal)) ∧
      resultRel (List.Forall₂ (vRel s.maxApp fFinal tFinal.refs tFinal.code))
        (vRel s.maxApp fFinal tFinal.refs tFinal.code) result targetResult ∧
      stateRel fFinal sFinal tFinal ∧ relocationSubmap f fFinal ∧
      unmappedRefsSubmap t.refs tFinal.refs f fFinal ∧ codeAnnotations sFinal ∧ sFinal.clock = tFinal.clock := by
  cases args with
  | nil =>
    cases argsRel
    simp [ClosSem.evaluateApp] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨0, .val [target], { t with clock := s.clock }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
    · simp
    · exact List.Forall₂.cons (by simpa using functionRel) .nil
    · exact (stateRel_clock f s t s.clock).1.mpr states
    · intro key value lookup
      exact lookup
    · intro key value lookup fresh
      exact ⟨lookup, fresh⟩
  | cons first tail =>
    have sourceNonempty : first :: tail ≠ [] := by simp
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      have lengths := argsRel.length_eq
      simp [empty] at lengths
    cases location with
    | none =>
      obtain ⟨extra, targetResult, tFinal, fFinal, targetRun, related, finalStates, map, refs, finalAnnotations, clocks⟩ :=
        applicationSimulation_all (first :: tail) sourceNonempty s sFinal t f function target targetArgs rest result
          run noType states annotations functionRel argsRel
      exact ⟨extra, targetResult, tFinal, fFinal, fun _ => targetRun, related, finalStates, map, refs, finalAnnotations, clocks⟩
    | some address =>
      obtain ⟨application, found⟩ := evaluateApp_direct_destClosure_some s sFinal address function (first :: tail)
        result sourceNonempty run noType
      obtain ⟨extra, targetResult, tFinal, fFinal, targetRun, related, finalStates, map, refs, finalAnnotations, clocks⟩ :=
        evaluateApp_direct_simulation_below s sFinal t f address s.clock function target (first :: tail) targetArgs rest
          application result (by omega) found run noType states annotations functionRel argsRel
          (fun body => expressionSimulationBelow_all s.clock [body])
      obtain ⟨body, targetFound⟩ := vRel_direct_findCode functionRel argsRel found
      have directRun := evaluate_directCall_env { t with clock := s.clock + extra } targetArgs rest target
        (address + numStubs s.maxApp) body targetNonempty (by simpa using targetFound)
      refine ⟨extra, targetResult, tFinal, fFinal, ?_, related, finalStates, map, refs, finalAnnotations, clocks⟩
      intro _
      dsimp only
      rw [targetFound]
      rw [directRun] at targetRun
      simpa [BvlSem.decClock] using targetRun

end Flapjack.Compiler.Backend.ClosToBvl
