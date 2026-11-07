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

namespace CompileExpsCorrectCarrier

/-- The closure state's reference and code maps have canonical finite support. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The BVL state's reference map has canonical finite support. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

end CompileExpsCorrectCarrier

/-- The closure-to-BVL expression and application simulations, assembled
with the original theorem's hypotheses and existential postconditions. The
lookup predicates express finite-map `FEVERY`, `SUBMAP`, and `FDIFF` through
the canonical finite-support representation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_correct"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, BvlSem.State.refs, f1, f2])]
theorem compileExpsCorrect_source {C F : Type} :
    (∀ (tmp : List ClosLang.Exp × List ClosSem.Value × ClosSem.State C F)
      (xs : List ClosLang.Exp) (env : List ClosSem.Value) (s1 : ClosSem.State C F)
      (aux1 : List (Nat × Nat × Bvl.Exp)) (t1 : BvlSem.State C F)
      (env' : List BvlSem.Value) (f1 : HolFiniteMapExact Nat Nat)
      (res : Result (List ClosSem.Value) ClosSem.Value) (s2 : ClosSem.State C F)
      (ys : List Bvl.Exp) (aux2 : List (Nat × Nat × Bvl.Exp)),
      tmp = (xs, env, s1) ∧ ClosSem.evaluate xs env s1 = (res, s2) ∧
      res ≠ .err (.abort .typeError) ∧ compileExpsHOL s1.maxApp xs aux1 = (ys, aux2) ∧
      ClosProps.everyFnLocationSome xs ∧
      (∀ name arity body, s1.code.lookup name = some (arity, body) → ClosProps.everyFnLocationSome [body]) ∧
      ClosProps.everyFnVarsSome xs ∧
      (∀ name arity body, s1.code.lookup name = some (arity, body) → ClosProps.everyFnVarsSome [body]) ∧
      codeInstalled aux2 t1.code ∧ envRel s1.maxApp f1 t1.refs t1.code env env' ∧ stateRel f1 s1 t1 →
      ∃ (ck : Nat) (res' : Result (List BvlSem.Value) BvlSem.Value)
        (t2 : BvlSem.State C F) (f2 : HolFiniteMapExact Nat Nat),
        BvlSem.evaluate ys env' { t1 with clock := s1.clock + ck } = (res', t2) ∧
        resultRel (List.Forall₂ (vRel s1.maxApp f2 t2.refs t2.code))
          (vRel s1.maxApp f2 t2.refs t2.code) res res' ∧
        stateRel f2 s2 t2 ∧ relocationSubmap f1 f2 ∧
        unmappedRefsSubmap t1.refs t2.refs f1 f2 ∧
        (∀ name arity body, s2.code.lookup name = some (arity, body) → ClosProps.everyFnLocationSome [body]) ∧
        (∀ name arity body, s2.code.lookup name = some (arity, body) → ClosProps.everyFnVarsSome [body]) ∧
        s2.clock = t2.clock) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (s1 : ClosSem.State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
      (s2 : ClosSem.State C F) (env : List BvlSem.Value) (t1 : BvlSem.State C F)
      (args' : List BvlSem.Value) (function' : BvlSem.Value) (f1 : HolFiniteMapExact Nat Nat),
      ClosSem.evaluateApp location function args s1 = (res, s2) ∧ res ≠ .err (.abort .typeError) ∧
      (∀ name arity body, s1.code.lookup name = some (arity, body) → ClosProps.everyFnLocationSome [body]) ∧
      (∀ name arity body, s1.code.lookup name = some (arity, body) → ClosProps.everyFnVarsSome [body]) ∧
      vRel s1.maxApp f1 t1.refs t1.code function function' ∧
      List.Forall₂ (vRel s1.maxApp f1 t1.refs t1.code) args args' ∧ stateRel f1 s1 t1 →
      ∃ (ck : Nat) (res' : Result (List BvlSem.Value) BvlSem.Value)
        (t2 : BvlSem.State C F) (f2 : HolFiniteMapExact Nat Nat),
        (args'.length ≠ 0 →
          (match location with
          | none => BvlSem.evaluate [mkClCall (.var args'.length) ((List.range args'.length).map Bvl.Exp.var)]
              (args' ++ [function'] ++ env) { t1 with clock := s1.clock + ck }
          | some address =>
            match BvlSem.findCode (some (address + numStubs s1.maxApp)) (args' ++ [function']) t1.code with
            | none => (.err (.abort .typeError), t2)
            | some (targetEnv, body) =>
              if s1.clock + ck < args'.length then (.err (.abort .timeoutError), { t1 with clock := 0 })
              else BvlSem.evaluate [body] targetEnv { t1 with clock := s1.clock + ck - args'.length }) =
            (res', t2)) ∧
        resultRel (List.Forall₂ (vRel s1.maxApp f2 t2.refs t2.code))
          (vRel s1.maxApp f2 t2.refs t2.code) res res' ∧
        stateRel f2 s2 t2 ∧ relocationSubmap f1 f2 ∧
        unmappedRefsSubmap t1.refs t2.refs f1 f2 ∧
        (∀ name arity body, s2.code.lookup name = some (arity, body) → ClosProps.everyFnLocationSome [body]) ∧
        (∀ name arity body, s2.code.lookup name = some (arity, body) → ClosProps.everyFnVarsSome [body]) ∧
        s2.clock = t2.clock) := by
  constructor
  · intro tmp xs env s1 aux1 t1 env' f1 res s2 ys aux2 hypotheses
    rcases hypotheses with ⟨_, run, noType, compile, loc, codeLoc, vars, codeVars, installed, envRel, states⟩
    obtain ⟨ck, res', t2, f2, targetRun, results, finalStates, submap, frame, ⟨finalLoc, finalVars⟩, clock⟩ :=
      expressionSimulation_all xs s1 s2 t1 env env' f1 aux1 aux2 ys res run noType compile loc
        ⟨codeLoc, codeVars⟩ vars installed envRel states
    exact ⟨ck, res', t2, f2, targetRun, results, finalStates, submap, frame, finalLoc, finalVars, clock⟩
  · intro location function args s1 res s2 env t1 args' function' f1 hypotheses
    rcases hypotheses with ⟨run, noType, codeLoc, codeVars, functionRel, argsRel, states⟩
    obtain ⟨ck, res', t2, f2, targetRun, results, finalStates, submap, frame, ⟨finalLoc, finalVars⟩, clock⟩ :=
      applicationSimulation_any location function args s1 s2 t1 function' args' env f1 res run noType
        ⟨codeLoc, codeVars⟩ functionRel argsRel states
    refine ⟨ck, res', t2, f2, ?_, results, finalStates, submap, frame, finalLoc, finalVars, clock⟩
    intro nonempty
    exact targetRun (by simpa using nonempty)

end Flapjack.Compiler.Backend.ClosToBvl
