module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApp
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyFullBody
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationIf
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLetrec
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationRaise
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationHandle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationTick
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCall
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOp

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Mutual evaluator induction for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Total
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL

/-- Induction on the evaluator clock and expression weight. This is
Flapjack infrastructure for assembling the original mutual theorem. -/
private theorem simulationAll {C F : Type} : ∀ clock : Nat,
    (∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), state.clock = clock → KnownAppSimulationAt location f args state) ∧
    (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), state.clock = clock → expsWeight expressions = weight →
        KnownSimulationAt expressions env state) := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock clockIH =>
    have appAll : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
        (state : State (Spt ValApprox × C) F), state.clock = clock → KnownAppSimulationAt location f args state := by
      intro location f args state stateClock
      cases args with
      | nil => exact knownCorrect0AppNil location f state
      | cons first rest =>
        apply ApplyFull.knownCorrect0AppCons location f first rest state ?_ ?_
        · intro kind body env remaining bodyResult middle values value tail h
          obtain ⟨found, rfl, enough, run, rfl, rfl, rfl⟩ := h
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have bound := evaluate_clock_le [body] env (decClock ((first :: rest).length - remaining.length) state)
          rw [run] at bound
          simp only at bound
          have small : middle.clock < clock := by simp only [decClock] at bound; omega
          exact (clockIH _ small).1 location value remaining middle rfl
        · intro kind body env remaining h
          obtain ⟨found, rfl, enough⟩ := h
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have small : (decClock ((first :: rest).length - remaining.length) state).clock < clock := by
            simp only [decClock]; omega
          exact (clockIH _ small).2 _ [body] env _ rfl rfl
    constructor
    · exact appAll
    · intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock ≤ clock → expsWeight expressions < weight →
              KnownSimulationAt expressions env state := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
          · exact weightIH _ weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock < clock → KnownSimulationAt expressions env state := by
          intro expressions env state clockLt
          exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
        have appBound : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock ≤ clock → KnownAppSimulationAt location f args state := by
          intro location f args state clockLe
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).1 location f args state rfl
          · exact appAll location f args state clockEq
        intro expressions env state stateClock measure
        cases expressions with
        | nil => exact knownCorrect0Nil env state
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply Cons.knownCorrect0Cons first second tail env state ?_ ?_
            · intro result next values ⟨run, _⟩
              have bound := evaluate_clock_le [first] env state
              rw [run] at bound
              simp only at bound
              apply exprIH (second :: tail) env next (by omega)
              simp only [expsWeight] at measure ⊢; omega
            · apply exprIH [first] env state (by omega)
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var trace index => exact knownCorrect0Var trace index env state
            | fn name location selected arity body => exact Fn.knownCorrect0Fn name location selected arity body env state
            | raise trace body =>
              apply Raise.knownCorrect0Raise trace body env state
              apply exprIH [body] env state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick trace body =>
              apply Tick.knownCorrect0Tick trace body env state
              intro nonzero
              apply smaller [body] env (decClock 1 state)
              simp only [decClock]; omega
            | «let» trace bindings body =>
              apply Let.knownCorrect0Let trace bindings body env state ?_ ?_
              · intro result next values ⟨run, _⟩
                have bound := evaluate_clock_le bindings env state
                rw [run] at bound
                simp only at bound
                apply exprIH [body] (values ++ env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply exprIH bindings env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle trace body handler =>
              apply Handle.knownCorrect0Handle trace body handler env state ?_ ?_
              · intro result next error value ⟨run, _, _⟩
                have bound := evaluate_clock_le [body] env state
                rw [run] at bound
                simp only at bound
                apply exprIH [handler] (value :: env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse trace condition yes no =>
              apply If.knownCorrect0If trace condition yes no env state ?_ ?_ ?_
              · intro result next values ⟨run, _, _, _⟩
                have bound := evaluate_clock_le [condition] env state
                rw [run] at bound
                simp only at bound
                apply exprIH [no] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro result next values ⟨run, _, _⟩
                have bound := evaluate_clock_le [condition] env state
                rw [run] at bound
                simp only at bound
                apply exprIH [yes] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply exprIH [condition] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | letrec names location selected functions body =>
              apply Letrec.knownCorrect0Letrec names location selected functions body env state
              intro buildRc envdelta ed _
              apply exprIH [body] (ed ++ env) state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call trace ticks location args =>
              apply Call.knownCorrect0Call trace ticks location args env state ?_ ?_
              · intro result next values entry callArgs body ⟨run, _, _, _, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply smaller [body] callArgs (decClock (ticks + 1) next)
                simp only [decClock]; omega
              · apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | app trace location function args =>
              apply App.knownCorrect0App trace location function args env state ?_ ?_ ?_
              · intro argResult next values fnResult last functions ⟨_, argsRun, _, fnRun, _⟩
                have bound1 := evaluate_clock_le args env state
                rw [argsRun] at bound1
                simp only at bound1
                have bound2 := evaluate_clock_le [function] env next
                rw [fnRun] at bound2
                simp only at bound2
                exact appBound location _ values last (by omega)
              · intro result next values ⟨_, run, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply exprIH [function] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro _
                apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | op trace op args =>
              apply Op.knownCorrect0Op trace op args env state ?_ ?_ ?_
              · intro result next values installResult installed program ⟨run, _, _, installRun, success⟩
                subst installResult
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                have installClock := doInstall_success_clock values.reverse next installed program installRun
                apply smaller program [] installed
                omega
              · intro result next values mode value ⟨run, _, _, opEq, _, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply exprIH [appUnit (.var .none 0)] [value] next (by omega)
                subst op
                have hweight := appUnit_var_weight
                simp only [expsWeight, expWeight] at measure
                simp only [appUnit, expsWeight, expWeight] at hweight ⊢
                omega
              · apply exprIH args env state (by omega)
                have opBound := opWeight_gt trace op args
                simp only [expsWeight] at measure
                omega

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The source optimizer's mutual expression and application simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0 {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), KnownSimulationAt expressions env state) ∧
    (∀ (location : Option Nat) (fn : ClosSem.Value) (args : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), KnownAppSimulationAt location fn args state) := by
  constructor
  · intro expressions env state
    exact (simulationAll state.clock).2 _ expressions env state rfl rfl
  · intro location fn args state
    exact (simulationAll state.clock).1 location fn args state rfl

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Total
