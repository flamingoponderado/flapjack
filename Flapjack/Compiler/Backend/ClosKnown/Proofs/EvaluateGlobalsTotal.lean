module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.EvaluateGlobals

@[expose] public section


/-! Mutual closure-evaluator global-safety theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown.EvaluateGlobalsPort.Total
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Well-founded evaluator induction over clock and expression weight.
This is Lean infrastructure with no separate HOL declaration. -/
private theorem evalGlobalsAll {C F : Type} : ∀ clock : Nat,
    (∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
      (state : ClosSem.State C F), state.clock = clock → EvalAppGlobalsInvariant location f args state) ∧
    (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : ClosSem.State C F), state.clock = clock → expsWeight expressions = weight →
        EvalGlobalsInvariant expressions env state) := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock clockIH =>
    have appAll : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
        (state : ClosSem.State C F), state.clock = clock → EvalAppGlobalsInvariant location f args state := by
      intro location f args state stateClock res last h
      cases args with
      | nil => exact evaluateAppChangedGlobalsNil location f state res last h
      | cons first rest =>
        apply evaluateAppChangedGlobalsCons location f first rest state ?_ ?_ res last h
        · intro body env remaining found enough
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have small : (decClock ((first :: rest).length - remaining.length) state).clock < clock := by
            simp only [decClock]
            omega
          exact (clockIH _ small).2 _ [body] env _ rfl rfl
        · intro body env remaining value next found enough bodyRun
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have bodyBound := evaluate_clock_le [body] env (decClock ((first :: rest).length - remaining.length) state)
          rw [bodyRun] at bodyBound
          have small : next.clock < clock := by simp only [decClock] at bodyBound; omega
          exact (clockIH _ small).1 location value remaining next rfl
    constructor
    · exact appAll
    · intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : ClosSem.State C F), state.clock ≤ clock → expsWeight expressions < weight →
              EvalGlobalsInvariant expressions env state := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
          · exact weightIH _ weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : ClosSem.State C F), state.clock < clock → EvalGlobalsInvariant expressions env state := by
          intro expressions env state clockLt
          exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
        have appBound : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
            (state : ClosSem.State C F), state.clock ≤ clock → EvalAppGlobalsInvariant location f args state := by
          intro location f args state clockLe
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).1 location f args state rfl
          · exact appAll location f args state clockEq
        intro expressions env state stateClock measure res last h
        cases expressions with
        | nil => exact evaluateChangedGlobalsNil env state res last h
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluateChangedGlobalsCons first second tail env state ?_ ?_ res last h
            · apply exprIH [first] env state (by omega)
              simp only [expsWeight] at measure ⊢
              omega
            · intro values next headRun
              have bound := evaluate_clock_le [first] env state
              rw [headRun] at bound
              simp only at bound
              apply exprIH (second :: tail) env next (by omega)
              simp only [expsWeight] at measure ⊢
              omega
          | nil =>
            cases first with
            | var trace index => exact evaluateChangedGlobalsVar trace index env state res last h
            | fn name location selected arity body =>
              exact evaluateChangedGlobalsFn name location selected arity body env state res last h
            | raise trace body =>
              apply evaluateChangedGlobalsRaise trace body env state ?_ res last h
              apply exprIH [body] env state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | tick trace body =>
              apply evaluateChangedGlobalsTick trace body env state ?_ res last h
              intro nonzero
              apply smaller [body] env (decClock 1 state)
              simp only [decClock]
              omega
            | «let» trace bindings body =>
              apply evaluateChangedGlobalsLet trace bindings body env state ?_ ?_ res last h
              · apply exprIH bindings env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next bindingsRun
                have bound := evaluate_clock_le bindings env state
                rw [bindingsRun] at bound
                simp only at bound
                apply exprIH [body] (values ++ env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | handle trace body handler =>
              apply evaluateChangedGlobalsHandle trace body handler env state ?_ ?_ res last h
              · apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro value next bodyRun
                have bound := evaluate_clock_le [body] env state
                rw [bodyRun] at bound
                simp only at bound
                apply exprIH [handler] (value :: env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | ifThenElse trace condition yes no =>
              apply evaluateChangedGlobalsIf trace condition yes no env state ?_ ?_ ?_ res last h
              · apply exprIH [condition] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next conditionRun _
                have bound := evaluate_clock_le [condition] env state
                rw [conditionRun] at bound
                simp only at bound
                apply exprIH [yes] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next conditionRun _ _
                have bound := evaluate_clock_le [condition] env state
                rw [conditionRun] at bound
                simp only at bound
                apply exprIH [no] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | letrec names location selected functions body =>
              apply evaluateChangedGlobalsLetrec names location selected functions body env state ?_ res last h
              intro buildRc envdelta ed _
              apply exprIH [body] (ed ++ env) state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | call trace ticks location args =>
              apply evaluateChangedGlobalsCall trace ticks location args env state ?_ ?_ res last h
              · apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next callArgs body argsRun found enough
                have bound := evaluate_clock_le args env state
                rw [argsRun] at bound
                simp only at bound
                apply smaller [body] callArgs (decClock (ticks + 1) next)
                simp only [decClock]
                omega
            | app trace location function args =>
              apply evaluateChangedGlobalsApp trace location function args env state ?_ ?_ ?_ res last h
              · intro positive
                apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next positive argsRun
                have bound := evaluate_clock_le args env state
                rw [argsRun] at bound
                simp only at bound
                apply exprIH [function] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro values next functions final positive argsRun fnRun
                have bound1 := evaluate_clock_le args env state
                rw [argsRun] at bound1
                simp only at bound1
                have bound2 := evaluate_clock_le [function] env next
                rw [fnRun] at bound2
                simp only at bound2
                exact appBound location _ values final (by omega)
            | op trace op args =>
              apply evaluateChangedGlobalsOp trace op args env state ?_ ?_ ?_ res last h
              · apply exprIH args env state (by omega)
                have opBound := opWeight_gt trace op args
                simp only [expsWeight] at measure
                omega
              · intro values next program installed argsRun opEq installRun
                have bound := evaluate_clock_le args env state
                rw [argsRun] at bound
                simp only at bound
                have installClock := doInstall_success_clock values.reverse next installed program installRun
                apply smaller program [] installed
                omega
              · intro values next value argsRun notInstall opEq inspected
                have bound := evaluate_clock_le args env state
                rw [argsRun] at bound
                simp only at bound
                apply exprIH [appUnit (.var .none 0)] [value] next (by omega)
                subst op
                have hweight := appUnit_var_weight
                simp only [expsWeight, expWeight] at measure
                simp only [appUnit, expsWeight, expWeight] at hweight ⊢
                omega


/-- Evaluation and closure application preserve global-write safety and
account for all writes in the evaluated syntax and installed programs. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsMutual {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
      (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F),
      evaluate expressions env s0 = (res, s) ∧ ssgcFree s0 ∧
        (∀ e ∈ expressions, esgcFree e) ∧ (∀ v ∈ env, vsgcFree v) →
      ssgcFree s ∧ rsgcFree res ∧ ∃ n,
        s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
        mglobalsExtend s0.globals
          ({k | elistGlobals expressions k ≠ 0} ∪
           {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals) ∧
    (∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value) (s0 : ClosSem.State C F)
      (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F),
      evaluateApp location f args s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
        (∀ v ∈ args, vsgcFree v) →
      ssgcFree s ∧ rsgcFree res ∧ ∃ n,
        s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
        mglobalsExtend s0.globals
          {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals) := by
  constructor
  · intro expressions env s0 res s h
    exact (evalGlobalsAll s0.clock).2 _ expressions env s0 rfl rfl res s h
  · intro location f args s0 res s h
    exact (evalGlobalsAll s0.clock).1 location f args s0 rfl res s h

/-- Evaluation preserves global safety and restricts writes to its syntax and
programs installed during execution. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobals {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate expressions env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ expressions, esgcFree e) ∧ (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals expressions k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals :=
  evaluateChangedGlobalsMutual.1 expressions env s0 res s h

/-- Closure application preserves global safety and restricts writes to
programs installed during execution. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_app_changed_globals"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppChangedGlobals {C F : Type} (location : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluateApp location f args s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
      (∀ v ∈ args, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals :=
  evaluateChangedGlobalsMutual.2 location f args s0 res s h

end Flapjack.Compiler.Backend.ClosKnown.EvaluateGlobalsPort.Total
