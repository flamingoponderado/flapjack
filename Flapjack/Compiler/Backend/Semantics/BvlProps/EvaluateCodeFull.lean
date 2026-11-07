import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateCode
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateEvents

/-! Code-growth induction for BVL evaluation. The private cases factor the
induction and have no standalone HOL declarations. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace CodeGrowthCarrier
/-- The canonical BVL reference-map state representation roundtrips. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end CodeGrowthCarrier

private theorem subsptRefl {α : Type} (tree : Spt α) : sptSubspt tree tree := by
  intro key member
  exact ⟨member, rfl⟩


private theorem evaluate_raise_code_step {C F : Type} (body : Bvl.Exp) (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (last : State C F) (bodyResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate [body] env state = (bodyResult, last) → sptSubspt state.code last.code)
    (run : evaluate [.raise body] env state = (result, final)) : sptSubspt state.code final.code := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    rw [evaluate, bodyRun] at run
    have codePrefix := bodyIH last bodyResult bodyRun
    cases bodyResult <;> simp at run
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals exact codePrefix


private theorem evaluate_let_code_step {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp) (env : List BvlSem.Value)
    (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (bindingsIH : ∀ (last : State C F) (bindingResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate bindings env state = (bindingResult, last) → sptSubspt state.code last.code)
    (bodyIH : ∀ (bodyEnv : List BvlSem.Value) (start last : State C F) (bodyResult : Result (List BvlSem.Value) BvlSem.Value),
      start.clock ≤ state.clock → evaluate [body] bodyEnv start = (bodyResult, last) → sptSubspt start.code last.code)
    (run : evaluate [.let bindings body] env state = (result, final)) : sptSubspt state.code final.code := by
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le bindings env state
      simpa [bindingsRun] using clock
    rw [bindingsRun] at run
    have codePrefix := bindingsIH last bindingResult bindingsRun
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact codePrefix
    | val values =>
      dsimp only at run
      exact sptSubsptTrans _ _ _ ⟨codePrefix, bodyIH (values ++ env) last final result bound run⟩


private theorem evaluate_if_code_step {C F : Type} (condition yes no : Bvl.Exp) (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (conditionIH : ∀ (last : State C F) (testResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate [condition] env state = (testResult, last) → sptSubspt state.code last.code)
    (branchIH : ∀ (choice : Bool) (start last : State C F) (branchResult : Result (List BvlSem.Value) BvlSem.Value),
      start.clock ≤ state.clock → evaluate [if choice then yes else no] env start = (branchResult, last) →
      sptSubspt start.code last.code)
    (run : evaluate [.ifThenElse condition yes no] env state = (result, final)) : sptSubspt state.code final.code := by
  rw [evaluate, fixClock_evaluate] at run
  cases conditionRun : evaluate [condition] env state with
  | mk testResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    rw [conditionRun] at run
    have codePrefix := conditionIH last testResult conditionRun
    cases testResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact codePrefix
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton condition env state last values conditionRun
      dsimp only at run
      cases boolRun : asBool value with
      | none =>
        simp [boolRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact codePrefix
      | some choice =>
        cases choice <;> simp [boolRun] at run
        · exact sptSubsptTrans _ _ _ ⟨codePrefix, branchIH false last final result bound run⟩
        · exact sptSubsptTrans _ _ _ ⟨codePrefix, branchIH true last final result bound run⟩


private theorem evaluate_handle_code_step {C F : Type} (body handler : Bvl.Exp) (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (last : State C F) (bodyResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate [body] env state = (bodyResult, last) → sptSubspt state.code last.code)
    (handlerIH : ∀ (value : BvlSem.Value) (start last : State C F) (handlerResult : Result (List BvlSem.Value) BvlSem.Value),
      start.clock ≤ state.clock → evaluate [handler] (value :: env) start = (handlerResult, last) →
      sptSubspt start.code last.code)
    (run : evaluate [.handle body handler] env state = (result, final)) : sptSubspt state.code final.code := by
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le [body] env state
      simpa [bodyRun] using clock
    rw [bodyRun] at run
    have codePrefix := bodyIH last bodyResult bodyRun
    cases bodyResult with
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact codePrefix
    | err error =>
      cases error with
      | abort reason =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact codePrefix
      | raise value =>
        dsimp only at run
        exact sptSubsptTrans _ _ _ ⟨codePrefix, handlerIH value last final result bound run⟩


private theorem evaluate_tick_code_step {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (start last : State C F) (bodyResult : Result (List BvlSem.Value) BvlSem.Value),
      start.clock < state.clock → evaluate [body] env start = (bodyResult, last) → sptSubspt start.code last.code)
    (run : evaluate [.tick body] env state = (result, final)) : sptSubspt state.code final.code := by
  rw [evaluate] at run
  split at run
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    exact subsptRefl _
  · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
    simpa [decClock] using bodyIH (decClock 1 state) final result smaller run



private theorem evaluate_call_code_step {C F : Type} (ticks : Nat) (location : Option Nat) (args : List Bvl.Exp) (env : List BvlSem.Value)
    (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate args env state = (argResult, last) → sptSubspt state.code last.code)
    (bodyIH : ∀ (body : Bvl.Exp) (bodyEnv : List BvlSem.Value) (start last : State C F)
      (bodyResult : Result (List BvlSem.Value) BvlSem.Value), start.clock < state.clock →
      evaluate [body] bodyEnv start = (bodyResult, last) → sptSubspt start.code last.code)
    (run : evaluate [.call ticks location args] env state = (result, final)) :
    sptSubspt state.code final.code := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact argsPrefix
    | val arguments =>
      dsimp only at run
      cases found : findCode location arguments last.code with
      | none =>
        simp [found] at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix
      | some entry =>
        rcases entry with ⟨bodyEnv, body⟩
        rw [found] at run
        dsimp only at run
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact argsPrefix
        · have smaller : (decClock (ticks + 1) last).clock < state.clock := by simp [decClock]; omega
          have bodyPrefix := bodyIH body bodyEnv (decClock (ticks + 1) last) final result smaller run
          exact sptSubsptTrans _ _ _ ⟨argsPrefix, by simpa [decClock] using bodyPrefix⟩



private theorem evaluate_cons_code_step {C F : Type} (first second : Bvl.Exp) (tail : List Bvl.Exp)
    (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (headIH : ∀ (last : State C F) (headResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate [first] env state = (headResult, last) → sptSubspt state.code last.code)
    (tailIH : ∀ (start last : State C F) (tailResult : Result (List BvlSem.Value) BvlSem.Value),
      start.clock ≤ state.clock → evaluate (second :: tail) env start = (tailResult, last) →
      sptSubspt start.code last.code)
    (run : evaluate (first :: second :: tail) env state = (result, final)) :
    sptSubspt state.code final.code := by
  cases headRun : evaluate [first] env state with
  | mk headResult last =>
    have headPrefix := headIH last headResult headRun
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le [first] env state
      simpa [headRun] using clock
    rw [evaluate, fixClock_evaluate, headRun] at run
    cases headResult with
    | err error => simp at run; rcases run with ⟨rfl, rfl⟩; exact headPrefix
    | val values =>
      cases tailRun : evaluate (second :: tail) env last with
      | mk tailResult tailFinal =>
        rw [tailRun] at run
        have tailPrefix := tailIH last tailFinal tailResult bound tailRun
        cases tailResult <;> simp at run
        all_goals rcases run with ⟨rfl, rfl⟩
        all_goals exact sptSubsptTrans _ _ _ ⟨headPrefix, tailPrefix⟩


private theorem evaluate_op_code_step {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List BvlSem.Value) BvlSem.Value),
      evaluate args env state = (argResult, last) → sptSubspt state.code last.code)
    (run : evaluate [.op op args] env state = (result, final)) : sptSubspt state.code final.code := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error => simp at run; rcases run with ⟨rfl, rfl⟩; exact argsPrefix
    | val arguments =>
      cases appRun : doApp op arguments.reverse last with
      | err error => simp [appRun] at run; rcases run with ⟨rfl, rfl⟩; exact argsPrefix
      | val pair =>
        rcases pair with ⟨value, next⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact sptSubsptTrans _ _ _ ⟨argsPrefix, doApp_code_mono op arguments.reverse last next value appRun⟩


private theorem evaluate_force_code_step {C F : Type} (location index : Nat)
    (env : List BvlSem.Value) (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (bodyIH : ∀ (body : Bvl.Exp) (bodyEnv : List BvlSem.Value) (start last : State C F)
      (bodyResult : Result (List BvlSem.Value) BvlSem.Value), start.clock < state.clock →
      evaluate [body] bodyEnv start = (bodyResult, last) → sptSubspt start.code last.code)
    (run : evaluate [.force location index] env state = (result, final)) :
    sptSubspt state.code final.code := by
  rw [evaluate] at run
  split at run
  · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
  · split at run
    · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
    · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
    · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
    · split at run
      · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
      · rename_i args body found
        split at run
        · simp at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
        · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
          simpa [decClock] using bodyIH body args (decClock 1 state) final result smaller run


private theorem evaluate_code_prefix {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state final : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (run : evaluate expressions env state = (result, final)) : sptSubspt state.code final.code := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List BvlSem.Value) (state final : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value), state.clock = clock →
      expsWeight expressions = weight → evaluate expressions env state = (result, final) →
      sptSubspt state.code final.code := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value)
            (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
            state.clock ≤ clock → expsWeight expressions < weight →
            evaluate expressions env state = (result, final) → sptSubspt state.code final.code := by
          intro expressions env state final result clockLe weightLt run
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state final result rfl rfl run
          · exact weightIH (expsWeight expressions) weightLt expressions env state final result clockEq rfl run
        have smaller : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value)
            (state final : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
            state.clock < clock → evaluate expressions env state = (result, final) →
            sptSubspt state.code final.code := by
          intro expressions env state final result clockLt run
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state final result rfl rfl run
        intro expressions env state final result stateClock measure run
        cases expressions with
        | nil => simp [evaluate] at run; rcases run with ⟨rfl, rfl⟩; exact subsptRefl _
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_cons_code_step first second tail env state final result ?_ ?_ run
            · intro last headResult headRun
              apply exprIH [first] env state last headResult (by omega) ?_ headRun
              simp only [expsWeight] at measure ⊢; have := expWeight_pos second; omega
            · intro start last tailResult bound tailRun
              apply exprIH (second :: tail) env start last tailResult (by omega) ?_ tailRun
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index =>
              rw [evaluate] at run
              split at run <;> simp at run
              all_goals rcases run with ⟨rfl, rfl⟩
              all_goals exact subsptRefl _
            | raise body =>
              apply evaluate_raise_code_step body env state final result ?_ run
              intro last bodyResult bodyRun
              apply exprIH [body] env state last bodyResult (by omega) ?_ bodyRun
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick body =>
              apply evaluate_tick_code_step body env state final result ?_ run
              intro start last bodyResult bound bodyRun
              exact smaller [body] env start last bodyResult (by omega) bodyRun
            | «let» bindings body =>
              apply evaluate_let_code_step bindings body env state final result ?_ ?_ run
              · intro last bindingResult bindingRun
                apply exprIH bindings env state last bindingResult (by omega) ?_ bindingRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro bodyEnv start last bodyResult bound bodyRun
                apply exprIH [body] bodyEnv start last bodyResult (by omega) ?_ bodyRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle body handler =>
              apply evaluate_handle_code_step body handler env state final result ?_ ?_ run
              · intro last bodyResult bodyRun
                apply exprIH [body] env state last bodyResult (by omega) ?_ bodyRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro value start last handlerResult bound handlerRun
                apply exprIH [handler] (value :: env) start last handlerResult (by omega) ?_ handlerRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse condition yes no =>
              apply evaluate_if_code_step condition yes no env state final result ?_ ?_ run
              · intro last testResult testRun
                apply exprIH [condition] env state last testResult (by omega) ?_ testRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro choice start last branchResult bound branchRun
                apply exprIH [if choice then yes else no] env start last branchResult (by omega) ?_ branchRun
                cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, expsWeight, expWeight] at measure ⊢ <;> omega
            | op op args =>
              apply evaluate_op_code_step op args env state final result ?_ run
              intro last argResult argRun
              apply exprIH args env state last argResult (by omega) ?_ argRun
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks location args =>
              apply evaluate_call_code_step ticks location args env state final result ?_ ?_ run
              · intro last argResult argRun
                apply exprIH args env state last argResult (by omega) ?_ argRun
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro body bodyEnv start last bodyResult bound bodyRun
                exact smaller [body] bodyEnv start last bodyResult (by omega) bodyRun
            | force location index =>
              apply evaluate_force_code_step location index env state final result ?_ run
              intro body bodyEnv start last bodyResult bound bodyRun
              exact smaller [body] bodyEnv start last bodyResult (by omega) bodyRun
  exact allRanks state.clock (expsWeight expressions) expressions env state final result rfl rfl run

/-- BVL evaluation preserves every code entry present at its start. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluateMono {C F : Type} (expressions : List Bvl.Exp) (env : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : evaluateTuple (expressions, env, state) = (result, final)) :
    sptSubspt state.code final.code :=
  evaluate_code_prefix expressions env state final result run


end Flapjack.Compiler.Backend.BvlProps
