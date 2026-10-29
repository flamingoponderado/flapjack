import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterCases

/-! Invocation of the installed interpreter, used by its recursive expression
cases. Evaluator and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp

/-- A three-argument interpreter invocation spends three clock units before
entering the interpreter body. The argument evaluations are pure and retain
the state, as they do for the generated variable and projection expressions. -/
theorem evaluate_interpreter_call {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (env : List ClosSem.Value)
    (environmentExpr flagExpr codeExpr : ClosLang.Exp)
    (environmentValue flagValue codeValue : ClosSem.Value)
    (environmentRun : ClosSem.evaluate [environmentExpr] env target = (.val [environmentValue], target))
    (flagRun : ClosSem.evaluate [flagExpr] env target = (.val [flagValue], target))
    (codeRun : ClosSem.evaluate [codeExpr] env target = (.val [codeValue], target))
    (clock : 3 ≤ target.clock) :
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [environmentExpr]
    let second := ClosLang.Exp.app .none none first [flagExpr]
    ClosSem.evaluate [.app .none none second [codeExpr]] env target =
      ClosSem.evaluate [closInterpreterBody] [codeValue, flagValue, environmentValue] (ClosSem.decClock 3 target) := by
  dsimp only
  let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
  let first := ClosLang.Exp.app .none none global [environmentExpr]
  let second := ClosLang.Exp.app .none none first [flagExpr]
  let original := ClosSem.Value.closure none [] [] 1 closInterpreter
  let firstValue := ClosSem.Value.closure none [] [environmentValue] 1
    (.fn (Flapjack.Basis.Pure.MlString.ofString "exp") none none 1 closInterpreterBody)
  let secondValue := ClosSem.Value.closure none [] [flagValue, environmentValue] 1 closInterpreterBody
  have positive : 1 ≤ target.maxApp := by
    rcases related.1 with ⟨_, _, _, maxEq, maxPositive, _⟩
    omega
  have globalRun : ClosSem.evaluate [global] env target = (.val [original], target) := by
    simpa [global, original] using evaluate_global_zero source target related .none env target.clock
  have firstCall : ClosSem.destClosure target.maxApp none original [environmentValue] =
      some (.fullApp closInterpreter [environmentValue] []) := by
    simp [original, ClosSem.destClosure, ClosSem.checkLoc, positive]
  have firstRun : ClosSem.evaluate [first] env target = (.val [firstValue], ClosSem.decClock 1 target) := by
    rw [show ClosSem.evaluate [first] env target = ClosSem.evaluateApp none original [environmentValue] target from
      evaluate_unary_app _ _ _ _ _ _ _ _ environmentRun globalRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ firstCall]
    have nonzero : target.clock ≠ 0 := by omega
    simp [closInterpreter, ClosSem.evaluate, ClosSem.decClock, positive, firstValue, nonzero]
  have secondCall : ClosSem.destClosure (ClosSem.decClock 1 target).maxApp none firstValue [flagValue] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "exp") none none 1 closInterpreterBody)
        [flagValue, environmentValue] []) := by
    simp [firstValue, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, positive]
  have secondRun : ClosSem.evaluate [second] env target =
      (.val [secondValue], ClosSem.decClock 1 (ClosSem.decClock 1 target)) := by
    rw [show ClosSem.evaluate [second] env target =
      ClosSem.evaluateApp none firstValue [flagValue] (ClosSem.decClock 1 target) from
      evaluate_unary_app _ _ _ _ _ _ _ _ flagRun firstRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ secondCall]
    have nonzero : target.clock - 1 ≠ 0 := by omega
    simp [ClosSem.evaluate, ClosSem.decClock, positive, secondValue, nonzero]
  have thirdCall : ClosSem.destClosure (ClosSem.decClock 1 (ClosSem.decClock 1 target)).maxApp none secondValue [codeValue] =
      some (.fullApp closInterpreterBody [codeValue, flagValue, environmentValue] []) := by
    simp [secondValue, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, positive]
  change ClosSem.evaluate [.app .none none second [codeExpr]] env target = _
  rw [evaluate_unary_app second codeExpr env target target (ClosSem.decClock 1 (ClosSem.decClock 1 target))
    codeValue secondValue codeRun secondRun]
  rw [FlatToClos.evaluateApp_unary _ _ _ _ _ thirdCall]
  have nonzero : target.clock - 2 ≠ 0 := by omega
  simp [ClosSem.decClock, Nat.sub_sub, nonzero]


/-- A selected interpreter replacement enters the interpreter body with the
encoded original expression and an empty environment. -/
theorem evaluate_optInterp {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (expression replacement : ClosLang.Exp)
    (selected : optInterp expression = some replacement) (clock : 3 ≤ target.clock) :
    ClosSem.evaluate [replacement] [] target =
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant expression), .block 0 [], .block 0 []]
        (ClosSem.decClock 3 target) := by
  unfold optInterp at selected
  split at selected
  · simp only [Option.some.injEq] at selected
    subst replacement
    exact evaluate_interpreter_call source target related []
      (.op .none (.blockOp (.cons 0)) []) (.op .none (.blockOp (.cons 0)) [])
      (.op .none (.blockOp (.constant (toConstant expression))) [])
      (.block 0 []) (.block 0 []) (ClosSem.makeConst (toConstant expression))
      (evaluate_cons_nil .none 0 [] target) (evaluate_cons_nil .none 0 [] target)
      (evaluate_constant .none (toConstant expression) [] target) clock
  · contradiction

end Flapjack.Compiler.Backend.ClosInterp
