import Flapjack.Compiler.Backend.ClosInterp.Proofs.EvaluateRev
import Flapjack.Compiler.Backend.ClosInterp.Proofs.Simulation

/-! Base cases of the interpreter expression simulation. The evaluator and
state carriers are proof-side and await cross-language review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The interpreter maps the empty expression list to the encoded empty list. -/
theorem interpreter_list_nil {C F : Type} (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstantList []), .block 1 [], ClosSem.listToValue env] state =
      (.val [ClosSem.listToValue []], state) := by
  simp [closInterpreterBody, interpreterVar_eq, interpreterGetEl_eq, interpreterCons_eq, interpreterApp_eq, toConstantList, ClosSem.makeConst, ClosSem.evaluate,
    ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.asBool, ClosSem.boolValue,
    ClosSem.listToValue, BackendCommon.trueTag, BackendCommon.nilTag]


/-- Integer constants decode to the same value without changing state. -/
theorem interpreter_integer_constant {C F : Type} (number : Int) (env : List ClosSem.Value)
    (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant (.op .none (.intOp (.const number)) [])),
        .block 0 [], ClosSem.listToValue env] state = (.val [.number number], state) := by
  simp [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCons_eq, interpreterApp_eq, toConstant, toConstantOp, ClosSem.makeConst,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.asBool,
    ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag]


/-- A closure constant is decoded to its runtime value. -/
theorem interpreter_block_constant {C F : Type} (constant : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant (.op .none (.blockOp (.constant constant)) [])),
        .block 0 [], ClosSem.listToValue env] state = (.val [ClosSem.makeConst constant], state) := by
  simp [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCons_eq, interpreterApp_eq, toConstant, toConstantOp, ClosSem.makeConst,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.asBool,
    ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag]

/-- A nullary constructor is decoded to its corresponding block. -/
theorem interpreter_nullary_constructor {C F : Type} (tag : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant (.op .none (.blockOp (.cons tag)) [])),
        .block 0 [], ClosSem.listToValue env] state = (.val [.block tag []], state) := by
  simp [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCons_eq, interpreterApp_eq, toConstant, toConstantOp, ClosSem.makeConst,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.asBool,
    ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag]


/-- Integer-constant case of the interpreter simulation. The source and
target evaluator carriers remain pending HOL correspondence review. -/
theorem interpreter_correct_integer_constant {C F : Type} (trace : BackendCommon.Tra) (number : Int)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.intOp (.const number)) []] env source = (result, sourceFinal))
    (_valid : canInterpret (.op trace (.intOp (.const number)) []) = true)
    (_assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.intOp (.const number)) [])),
          .block 0 [], ClosSem.listToValue env] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have sourceRun : ClosSem.evaluate [.op trace (.intOp (.const number)) []] env source =
      (.val [.number number], source) := by
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
  rw [sourceRun] at run
  cases run
  refine ⟨0, target, ?_, related⟩
  simpa [toConstant] using interpreter_integer_constant number env target

/-- Empty expression-list case of the interpreter simulation. -/
theorem interpreter_correct_list_nil {C F : Type}
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [] env source = (result, sourceFinal))
    (_valid : canInterpretList [] = true) (_assumption : InterpAssum C F source.clock)
    (related : StateRel source target) (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal targetResult,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList []), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (targetResult, targetFinal) ∧
      StateRel sourceFinal targetFinal ∧
      (match result with
       | .val values => targetResult = .val [ClosSem.listToValue values]
       | .err _ => result = targetResult) := by
  simp only [ClosSem.evaluate] at run
  cases run
  refine ⟨0, target, .val [ClosSem.listToValue []], ?_, related, rfl⟩
  simpa using interpreter_list_nil env target

end Flapjack.Compiler.Backend.ClosInterp
