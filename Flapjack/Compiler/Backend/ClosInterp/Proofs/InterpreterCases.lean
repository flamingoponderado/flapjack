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


/-- An evaluated Boolean condition selects the corresponding closure branch. -/
private theorem evaluate_if_condition {C F : Type} (condition yes no : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (choice : Bool)
    (test : ClosSem.evaluate [condition] env state = (.val [ClosSem.boolValue choice], state)) :
    ClosSem.evaluate [.ifThenElse .none condition yes no] env state =
      ClosSem.evaluate [if choice then yes else no] env state := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, test]
  cases choice <;> rfl

/-- Decoding a variable expression invokes the interpreter's environment
lookup helper and returns the indexed value. -/
theorem interpreter_variable {C F : Type} (index : Nat) (env : List ClosSem.Value)
    (state : ClosSem.State C F) (bound : index < env.length) (positive : 1 ≤ state.maxApp) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant (.var .none index)), .block 0 [], ClosSem.listToValue env]
      { state with clock := (2 * index + 2) + state.clock } = (.val [env[index]], state) := by
  let encoded := ClosSem.Value.block 0 [.number (Int.ofNat index)]
  let vars := [encoded, ClosSem.Value.block 0 [], ClosSem.listToValue env]
  let current := { state with clock := (2 * index + 2) + state.clock }
  simp only [toConstant, ClosSem.makeConst, List.map_cons, List.map_nil]
  change ClosSem.evaluate [closInterpreterBody] vars current = _
  simp only [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterApp_eq]
  rw [evaluate_if_condition (.var .none 1) _ _ vars current false (by
    simp [vars, ClosSem.evaluate, ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 2)) [.var .none 0]) _ _ vars current false (by
    simp [vars, encoded, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 1 1)) [.var .none 0]) _ _ vars current false (by
    simp [vars, encoded, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 2 1)) [.var .none 0]) _ _ vars current false (by
    simp [vars, encoded, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 1)) [.var .none 0]) _ _ vars current true (by
    simp [vars, encoded, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rw [ClosSem.evaluate]
  have pos : 1 ≤ current.maxApp := by simpa [current] using positive
  simp [pos]
  let recFun := ClosSem.Value.recclosure none [] vars
    [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0
  let bodyEnv := recFun :: vars
  let indexExp := ClosLang.Exp.op .none (.blockOp (.elemAt 0)) [.var .none 1]
  let inner := ClosLang.Exp.app .none none (.var .none 0) [indexExp]
  let value := ClosSem.Value.closure none [] (.number (Int.ofNat index) :: recFun :: vars) 1 closInterpEl
  have envRun : ClosSem.evaluate [.var .none 3] bodyEnv current = (.val [ClosSem.listToValue env], current) := by
    simp [bodyEnv, vars, ClosSem.evaluate]
  have indexRun : ClosSem.evaluate [indexExp] bodyEnv current = (.val [.number (Int.ofNat index)], current) := by
    simp [indexExp, bodyEnv, vars, encoded, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have fnRun : ClosSem.evaluate [.var .none 0] bodyEnv current = (.val [recFun], current) := by
    simp [bodyEnv, ClosSem.evaluate]
  have recCall : ClosSem.destClosure current.maxApp none recFun [.number (Int.ofNat index)] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)
        (.number (Int.ofNat index) :: recFun :: vars) []) := by
    simp [recFun, ClosSem.destClosure, ClosSem.checkLoc, pos]
  have innerRun : ClosSem.evaluate [inner] bodyEnv current = (.val [value], ClosSem.decClock 1 current) := by
    rw [show ClosSem.evaluate [inner] bodyEnv current = ClosSem.evaluateApp none recFun [.number (Int.ofNat index)] current from
      evaluate_unary_app _ _ _ _ _ _ _ _ indexRun fnRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ recCall]
    have nonzero : current.clock ≠ 0 := by simp [current]
    simp [ClosSem.evaluate, ClosSem.decClock, pos, value, nonzero]
  have call : ClosSem.destClosure (ClosSem.decClock 1 current).maxApp none value [ClosSem.listToValue env] =
      some (.fullApp closInterpEl (ClosSem.listToValue env :: .number (Int.ofNat index) :: recFun :: vars) []) := by
    simp [value, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, pos]
  change ClosSem.evaluate [.app .none none inner [.var .none 3]] bodyEnv current = _
  rw [evaluate_unary_app inner (.var .none 3) bodyEnv current current (ClosSem.decClock 1 current)
    (ClosSem.listToValue env) value envRun innerRun]
  rw [FlatToClos.evaluateApp_unary _ _ _ _ _ call]
  have nonzero : (ClosSem.decClock 1 current).clock ≠ 0 := by simp [ClosSem.decClock, current]
  simp only [nonzero, ↓reduceIte]
  have clocks : ClosSem.decClock 1 (ClosSem.decClock 1 current) =
      { state with clock := state.clock + 2 * index } := by
    simp only [ClosSem.decClock, current]
    congr 1
    omega
  rw [clocks]
  simpa [recFun] using
    evaluate_closInterpEl index env vars vars env[index] state positive (by simp [bound])


/-- Variable case of the interpreter simulation, including rejection of an
out-of-range source lookup by the original type-error exclusion. -/
theorem interpreter_correct_variable {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.var trace index] env source = (result, sourceFinal))
    (_valid : canInterpret (.var trace index) = true)
    (_assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.var trace index)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases found : env[index]? with
  | none =>
    simp [ClosSem.evaluate, found] at run
    exact (notTypeError run.1.symm).elim
  | some value =>
    obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
    simp [ClosSem.evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    have positive : 1 ≤ target.maxApp := by
      rcases related.1 with ⟨_, _, _, maxEq, maxPositive, _⟩
      omega
    refine ⟨2 * index + 2, target, ?_, related⟩
    simpa [toConstant, equal] using interpreter_variable index env target bound positive


/-- An encoded global read has the same result as the original global read. -/
theorem interpreter_global {C F : Type} (index : Nat) (env : List ClosSem.Value)
    (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant (.op .none (.globOp (.global index)) [])),
        .block 0 [], ClosSem.listToValue env] state =
      ClosSem.evaluate [.op .none (.globOp (.global index)) []] env state := by
  have nonnegative : ¬ ((index : Int) < 0) := by
    have bound : 0 ≤ (index : Int) := Int.natCast_nonneg _
    omega
  simp [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCons_eq, interpreterApp_eq, toConstant, toConstantOp, ClosSem.makeConst,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal, ClosSem.applyBlock, ClosSem.asBool,
    ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag, nonnegative]


/-- Global-read case of the interpreter simulation. -/
theorem interpreter_correct_global {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.globOp (.global index)) []] env source = (result, sourceFinal))
    (_valid : canInterpret (.op trace (.globOp (.global index)) []) = true)
    (_assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.globOp (.global index)) [])),
          .block 0 [], ClosSem.listToValue env] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have globals : source.globals = target.globals := related.1.2.2.2.2.2.2.2.1
  cases found : (ClosSem.getGlobal index source.globals).join with
  | none =>
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal, found] at run
    exact (notTypeError run.1.symm).elim
  | some value =>
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal, found] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨0, target, ?_, related⟩
    rw [show ClosSem.makeConst (toConstant (.op trace (.globOp (.global index)) [])) =
      ClosSem.makeConst (toConstant (.op .none (.globOp (.global index)) [])) by rfl]
    have targetFound : (ClosSem.getGlobal index target.globals).join = some value := by
      simpa only [← globals] using found
    have targetRun : ClosSem.evaluate [.op .none (.globOp (.global index)) []] env target =
        (.val [value], target) := by
      simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal, targetFound]
    simpa using (interpreter_global index env target).trans targetRun


/-- Constant-block case of the interpreter simulation. -/
theorem interpreter_correct_block_constant {C F : Type} (trace : BackendCommon.Tra) (constant : ClosLang.Const)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.blockOp (.constant constant)) []] env source = (result, sourceFinal))
    (_valid : canInterpret (.op trace (.blockOp (.constant constant)) []) = true)
    (_assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.blockOp (.constant constant)) [])),
          .block 0 [], ClosSem.listToValue env] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have sourceRun : ClosSem.evaluate [.op trace (.blockOp (.constant constant)) []] env source =
      (.val [ClosSem.makeConst constant], source) := by
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  rw [sourceRun] at run
  cases run
  refine ⟨0, target, ?_, related⟩
  simpa [toConstant] using interpreter_block_constant constant env target

/-- Nullary-constructor case of the interpreter simulation. -/
theorem interpreter_correct_nullary_constructor {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.blockOp (.cons tag)) []] env source = (result, sourceFinal))
    (_valid : canInterpret (.op trace (.blockOp (.cons tag)) []) = true)
    (_assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.blockOp (.cons tag)) [])),
          .block 0 [], ClosSem.listToValue env] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have sourceRun : ClosSem.evaluate [.op trace (.blockOp (.cons tag)) []] env source =
      (.val [.block tag []], source) := by
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  rw [sourceRun] at run
  cases run
  refine ⟨0, target, ?_, related⟩
  simpa [toConstant] using interpreter_nullary_constructor tag env target

end Flapjack.Compiler.Backend.ClosInterp
