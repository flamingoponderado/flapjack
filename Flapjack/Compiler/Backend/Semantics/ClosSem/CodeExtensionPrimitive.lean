import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtension

/-! Primitive operations under a code-map replacement. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Replace the code field in a successful primitive result. -/
def replaceCodeInOption {C F : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    Option (Value × State C F) → Option (Value × State C F) :=
  Option.map (fun (value, state) => (value, { state with code := code }))

/-- Global operations commute with replacement of the code field. -/
theorem applyGlobal_withCode {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (source : State C F) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    applyGlobal op args { source with code := code } = replaceCodeInOption code (applyGlobal op args source) := by
  unfold applyGlobal
  split <;> simp_all [replaceCodeInOption, Option.map_map, Function.comp_def]
  all_goals repeat' split <;> simp_all [Option.map_map, Function.comp_def]

/-- Block operations commute with replacement of the code field. -/
theorem applyBlock_withCode {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (source : State C F) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    applyBlock op args { source with code := code } = replaceCodeInOption code (applyBlock op args source) := by
  unfold applyBlock
  split <;> simp_all [replaceCodeInOption]
  all_goals repeat' split <;> simp_all

/-- Memory operations commute with replacement of the code field. -/
theorem applyMemory_withCode {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (source : State C F) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    applyMemory op args { source with code := code } = replaceCodeInOption code (applyMemory op args source) := by
  unfold applyMemory
  split <;> simp_all [replaceCodeInOption]
  all_goals repeat' first | split | (congr 1; funext _) | simp_all

/-- Numeric operations commute with replacement of the code field. -/
theorem applyNumeric_withCode {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source : State C F) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    applyNumeric op args { source with code := code } = replaceCodeInOption code (applyNumeric op args source) := by
  unfold applyNumeric
  split <;> simp_all [replaceCodeInOption, Option.map_map, Function.comp_def]

/-- Replacing the code map commutes with ordinary primitive dispatch. -/
theorem doApp_withCode {C F : Type} (op : ClosLang.Op) (values : List Value)
    (source : State C F) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    doApp op values { source with code := code } =
      match doApp op values source with
      | .err error => .err error
      | .val (value, next) => .val (value, { next with code := code }) := by
  cases op with
  | globOp operation =>
    simp only [doApp, applyGlobal_withCode, replaceCodeInOption]
    cases applyGlobal operation values source <;> simp_all
  | blockOp operation =>
    simp only [doApp, applyBlock_withCode, replaceCodeInOption]
    cases applyBlock operation values source <;> simp_all
  | memOp operation =>
    simp only [doApp, applyMemory_withCode, replaceCodeInOption]
    cases applyMemory operation values source <;> simp_all
  | intOp operation =>
    simp only [doApp, applyNumeric_withCode, replaceCodeInOption]
    cases applyNumeric (.intOp operation) values source <;> simp_all
  | wordOp operation =>
    simp only [doApp, applyNumeric_withCode, replaceCodeInOption]
    cases applyNumeric (.wordOp operation) values source <;> simp_all
  | label index => rfl
  | install => rfl
  | ffi name =>
    unfold doApp
    split <;> simp_all
    all_goals repeat' first | split | simp_all
    all_goals aesop
  | thunkOp operation =>
    unfold doApp
    split <;> simp_all
    all_goals repeat' first | split | simp_all
    all_goals aesop

/-- Primitive errors agree under a code extension. -/
theorem doApp_codeExtension_error {C F : Type} (op : ClosLang.Op) (values : List Value)
    (source target : State C F) (error : ErrorResult Value)
    (run : doApp op values source = .err error) (related : CodeExtension source target) :
    doApp op values target = .err error := by
  rw [related.1, doApp_withCode, run]

/-- A successful primitive returns the same value and preserves the code
extension relation. -/
theorem doApp_codeExtension_value {C F : Type} (op : ClosLang.Op) (values : List Value)
    (source target next : State C F) (value : Value)
    (run : doApp op values source = .val (value, next)) (related : CodeExtension source target) :
    ∃ targetNext, doApp op values target = .val (value, targetNext) ∧ CodeExtension next targetNext := by
  refine ⟨{ next with code := target.code }, ?_, ?_⟩
  · rw [related.1, doApp_withCode, run]
  · have fields := doApp_codeOracle op values source next value run
    exact ⟨rfl, by simpa [fields.1] using related.2.1, by simpa [fields.2] using related.2.2⟩

/-- Evaluator simulation at one source state under safe code extension. -/
def EvalCodeExtensionAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (target : State C F) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → result ≠ .err (.abort .typeError) →
    CodeExtension source target →
    ∃ targetNext, evaluate expressions env target = (result, targetNext) ∧ CodeExtension next targetNext

/-- Ordinary primitive expressions preserve a safe code extension when their
argument evaluation does. -/
theorem evaluate_ordinaryOp_codeExtension {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (source : State C F)
    (argsIH : EvalCodeExtensionAt source args) : EvalCodeExtensionAt source [.op trace op args] := by
  intro env target result next run noType states
  rw [evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.err error) next argsRun noType states
      refine ⟨targetMiddle, ?_, middleRel⟩
      rw [evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.val values) middle argsRun argsNoType states
      dsimp only at run
      cases appRun : doApp op values.reverse middle with
      | err error =>
        rw [appRun] at run
        cases run
        have nextApp := doApp_codeExtension_error op values.reverse next targetMiddle error appRun middleRel
        refine ⟨targetMiddle, ?_, middleRel⟩
        rw [evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetRun]
        dsimp only
        rw [nextApp]
      | val pair =>
        obtain ⟨value, last⟩ := pair
        rw [appRun] at run
        cases run
        obtain ⟨targetLast, nextApp, lastRel⟩ :=
          doApp_codeExtension_value op values.reverse middle targetMiddle next value appRun middleRel
        refine ⟨targetLast, ?_, lastRel⟩
        rw [evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetRun]
        dsimp only
        rw [nextApp]
end Flapjack.Compiler.Backend.ClosSem
