import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallPrimitives
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

/-! No-install invariants for the proof-side closure evaluator. Its evaluator
and state carriers still require HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Every body in the code store is free of installation. -/
def codeNoInstall (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Prop :=
  ∀ location arity body, code.lookup location = some (arity, body) → ClosLang.hasInstall body = false

/-- A successful direct code lookup returns safe arguments and a safe body. -/
theorem findCode_noInstall (location : Nat) (args output : List ClosSem.Value)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (argsOk : valuesNoInstall args = true) (codeOk : codeNoInstall code)
    (run : ClosSem.findCode location args code = some (output, body)) :
    valuesNoInstall output = true ∧ ClosLang.hasInstall body = false := by
  unfold ClosSem.findCode at run
  cases found : code.lookup location with
  | none => simp [found] at run
  | some entry =>
    rcases entry with ⟨arity, expression⟩
    by_cases same : args.length = arity
    · simp [found, same] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argsOk, codeOk location arity expression found⟩
    · simp [found, same] at run

/-- Successful global primitives leave code unchanged. -/
theorem applyGlobal_code {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyGlobal op args state = some (value, next)) : next.code = state.code := by
  unfold ClosSem.applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals (rcases run with ⟨_, rfl⟩; rfl)

/-- Successful memory primitives leave code unchanged. -/
theorem applyMemory_code {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyMemory op args state = some (value, next)) : next.code = state.code := by
  unfold ClosSem.applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- Successful ordinary primitives leave the code store unchanged. -/
theorem doApp_code {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp op args state = .val (value, next)) : next.code = state.code := by
  cases op with
  | globOp operation =>
    cases found : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      exact applyGlobal_code operation args state next value found
  | blockOp operation =>
    cases found : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyBlock_state operation args state next value found]
  | memOp operation =>
    cases found : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      exact applyMemory_code operation args state next value found
  | intOp operation =>
    cases found : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyNumeric_state (.intOp operation) args state next value found]
  | wordOp operation =>
    cases found : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyNumeric_state (.wordOp operation) args state next value found]
  | ffi | thunkOp =>
    simp only [ClosSem.doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals (rcases run with ⟨_, rfl⟩; rfl)
  | label | install => simp [ClosSem.doApp] at run

/-- Ordinary primitive dispatch never raises a language exception. -/
theorem doApp_not_raise {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (value : ClosSem.Value) :
    ClosSem.doApp op args state ≠ .err (.raise value) := by
  unfold ClosSem.doApp
  repeat' split
  all_goals simp_all
  all_goals split <;> simp_all

/-- The parts of a closure evaluator state relevant to the no-install invariant. -/
def evalStateNoInstall {C F : Type} (state : ClosSem.State C F) : Prop :=
  globalsNoInstall state.globals ∧ refsNoInstall state.refs ∧ codeNoInstall state.code

/-- The ordinary operation case preserves no-install results and state,
assuming the same for evaluation of its argument expressions. -/
theorem evaluate_ordinaryOp_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last)
    (run : ClosSem.evaluate [.op trace op args] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk argResult last =>
    rw [argsRun] at run
    obtain ⟨argOk, lastOk⟩ := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argOk, lastOk⟩
    | val arguments =>
      cases appRun : ClosSem.doApp op arguments.reverse last with
      | err error =>
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        constructor
        · cases error with
          | raise value => exact False.elim (doApp_not_raise op arguments.reverse last value appRun)
          | abort _ => trivial
        · exact lastOk
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨globalsOk, refsOk, codeOk⟩ := lastOk
        have argumentsOk : valuesNoInstall arguments.reverse = true :=
          (valuesNoInstall_reverse arguments).2 argOk
        obtain ⟨valueOk, finalGlobals, finalRefs⟩ :=
          doApp_noInstall op arguments.reverse last final value argumentsOk globalsOk refsOk appRun
        exact ⟨by simp [resultNoInstall, valuesNoInstall, valueOk],
          finalGlobals, finalRefs, by simpa [doApp_code op arguments.reverse last final value appRun] using codeOk⟩

end Flapjack.Compiler.Backend.ClosInterp
