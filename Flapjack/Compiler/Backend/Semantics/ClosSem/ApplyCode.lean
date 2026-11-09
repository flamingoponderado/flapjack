module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
public import Aesop

@[expose] public section

/-! Code and oracle fields of successful closure primitives. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Successful global primitives preserve the code and oracle fields. -/
private theorem applyGlobal_codeOracle {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyGlobal op args state = some (value, next)) : next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful block primitives preserve the code and oracle fields. -/
private theorem applyBlock_codeOracle {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyBlock op args state = some (value, next)) : next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful numeric primitives preserve the code and oracle fields. -/
private theorem applyNumeric_codeOracle {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyNumeric op args state = some (value, next)) : next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful memory primitives preserve the code and oracle fields. -/
private theorem applyMemory_codeOracle {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyMemory op args state = some (value, next)) : next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- The primitive dispatcher preserves code and compile oracle on success.
This proof-side invariant is untagged pending HOL correspondence review. -/
theorem doApp_codeOracle {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) : next.code = state.code ∧ next.compileOracle = state.compileOracle := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_codeOracle operation args state next value h
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_codeOracle operation args state next value h
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_codeOracle operation args state next value h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_codeOracle (.intOp operation) args state next value h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_codeOracle (.wordOp operation) args state next value h
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | install => simp [doApp] at run

end Flapjack.Compiler.Backend.ClosSem
