import Flapjack.Compiler.Backend.ClosLang.Pure
import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
import Aesop

/-! Purity properties of proof-side closure primitives. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A successful pure global operation does not change the state. -/
private theorem applyGlobal_pure {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (source next : State C F) (value : Value) (pure : ClosLang.pureOp (.globOp op) = true)
    (run : applyGlobal op args source = some (value, next)) : next = source := by
  cases op <;> simp_all [ClosLang.pureOp, applyGlobal]
  all_goals aesop

/-- Block and numeric operations do not change the state on success. -/
private theorem applyBlock_pure {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (source next : State C F) (value : Value) (run : applyBlock op args source = some (value, next)) :
    next = source := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

private theorem applyNumeric_pure {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : State C F) (value : Value) (run : applyNumeric op args source = some (value, next)) :
    next = source := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Memory operations classified as pure leave the state unchanged. -/
private theorem applyMemory_pure {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (source next : State C F) (value : Value) (pure : ClosLang.pureOp (.memOp op) = true)
    (run : applyMemory op args source = some (value, next)) : next = source := by
  cases op <;> simp_all [ClosLang.pureOp]
  all_goals unfold applyMemory at run
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all)
  all_goals aesop

/-- Successful pure primitives leave the complete closure state unchanged. -/
theorem doApp_pure_success {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source next : State C F) (value : Value) (pure : ClosLang.pureOp op = true)
    (run : doApp op args source = .val (value, next)) : next = source := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args source with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_pure operation args source next value pure h
  | blockOp operation =>
    cases h : applyBlock operation args source with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_pure operation args source next value h
  | memOp operation =>
    cases h : applyMemory operation args source with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_pure operation args source next value pure h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args source with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_pure (.intOp operation) args source next value h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args source with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_pure (.wordOp operation) args source next value h
  | ffi | thunkOp => simp [ClosLang.pureOp] at pure
  | label | install => simp [doApp] at run

/-- A pure primitive can fail only with a type error. -/
theorem doApp_pure_error {C F : Type} (op : ClosLang.Op) (args : List Value) (source : State C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value) (pure : ClosLang.pureOp op = true)
    (run : doApp op args source = .err error) : error = .abort .typeError := by
  cases op <;> simp_all [ClosLang.pureOp, doApp]
  all_goals split at run <;> simp_all

end Flapjack.Compiler.Backend.ClosProps
