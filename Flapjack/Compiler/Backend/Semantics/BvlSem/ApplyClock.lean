import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
import Aesop

/-! Clock preservation for the proof-side BVL primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- Global primitives leave the clock unchanged. -/
theorem applyGlobal_clock {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyGlobal op args state = some (value, next)) :
    next.clock = state.clock := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Block primitives leave the state unchanged. -/
theorem applyBlock_clock {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyBlock op args state = some (value, next)) :
    next.clock = state.clock := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Integer and word primitives leave the state unchanged. -/
theorem applyNumeric_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : applyNumeric op args state = some (value, next)) :
    next.clock = state.clock := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Memory primitives may update references but leave the clock unchanged. -/
theorem applyMemory_clock {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyMemory op args state = some (value, next)) :
    next.clock = state.clock := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- A successful installation preserves the clock. -/
theorem doInstall_clock {C F R : Type} (args : List Value)
    (state next : State C F) (value : Value) (run : doInstall (R := R) args state = .val (value, next)) :
    next.clock = state.clock := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- A successful primitive application never changes the clock. This is a
proof-side invariant, pending correspondence review of the dispatcher. -/
theorem doApp_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : doApp op args state = .val (value, next)) :
    next.clock = state.clock := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_clock operation args state next value h
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_clock operation args state next value h
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_clock operation args state next value h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_clock (.intOp operation) args state next value h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_clock (.wordOp operation) args state next value h
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
  | install => exact doInstall_clock args state next value run

end Flapjack.Compiler.Backend.BvlSem
