import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyClock
import Aesop
/-! Clock preservation for the BVI primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A clock-clamped result cannot exceed the incoming clock. -/
theorem fixClock_clock_le {C F D G R : Type} (state : BviState C F) (result : R × BviState D G) :
    (fixClock state result).2.clock ≤ state.clock := Nat.min_le_left _ _

/-- Installation preserves the clock on successful results. -/
theorem doInstall_clock {C F R : Type} (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doInstall (R := R) args state = .val (value, next)) : next.clock = state.clock := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- A handled BVI-specific operation preserves the clock. -/
theorem doAppAux_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doAppAux op args state = some (some (value, next))) : next.clock = state.clock := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Clock preservation for the special-or-fallback dispatch. -/
theorem fallback_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doAppFallback op args state = .val (value, next)) : next.clock = state.clock := by
  unfold doAppFallback at run
  cases h : doAppAux op args state with
  | none => simp [h] at run
  | some option =>
    cases option with
    | some pair =>
      have eq : pair = (value, next) := by simpa [h] using run
      subst pair
      exact doAppAux_clock op args state next value h
    | none =>
      simp only [h] at run
      cases original : BvlSem.doApp op args (toBvl state) with
      | err error => cases error <;> simp [original] at run
      | val pair =>
        obtain ⟨originalValue, originalState⟩ := pair
        simp only [original, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have bound := BvlSem.doApp_clock op args (toBvl state) originalState _ original
        simpa [fromBvl, toBvl] using bound

/-- Successful BVI primitive applications preserve the clock. This is
untagged pending full dispatcher source qualification. -/
theorem doApp_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doApp op args state = .val (value, next)) : next.clock = state.clock := by
  cases op with
  | install => exact doInstall_clock args state next value run
  | label n => exact fallback_clock (.label n) args state next value (by simpa only [doApp] using run)
  | ffi n => exact fallback_clock (.ffi n) args state next value (by simpa only [doApp] using run)
  | intOp n => exact fallback_clock (.intOp n) args state next value (by simpa only [doApp] using run)
  | wordOp n => exact fallback_clock (.wordOp n) args state next value (by simpa only [doApp] using run)
  | blockOp n => exact fallback_clock (.blockOp n) args state next value (by simpa only [doApp] using run)
  | globOp n => exact fallback_clock (.globOp n) args state next value (by simpa only [doApp] using run)
  | memOp n => exact fallback_clock (.memOp n) args state next value (by simpa only [doApp] using run)
  | thunkOp n => exact fallback_clock (.thunkOp n) args state next value (by simpa only [doApp] using run)
end Flapjack.Compiler.Backend.BviSem
