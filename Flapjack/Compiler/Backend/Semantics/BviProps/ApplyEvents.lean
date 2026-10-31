import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyCode
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyEvents

/-! Event-prefix preservation for BVI primitives. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Installation leaves the FFI state untouched. -/
theorem doInstall_ffi {C F R : Type} (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doInstall (R := R) args s = .val (value, t)) : t.ffi = s.ffi := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- BVI-specific operations leave the FFI state untouched. -/
theorem doAppAux_ffi {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t))) : t.ffi = s.ffi := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- The BVI-specific and delegated primitive cases extend the I/O trace. -/
theorem doAppFallback_ioEvents_prefix {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppFallback op args s = .val (value, t)) : s.ffi.ioEvents <+: t.ffi.ioEvents := by
    unfold doAppFallback at run
    cases aux : doAppAux op args s with
    | none => simp [aux] at run
    | some inner =>
      cases inner with
      | some pair =>
        obtain ⟨v, next⟩ := pair
        simp [aux] at run
        obtain ⟨rfl, rfl⟩ := run
        rw [doAppAux_ffi op args s next v aux]
      | none =>
        simp only [aux] at run
        cases fallback : BvlSem.doApp op args (toBvl s) with
        | err error => cases error <;> simp [fallback] at run
        | val pair =>
          obtain ⟨v, next⟩ := pair
          simp [fallback] at run
          obtain ⟨rfl, rfl⟩ := run
          simpa [toBvl, fromBvl] using BvlProps.doApp_ioEvents_prefix op args (toBvl s) next v fallback

/-- A successful primitive application extends the I/O-event trace. This
is untagged while the dispatcher correspondence is under source review. -/
theorem doApp_ioEvents_prefix {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doApp op args s = .val (value, t)) : s.ffi.ioEvents <+: t.ffi.ioEvents := by
  cases op with
  | install => simp [doInstall_ffi args s t value run]
  | _ => simp only [doApp] at run; exact doAppFallback_ioEvents_prefix _ args s t value run

end Flapjack.Compiler.Backend.BviProps
