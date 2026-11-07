import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyClock
import Aesop

/-! Preservation of an initialized BVI global pointer by primitives. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Flapjack helper: successful installation leaves the global pointer intact. -/
theorem doInstall_global {C F R : Type} (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doInstall (R := R) args s = .val (value, t)) : t.global = s.global := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Flapjack helper: handled BVI primitives never remove an initialized global. -/
theorem doAppAux_global {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t)))
    (present : s.global.isSome = true) : t.global.isSome = true := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Flapjack helper: successful BVI primitive applications preserve the
presence of the global pointer, including BVL fallback. -/
theorem doApp_global {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doApp op args s = .val (value, t))
    (present : s.global.isSome = true) : t.global.isSome = true := by
  cases op with
  | install => simpa [doInstall_global args s t value run] using present
  | _ =>
    simp only [doApp, doAppFallback] at run
    repeat' split at run
    all_goals simp_all
    all_goals try (apply doAppAux_global _ _ s t value <;> assumption)
    all_goals rcases run with ⟨_, rfl⟩
    all_goals exact present

end Flapjack.Compiler.Backend.BviProps
