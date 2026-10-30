import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyGlobal
import Flapjack.Misc.Sptree.Subspt

/-! Code-tree growth during BVI primitive application. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Flapjack helper: installation only extends the BVI code tree. -/
theorem doInstall_code_mono {C F R : Type} (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doInstall (R := R) args s = .val (value, t)) : sptSubspt s.code t.code := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try (rcases run with ⟨rfl, rfl⟩; exact sptSubsptUnion _ _)

/-- Flapjack helper: handled BVI-specific operations do not alter code. -/
theorem doAppAux_code {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t))) : t.code = s.code := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Flapjack helper: successful BVI primitive applications preserve every
previous code-tree entry. -/
theorem doApp_code_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doApp op args s = .val (value, t)) : sptSubspt s.code t.code := by
  cases op with
  | install => exact doInstall_code_mono args s t value run
  | _ =>
    simp only [doApp, doAppFallback] at run
    repeat' split at run
    all_goals simp_all
    all_goals try (have eq := doAppAux_code _ _ s t value (by assumption); rw [eq]; exact fun k h => ⟨h, rfl⟩)
    all_goals rcases run with ⟨_, rfl⟩
    all_goals exact fun k h => ⟨h, rfl⟩

end Flapjack.Compiler.Backend.BviProps
