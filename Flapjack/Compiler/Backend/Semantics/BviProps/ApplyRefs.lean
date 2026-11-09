import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyRefs

/-! Reference-domain preservation for BVI primitive operations. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Flapjack infrastructure: a handled BVI-specific primitive preserves
previously allocated reference keys. -/
theorem doAppAux_refs_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t)))
    (key : Nat) (present : s.refs.lookup key ≠ none) : t.refs.lookup key ≠ none := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop (config := {warnOnNonterminal := false}) (add safe forward finaliseCons_domain)
  all_goals simp_all [FUPDATE_HOL]
  all_goals split at * <;> simp_all

/-- Flapjack infrastructure: successful installation preserves references. -/
theorem doInstall_refs_mono {C F R : Type} (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doInstall (R := R) args s = .val (value, t))
    (key : Nat) (present : s.refs.lookup key ≠ none) : t.refs.lookup key ≠ none := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Flapjack infrastructure: successful BVI primitive application preserves
every previously allocated key, including through the BVL fallback. -/
theorem doApp_refs_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doApp op args s = .val (value, t))
    (key : Nat) (present : s.refs.lookup key ≠ none) : t.refs.lookup key ≠ none := by
  cases op with
  | install => exact doInstall_refs_mono args s t value run key present
  | _ =>
    simp only [doApp, doAppFallback] at run
    repeat' split at run
    all_goals simp_all
    all_goals try (exact doAppAux_refs_mono _ _ s t value (by assumption) key present)
    all_goals try (rcases run with ⟨_, rfl⟩; exact BvlProps.doApp_refs_mono _ _ (toBvl s) _ _ (by assumption) key present)

end Flapjack.Compiler.Backend.BviProps
