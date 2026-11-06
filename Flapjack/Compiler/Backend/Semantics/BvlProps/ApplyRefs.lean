import Flapjack.Compiler.Backend.Semantics.BvlProps.BuildRefs
import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyClock

/-! Reference-domain preservation for BVL primitives. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Updating a finite map never removes an existing key. -/
theorem refs_update_mono (refs : HolFiniteMapExact Nat (Ref Value)) (index key : Nat)
    (value : Ref Value) (present : refs.lookup key ≠ none) :
    (refs.updateEq (index, value)).lookup key ≠ none := by
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  split <;> simp_all

/-- Successful global operations leave the reference domain unchanged. -/
theorem applyGlobal_refs_mono {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyGlobal op args state = some (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Numeric primitives leave the reference domain unchanged. -/
theorem applyNumeric_refs_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : applyNumeric op args state = some (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Block operations preserve the reference domain, including constant
construction. This is untagged Flapjack infrastructure for `do_app_refs_SUBSET`. -/
theorem applyBlock_refs_mono {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyBlock op args state = some (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop (add safe forward doBuildConst_refs_mono)

/-- Memory operations preserve the reference domain when successful. -/
theorem applyMemory_refs_mono {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyMemory op args state = some (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (apply refs_update_mono; exact present)
  all_goals try (rcases run with ⟨_, _, _, rfl⟩; exact refs_update_mono _ _ _ _ present)
  all_goals try (rcases run with ⟨_, _, _, _, _, rfl⟩; exact refs_update_mono _ _ _ _ present)
  all_goals try (rcases h with ⟨_, _, _, rfl⟩; exact refs_update_mono _ _ _ _ present)

/-- Successful dynamic installation leaves references unchanged. -/
theorem doInstall_refs_mono {C F R : Type} (args : List Value) (state next : State C F)
    (value : Value) (run : doInstall (R := R) args state = .val (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful primitive application preserves the input reference domain. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_refs_SUBSET"
  (fmap_as_finite_support := [refs])]
theorem doApp_refs_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (value : Value) (run : doApp op args state = .val (value, next))
    (key : Nat) (present : state.refs.lookup key ≠ none) : next.refs.lookup key ≠ none := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_refs_mono operation args state next value h key present
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_refs_mono operation args state next value h key present
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_refs_mono operation args state next value h key present
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_refs_mono (.intOp operation) args state next value h key present
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_refs_mono (.wordOp operation) args state next value h key present
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals rcases run with ⟨_, rfl⟩
    all_goals exact refs_update_mono _ _ _ _ present
  | label =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
  | install => exact doInstall_refs_mono args state next value run key present

end Flapjack.Compiler.Backend.BvlProps
