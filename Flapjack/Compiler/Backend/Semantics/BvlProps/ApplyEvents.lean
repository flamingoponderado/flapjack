import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
import Flapjack.FfiHOL
import Aesop

/-! Event preservation for BVL primitives. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

namespace EventsCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EventsCarrier

/-- Global primitives leave the FFI state unchanged. -/
theorem applyGlobal_ffi {C F : Type} (op : ClosLang.GlobOp) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : applyGlobal op args state = some (value, next)) : next.ffi = state.ffi := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Block primitives leave the FFI state unchanged. -/
theorem applyBlock_ffi {C F : Type} (op : ClosLang.BlockOp) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : applyBlock op args state = some (value, next)) : next.ffi = state.ffi := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Numeric primitives leave the FFI state unchanged. -/
theorem applyNumeric_ffi {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : applyNumeric op args state = some (value, next)) : next.ffi = state.ffi := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Memory primitives leave the FFI state unchanged. -/
theorem applyMemory_ffi {C F : Type} (op : ClosLang.MemOp) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : applyMemory op args state = some (value, next)) : next.ffi = state.ffi := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- Successful primitive application extends the event trace. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem doApp_ioEvents_prefix {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state next : Flapjack.Compiler.Backend.BvlSem.State C F) (value : BvlSem.Value)
    (run : doApp op args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op with
  | globOp operation =>
    cases found : applyGlobal operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      rw [applyGlobal_ffi operation args state next value found]
      exact List.prefix_refl _
  | blockOp operation =>
    cases found : applyBlock operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      rw [applyBlock_ffi operation args state next value found]
      exact List.prefix_refl _
  | memOp operation =>
    cases found : applyMemory operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      rw [applyMemory_ffi operation args state next value found]
      exact List.prefix_refl _
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      rw [applyNumeric_ffi (.intOp operation) args state next value found]
      exact List.prefix_refl _
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      rw [applyNumeric_ffi (.wordOp operation) args state next value found]
      exact List.prefix_refl _
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals try (solve | rcases run with ⟨_, rfl⟩; exact List.prefix_refl _)
    all_goals rcases run with ⟨_, rfl⟩
    all_goals apply callFFIHOL_return_ioEvents_prefix <;> assumption
  | label =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
  | install =>
    simp only [doApp] at run
    unfold doInstall at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop

end Flapjack.Compiler.Backend.BvlProps
