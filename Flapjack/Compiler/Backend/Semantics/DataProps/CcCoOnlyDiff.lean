module

public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields

@[expose] public section

/-! Agreement of two data-language states up to their compiler configuration. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Two states agree on every field except the compiler callback and the
compile oracle, so they may have different compiler types. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cc_co_only_diff_def"]
def ccCoOnlyDiff {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) : Prop :=
  s.locals = t.locals ∧
  s.localsSize = t.localsSize ∧
  s.stack = t.stack ∧
  s.stackMax = t.stackMax ∧
  s.stackFrameSizes = t.stackFrameSizes ∧
  s.global = t.global ∧
  s.handler = t.handler ∧
  s.refs = t.refs ∧
  s.clock = t.clock ∧
  s.code = t.code ∧
  s.ffi = t.ffi ∧
  s.space = t.space ∧
  s.tstamps = t.tstamps ∧
  s.limits = t.limits ∧
  s.safeForSpace = t.safeForSpace ∧
  s.peakHeapLength = t.peakHeapLength

/-- Popping a saved frame keeps the two states in agreement. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "pop_env_cc_co_only_diff"]
theorem popEnv_ccCoOnlyDiff {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (s1 : State C1 F)
    (premises : ccCoOnlyDiff s t ∧ popEnv s = some s1) :
    ∃ t1, popEnv t = some t1 ∧ ccCoOnlyDiff s1 t1 := by
  obtain ⟨diff, pop⟩ := premises
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handler, refs, clock, code,
    ffi, space, tstamps, limits, safe, peak⟩ := diff
  cases shape : s.stack with
  | nil =>
    simp [popEnv, shape] at pop
  | cons frame rest =>
    cases frame with
    | env size env =>
      simp [popEnv, shape] at pop
      obtain rfl := pop
      refine ⟨{ t with locals := env, stack := rest, localsSize := size }, ?_, ?_⟩
      · simp [popEnv, ← stack, shape]
      · simp_all [ccCoOnlyDiff]
    | exc size env handler' =>
      simp [popEnv, shape] at pop
      obtain rfl := pop
      refine ⟨{ t with locals := env, stack := rest, localsSize := size, handler := handler' }, ?_, ?_⟩
      · simp [popEnv, ← stack, shape]
      · simp_all [ccCoOnlyDiff]

/-- Calling through a pushed environment keeps the two states in agreement. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cc_co_only_diff_call_env"]
theorem callEnv_ccCoOnlyDiff {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (args1 : List Value) (ss : Option Nat) (env : Spt Value) (b : Bool)
    (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (callEnv args1 ss (pushEnv env b (decClock s)))
      (callEnv args1 ss (pushEnv env b (decClock t))) := by
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handler, refs, clock, code,
    ffi, space, tstamps, limits, safe, peak⟩ := diff
  cases b <;>
    simp [ccCoOnlyDiff, callEnv, pushEnv, decClock, locals, localsSize, stack, stackMax,
      frameSizes, global, handler, refs, clock, code, ffi, space, tstamps, limits, safe, peak]

/-- The narrow cut keeps the two states in agreement. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_cc_co"]
theorem cutStateOpt_ccCoOnlyDiff {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : Option NumSet) (s1 : State C1 F)
    (premises : ccCoOnlyDiff s t ∧ cutStateOpt names s = some s1) :
    ∃ t1, cutStateOpt names t = some t1 ∧ ccCoOnlyDiff s1 t1 := by
  obtain ⟨diff, cut⟩ := premises
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handler, refs, clock, code,
    ffi, space, tstamps, limits, safe, peak⟩ := diff
  cases names with
  | none =>
    simp only [cutStateOpt] at cut
    simp only [Option.some.injEq] at cut
    obtain rfl := cut
    exact ⟨t, by simp [cutStateOpt],
      ⟨locals, localsSize, stack, stackMax, frameSizes, global, handler, refs, clock, code, ffi,
        space, tstamps, limits, safe, peak⟩⟩
  | some names =>
    simp only [cutStateOpt, cutState] at cut ⊢
    rw [← locals] at ⊢
    cases found : cutEnv names s.locals with
    | none => simp [found] at cut
    | some env =>
      simp [found] at cut
      obtain rfl := cut
      refine ⟨{ t with locals := env }, ?_, ?_⟩
      · simp
      · simp_all [ccCoOnlyDiff]

end Flapjack.Compiler.Backend.DataProps
