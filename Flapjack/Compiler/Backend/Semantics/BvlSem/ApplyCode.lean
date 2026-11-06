import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyClock
import Flapjack.HolRef

/-! Code and compiler state preservation for BVL primitive application. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

namespace FrameCarrier
/-- Canonical finite-map state representation roundtrip for the frame theorem. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end FrameCarrier

/-- Global primitives preserve code, compiler, and oracle. -/
theorem applyGlobal_code {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyGlobal op args state = some (value, next)) :
    next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Block primitives preserve code, compiler, and oracle. -/
theorem applyBlock_code {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyBlock op args state = some (value, next)) :
    next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Integer and word primitives preserve code, compiler, and oracle. -/
theorem applyNumeric_code {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : applyNumeric op args state = some (value, next)) :
    next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Memory primitives preserve code, compiler, and oracle. -/
theorem applyMemory_code {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value) (run : applyMemory op args state = some (value, next)) :
    next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- A successful installation unions in the current oracle program, advances
the oracle once, and leaves the compiler callback unchanged. -/
theorem doInstall_code {C F R : Type} (args : List Value)
    (state next : State C F) (value : Value) (run : doInstall (R := R) args state = .val (value, next)) :
    next.code = sptUnion state.code (sptFromAList (state.compileOracle 0).2) ∧
    next.compile = state.compile ∧
    next.compileOracle = (fun n => state.compileOracle (n + 1)) := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop


/-- A non-install primitive leaves code, compiler, and oracle unchanged.
This is a proof-side invariant pending dispatcher correspondence review. -/
theorem doApp_code {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (notInstall : op ≠ .install) (run : doApp op args state = .val (value, next)) :
    next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_code operation args state next value h
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_code operation args state next value h
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_code operation args state next value h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_code (.intOp operation) args state next value h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_code (.wordOp operation) args state next value h
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
  | install => exact (notInstall rfl).elim

/-- The dispatcher preserves its compiler callback on every successful path. -/
theorem doApp_compile {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : doApp op args state = .val (value, next)) :
    next.compile = state.compile := by
  by_cases install : op = .install
  · subst op
    exact (doInstall_code args state next value run).2.1
  · exact (doApp_code op args state next value install run).2.1

/-- Successful primitive application preserves every existing code entry,
including when installation adds new code. -/
theorem doApp_lookup_code {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value) (run : doApp op args state = .val (value, next))
    (key : Nat) (entry : Nat × Bvl.Exp) (found : sptLookup key state.code = some entry) :
    sptLookup key next.code = some entry := by
  by_cases install : op = .install
  · subst op
    rw [(doInstall_code args state next value run).1, sptLookup_sptUnion, found]
  · rw [(doApp_code op args state next value install run).1, found]

/-- Successful primitive application preserves the clock, and all
non-installation operations preserve code and compiler callbacks. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_app_const"
  (fmap_as_finite_support := [refs])]
theorem doApp_state_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    next.clock = state.clock ∧ (op ≠ .install →
      next.code = state.code ∧ next.compile = state.compile ∧ next.compileOracle = state.compileOracle) :=
  ⟨doApp_clock op args state next value run, fun h => doApp_code op args state next value h run⟩


end Flapjack.Compiler.Backend.BvlSem
