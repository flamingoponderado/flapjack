module

public import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyCode

@[expose] public section

/-! Transfer fallback primitives while retaining the target globals. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

/-- Preserve the target compiler and code while taking the runtime fields
from the source, retaining target globals. This Flapjack helper has no standalone
HOL declaration; BVI discards BVL globals on the fallback path. -/
def fallbackFrame {C D F G : Type} (source : State C F) (target : State D G) : State D F :=
  ⟨target.globals, source.refs, source.clock, target.compile, target.compileOracle, target.code, source.ffi⟩

private def frameOption {C D F G : Type} (target : State D G)
    (result : Option (BvlSem.Value × State C F)) : Option (BvlSem.Value × State D F) :=
  result.map fun (value, next) => (value, fallbackFrame next target)

private theorem applyBlock_frame {C D F G : Type} (op : ClosLang.BlockOp) (args : List BvlSem.Value)
    (source : State C F) (target : State D G) :
    applyBlock op args (fallbackFrame source target) = frameOption target (applyBlock op args source) := by
  unfold applyBlock frameOption fallbackFrame
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]

private theorem applyNumeric_frame {C D F G : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (source : State C F) (target : State D G) :
    applyNumeric op args (fallbackFrame source target) = frameOption target (applyNumeric op args source) := by
  cases op <;> simp [applyNumeric, frameOption, fallbackFrame, Option.map_map, Function.comp_def]

private theorem applyMemory_frame {C D F G : Type} (op : ClosLang.MemOp) (args : List BvlSem.Value)
    (source : State C F) (target : State D G) :
    applyMemory op args (fallbackFrame source target) = frameOption target (applyMemory op args source) := by
  unfold applyMemory frameOption fallbackFrame
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind, Function.comp_def]))

/-- Successful non-global, non-install application transfers across states with arbitrary
compiler and FFI carrier types when the code domain grows. This Flapjack-specific
variant of HOL's `do_app_Rval_swap` excludes globals because the BVI fallback
discards BVL globals, so the original lemma cannot be used directly. -/
theorem doAppFallbackRvalSwap {C D F G : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (source next : Flapjack.Compiler.Backend.BvlSem.State C F) (value : BvlSem.Value)
    (target : Flapjack.Compiler.Backend.BvlSem.State D G)
    (notGlobal : ∀ operation, op ≠ .globOp operation)
    (h : doApp op args source = .val (value, next) ∧ op ≠ .install ∧
      (∀ key, sptDomain source.code key → sptDomain target.code key)) :
    doApp op args (fallbackFrame source target) = .val (value, fallbackFrame next target) := by
  rcases h with ⟨run, notInstall, domain⟩
  cases op with
  | globOp operation => exact (notGlobal operation rfl).elim
  | blockOp operation =>
    cases found : applyBlock operation args source with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyBlock_frame, found, frameOption]
  | memOp operation =>
    cases found : applyMemory operation args source with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyMemory_frame, found, frameOption]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args source with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyNumeric_frame, found, frameOption]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args source with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyNumeric_frame, found, frameOption]
  | label index =>
    cases args with
    | cons a rest => simp [doApp] at run
    | nil =>
      cases found : sptLookup index source.code with
      | none => simp [doApp, found] at run
      | some entry =>
        have present : sptDomain target.code index := domain index (by simp [sptDomain, found])
        cases newFound : sptLookup index target.code with
        | none => simp [sptDomain, newFound] at present
        | some replacement =>
          simp [doApp, found] at run
          rcases run with ⟨rfl, rfl⟩
          simp [doApp, fallbackFrame, newFound]
  | install => exact (notInstall rfl).elim
  | ffi | thunkOp =>
    simp only [doApp] at run ⊢
    repeat' split at run
    all_goals simp_all [fallbackFrame]
    all_goals aesop

/-- A non-global, non-install error transfers across independently typed compiler and FFI
carriers when the target code domain is contained in the source domain. This
Flapjack-specific variant of HOL's `do_app_Rerr_swap` excludes globals because
the BVI fallback discards BVL globals, so the original lemma cannot be used directly. -/
theorem doAppFallbackRerrSwap {C D F G : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (source : Flapjack.Compiler.Backend.BvlSem.State C F) (error : ErrorResult BvlSem.Value)
    (target : Flapjack.Compiler.Backend.BvlSem.State D G)
    (notGlobal : ∀ operation, op ≠ .globOp operation)
    (h : doApp op args source = .err error ∧ op ≠ .install ∧
      ((∀ key, sptDomain target.code key → sptDomain source.code key) ∨
        error ≠ .abort .typeError)) :
    doApp op args (fallbackFrame source target) = .err error := by
  rcases h with ⟨run, notInstall, domain⟩
  cases op with
  | globOp operation => exact (notGlobal operation rfl).elim
  | blockOp operation =>
    cases found : applyBlock operation args source <;>
      simp_all [doApp, applyBlock_frame, frameOption]
  | memOp operation =>
    cases found : applyMemory operation args source <;>
      simp_all [doApp, applyMemory_frame, frameOption]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args source <;>
      simp_all [doApp, applyNumeric_frame, frameOption]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args source <;>
      simp_all [doApp, applyNumeric_frame, frameOption]
  | label index =>
    cases args with
    | cons a rest => simp_all [doApp]
    | nil =>
      cases found : sptLookup index source.code with
      | some entry => simp [doApp, found] at run
      | none =>
        simp [doApp, found] at run
        subst error
        cases newFound : sptLookup index target.code with
        | none => simp [doApp, fallbackFrame, newFound]
        | some entry =>
          have domain' := domain.resolve_right (by simp)
          have present := domain' index (by simp [sptDomain, newFound])
          simp [sptDomain, found] at present
  | install => exact (notInstall rfl).elim
  | ffi | thunkOp =>
    simp only [doApp] at run ⊢
    repeat' split at run
    all_goals simp_all [fallbackFrame]

end Flapjack.Compiler.Backend.BvlProps
