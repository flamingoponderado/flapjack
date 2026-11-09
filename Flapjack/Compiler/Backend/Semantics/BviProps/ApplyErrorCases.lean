import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyError

/-! Classification of BVI primitive errors. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Flapjack infrastructure: installation errors are type errors. -/
theorem doInstall_error {C F : Type} (args : List Value) (state : BviState C F)
    (error : ErrorResult ExnOrRet) (run : doInstall args state = .err error) : error = .abort .typeError := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all

/-- Flapjack infrastructure: classify errors from the BVI fallback. -/
theorem doAppFallback_error {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (error : ErrorResult ExnOrRet)
    (run : doAppFallback op args state = .err error) :
    error = .abort .typeError ∨ ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  unfold doAppFallback at run
  cases aux : doAppAux op args state with
  | none => simp [aux] at run; exact Or.inl run.symm
  | some inner =>
    cases inner with
    | some pair => simp [aux] at run
    | none =>
      simp only [aux] at run
      cases fallback : BvlSem.doApp op args (toBvl state) with
      | val pair => cases pair; simp [fallback] at run
      | err failure =>
        have classified := BvlProps.doAppError op args (toBvl state) failure fallback
        rcases classified with isType | ⟨name, outcome, isFfi, isError⟩
        · subst failure
          simp [fallback] at run
          exact Or.inl run.symm
        · subst failure
          simp [fallback] at run
          exact Or.inr ⟨name, outcome, isFfi, run.symm⟩

/-- Flapjack infrastructure: BVI primitives report type errors or final FFI
errors. This remains untagged pending source review of the dispatcher. -/
theorem doApp_error {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (error : ErrorResult ExnOrRet)
    (run : doApp op args state = .err error) :
    error = .abort .typeError ∨ ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  cases op with
  | install => exact Or.inl (doInstall_error args state error run)
  | _ => exact doAppFallback_error _ args state error run

end Flapjack.Compiler.Backend.BviProps
