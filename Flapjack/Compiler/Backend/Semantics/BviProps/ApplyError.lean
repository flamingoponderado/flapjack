import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyError

/-! Error behavior of BVI primitive operations. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- The BVI-specific installation primitive does not produce timeouts. -/
theorem doInstall_not_timeout {C F : Type} (args : List Value) (state : BviState C F) :
    doInstall (R := ExnOrRet) args state ≠ .err (.abort .timeoutError) := by
  intro run
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all

/-- Delegated or BVI-specific primitive application cannot time out. -/
theorem doAppFallback_not_timeout {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) : doAppFallback op args state ≠ .err (.abort .timeoutError) := by
  intro run
  unfold doAppFallback at run
  cases aux : doAppAux op args state with
  | none => simp [aux] at run
  | some inner =>
    cases inner with
    | some pair => simp [aux] at run
    | none =>
      simp only [aux] at run
      cases fallback : BvlSem.doApp op args (toBvl state) with
      | val pair => cases pair; simp [fallback] at run
      | err error =>
        cases error with
        | raise value => simp [fallback] at run
        | abort reason =>
          cases reason with
          | typeError => simp [fallback] at run
          | ffiError event => simp [fallback] at run
          | timeoutError =>
            have impossible := BvlProps.doAppError op args (toBvl state) _ fallback
            simp at impossible

/-- BVI primitive application cannot produce a clock timeout. Untagged
pending review of the dispatcher and its delegated BVL operations. -/
theorem doApp_not_timeout {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) : doApp op args state ≠ .err (.abort .timeoutError) := by
  cases op with
  | install => exact doInstall_not_timeout args state
  | _ => simp only [doApp]; exact doAppFallback_not_timeout _ args state

end Flapjack.Compiler.Backend.BviProps
