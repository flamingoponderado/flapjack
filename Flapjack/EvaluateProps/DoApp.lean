import Flapjack.EvaluateProps
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

/-! FFI, test, conversion, and arithmetic cases of the original
primitive-application transition theorem. The other primitive cases and the
assembling theorem remain open. The evaluator and dispatcher are pending source
and carrier review; floating-point operations inherit the rational-cut assumption
in `docs/SOUNDNESS.md`. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Flapjack helper: numeric application does not modify the FFI state. -/
theorem doAppNumericCore_ffi {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (op : AstHOL.Op) (values : List Value)
    (result : Result Value Value)
    (h : doAppNumericCore (store, ffi) op values = some (some ((store', ffi'), result))) :
    ffi' = ffi := by
  cases op <;> simp only [doAppNumericCore] at h <;>
    repeat' first | split at h | simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨_, _, ⟨_, hffi⟩, _⟩ := h; exact hffi.symm

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "do_app_call_FFI_rel"]
theorem doAppArith_callFFIRel {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (action : AstHOL.Arith) (typ : AstHOL.PrimType)
    (values : List Value) (result : Result Value Value)
    (h : doApp (store, ffi) (.arith action typ) values = some ((store', ffi'), result)) :
    Relation.ReflTransGen callFFIRelHOL ffi ffi' := by
  cases typ <;> simp only [doApp, doAppBasic] at h
  case float64T =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, heq⟩ := h
    cases heq
    exact Relation.ReflTransGen.refl
  all_goals
    split at h <;> simp_all
    have heq : ffi' = ffi := by
      apply doAppNumericCore_ffi store store' ffi ffi' (.arith action _) values result
      assumption
    subst ffi'
    exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "do_app_call_FFI_rel"]
theorem doAppFromTo_callFFIRel {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (source target : AstHOL.PrimType)
    (values : List Value) (result : Result Value Value)
    (h : doApp (store, ffi) (.fromTo source target) values = some ((store', ffi'), result)) :
    Relation.ReflTransGen callFFIRelHOL ffi ffi' := by
  simp only [doApp, doAppBasic] at h
  cases hn : doAppNumericCore (store, ffi) (.fromTo source target) values with
  | none => simp [hn] at h
  | some outcome =>
    simp only [hn] at h
    have heq := doAppNumericCore_ffi store store' ffi ffi' (.fromTo source target) values result (by rw [hn]; exact congrArg some h)
    subst ffi'
    exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "do_app_call_FFI_rel"]
theorem doAppTest_callFFIRel {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (test : AstHOL.Test) (typ : AstHOL.PrimType)
    (values : List Value) (result : Result Value Value)
    (h : doApp (store, ffi) (.test test typ) values = some ((store', ffi'), result)) :
    Relation.ReflTransGen callFFIRelHOL ffi ffi' := by
  simp only [doApp] at h
  repeat' first | split at h | simp_all
  all_goals exact Relation.ReflTransGen.refl

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "do_app_call_FFI_rel"]
theorem doAppFfi_callFFIRel {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (name : MlString) (values : List Value)
    (result : Result Value Value)
    (h : doApp (store, ffi) (.ffi name) values = some ((store', ffi'), result)) :
    Relation.ReflTransGen callFFIRelHOL ffi ffi' := by
  simp only [doApp, doAppNumericCore, doAppBasic] at h
  repeat' first | split at h | simp_all
  all_goals try exact Relation.ReflTransGen.refl
  case h_1 =>
    obtain ⟨_, _, heq⟩ := Option.bind_eq_some_iff.mp h
    simp_all
    apply Relation.ReflTransGen.single
    exact ⟨_, _, _, _, by assumption⟩

end Flapjack.EvaluateProps
