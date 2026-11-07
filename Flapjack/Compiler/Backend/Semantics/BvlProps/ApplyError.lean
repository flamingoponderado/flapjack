import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
import Flapjack.HolRef
import Aesop

/-! Error cases for BVL primitive application. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace ErrorCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ErrorCarrier

private theorem installError {C F R : Type} (args : List BvlSem.Value)
    (state : BvlSem.State C F) (error : ErrorResult R)
    (run : doInstall args state = .err error) : error = .abort .typeError := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Primitive errors are type errors or final external-call outcomes. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_err"
  (fmap_as_finite_support := [refs])]
theorem doAppError {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (error : ErrorResult BvlSem.Value)
    (run : doApp op args state = .err error) :
    error = .abort .typeError ∨ ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  cases op with
  | install => exact Or.inl (installError args state error run)
  | globOp operation =>
    cases h : applyGlobal operation args state <;> simp_all [doApp]
  | blockOp operation =>
    cases h : applyBlock operation args state <;> simp_all [doApp]
  | memOp operation =>
    cases h : applyMemory operation args state <;> simp_all [doApp]
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state <;> simp_all [doApp]
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state <;> simp_all [doApp]
  | ffi name =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all

end Flapjack.Compiler.Backend.BvlProps
