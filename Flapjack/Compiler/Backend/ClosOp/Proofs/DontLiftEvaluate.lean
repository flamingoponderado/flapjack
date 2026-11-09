import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftCorrect
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

/-! Original constant evaluation lemmas for closure lifting. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace DontLiftPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DontLiftPort

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem intEval {C F : Type} (t : BackendCommon.Tra) (i : Int)
    (env : List Value) (s : State C F) :
    evaluate [.op t (.intOp (.const i)) []] env s = (.val [.number i],s) := by
  rw [evaluate_ordinaryOp_eq t _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyNumeric, doIntApp]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem blockEval {C F : Type} (t : BackendCommon.Tra) (tag : Nat)
    (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp (.cons tag)) []] env s = (.val [.block tag []],s) := by
  rw [evaluate_ordinaryOp_eq t _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem constEval {C F : Type} (t : BackendCommon.Tra) (c : Const)
    (env : List Value) (s : State C F) :
    evaluate [.op t (.blockOp (.constant c)) []] env s = (.val [makeConst c],s) := by
  rw [evaluate_ordinaryOp_eq t _ [] env s (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock]

/-- A non-lifted expression returns one value without changing state. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "dont_lift_Rval"
  (fmap_as_finite_support := [refs, code])]
theorem dontRval {C F : Type} (x : ClosLang.Exp) (env : List Value) (s1 s2 : State C F)
    (res : Result (List Value) Value)
    (h : dontLift x = true ∧ evaluate [x] env s1 = (res,s2)) :
    ∃ v, res = .val [v] ∧ s2 = s1 := by
  rcases (dontLiftCharacterization x).mp h.1 with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩
  · rw [intEval] at h; exact ⟨_,(Prod.mk.inj h.2).1.symm,(Prod.mk.inj h.2).2.symm⟩
  · rw [blockEval] at h; exact ⟨_,(Prod.mk.inj h.2).1.symm,(Prod.mk.inj h.2).2.symm⟩
  · rw [constEval] at h; exact ⟨_,(Prod.mk.inj h.2).1.symm,(Prod.mk.inj h.2).2.symm⟩
  · rw [constEval] at h; exact ⟨_,(Prod.mk.inj h.2).1.symm,(Prod.mk.inj h.2).2.symm⟩
  · rw [constEval] at h; exact ⟨_,(Prod.mk.inj h.2).1.symm,(Prod.mk.inj h.2).2.symm⟩

/-- A non-lifted expression evaluates to the same value in any environment and state. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "evaluate_dont_lift"
  (fmap_as_finite_support := [refs, code])]
theorem evalDont {C F : Type} (x : ClosLang.Exp) (env env1 : List Value)
    (s1 s2 s : State C F) (v : Value)
    (h : evaluate [x] env s1 = (.val [v],s2) ∧ dontLift x = true) :
    evaluate [x] env1 s = (.val [v],s) := by
  rcases (dontLiftCharacterization x).mp h.2 with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s0,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩
  · simp_all [intEval]
  · simp_all [blockEval]
  · simp_all [constEval]
  · simp_all [constEval]
  · simp_all [constEval]
end Flapjack.Compiler.Backend.ClosOp
