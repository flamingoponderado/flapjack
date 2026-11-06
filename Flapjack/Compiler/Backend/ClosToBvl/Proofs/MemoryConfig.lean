import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Garbage-collector configuration operation correspondence. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Successful configuration takes two numbers and returns related unit
values without changing the state. -/
theorem configGC_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .configGC) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp .configGC) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value target := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
        all_goals try contradiction
        case number.number first second =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases related with
          | cons firstRel tail =>
            cases tail with
            | cons secondRel tail =>
              cases tail
              have firstEq := vRel_number_inv firstRel
              have secondEq := vRel_number_inv secondRel
              subst_vars
              exact ⟨BvlSem.unitValue, by simp [BvlSem.doApp, BvlSem.applyMemory], rfl, .block .nil⟩

/-- Invalid configuration arguments report a source type error. -/
theorem configGC_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .configGC) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .configGC args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
