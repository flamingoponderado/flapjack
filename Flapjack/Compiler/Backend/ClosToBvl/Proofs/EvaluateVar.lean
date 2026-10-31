import Flapjack.Compiler.Backend.ClosToBvl.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.BvlSem.Evaluate

/-! The variable evaluation case of closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- A lookup in the related source environment has a related target value at
the same index. This helper is Flapjack infrastructure for the variable case. -/
theorem envRel_lookup {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {env : List ClosSem.Value} {targetEnv : List BvlSem.Value} {index : Nat} {value : ClosSem.Value}
    (related : envRel maxApp f refs code env targetEnv) (found : env[index]? = some value) :
    ∃ targetValue, targetEnv[index]? = some targetValue ∧ vRel maxApp f refs code value targetValue := by
  induction env generalizing targetEnv index with
  | nil => simp at found
  | cons head tail ih =>
      cases targetEnv with
      | nil => exact False.elim related
      | cons targetHead targetTail =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst value
              exact ⟨targetHead, rfl, related.1⟩
          | succ index =>
              simp only [List.getElem?_cons_succ] at found ⊢
              exact ih related.2 found

/-- A successfully evaluated source variable has a corresponding BVL
evaluation with the same clock and related value. This is untagged: the
evaluators and candidate state relation still await their HOL carrier review,
and it does not by itself state the complete source simulation theorem. -/
theorem evaluate_var {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s : ClosSem.State C F) (t : BvlSem.State C F)
    (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (trace : BackendCommon.Tra) (index : Nat) (aux : List (Nat × Nat × Bvl.Exp))
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (sNext : ClosSem.State C F)
    (run : ClosSem.evaluate [.var trace index] env s = (result, sNext))
    (noTypeError : result ≠ .err (.abort .typeError))
    (envRelated : envRel s.maxApp f t.refs t.code env targetEnv)
    (statesRelated : stateRel f s t) :
    ∃ value targetValue,
      result = .val [value] ∧ sNext = s ∧
      compileExpsHOL s.maxApp [.var trace index] aux = ([.var index], aux) ∧
      BvlSem.evaluate [.var index] targetEnv { t with clock := s.clock } =
        (.val [targetValue], { t with clock := s.clock }) ∧
      vRel s.maxApp f t.refs t.code value targetValue ∧
      stateRel f sNext { t with clock := s.clock } := by
  cases found : env[index]? with
  | none =>
      simp [ClosSem.evaluate, found] at run
      exact False.elim (noTypeError run.1.symm)
  | some value =>
      simp [ClosSem.evaluate, found] at run
      obtain ⟨targetValue, targetFound, valueRelated⟩ := envRel_lookup envRelated found
      refine ⟨value, targetValue, run.1.symm, run.2.symm, ?_, ?_, valueRelated, ?_⟩
      · simp [compileExpsHOL, compileExpsSingletonHOL]
      · simp [BvlSem.evaluate, targetFound]
      · rw [← run.2]
        exact (stateRel_clock f s t s.clock).1.mpr statesRelated

end Flapjack.Compiler.Backend.ClosToBvl
