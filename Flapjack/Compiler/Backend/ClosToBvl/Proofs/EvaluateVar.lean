module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Evaluate

@[expose] public section

/-! The variable evaluation case of closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

local instance : Nonempty ClosSem.Value := ⟨.number 0⟩

/-- A bounded source index is also bounded in a related target environment,
and the values at that index are related. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "LESS_LENGTH_env_rel_IMP"
  (fmap_as_finite_support_relation := [f, refs])]
theorem envRel_index (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp)) :
    ∀ (env : List ClosSem.Value) (targetEnv : List BvlSem.Value) (n : Nat),
      n < env.length ∧ envRel maxApp f refs code env targetEnv →
      n < targetEnv.length ∧ vRel maxApp f refs code (holEl n env) (holEl n targetEnv) := by
  intro env
  induction env with
  | nil =>
      intro targetEnv n ⟨bound, _⟩
      simp at bound
  | cons head tail ih =>
      intro targetEnv n ⟨bound, related⟩
      cases targetEnv with
      | nil => exact False.elim related
      | cons targetHead targetTail =>
          cases n with
          | zero =>
              simpa [holEl, holHd] using related.1
          | succ n =>
              have bound' : n < tail.length := by simpa using bound
              have result := ih targetTail n ⟨bound', related.2⟩
              simpa [holEl] using result

/-- A lookup in the related source environment has a related target value at
the same index. This helper is Flapjack infrastructure for the variable case. -/
theorem envRel_lookup {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {env : List ClosSem.Value} {targetEnv : List BvlSem.Value} {index : Nat} {value : ClosSem.Value}
    (related : envRel maxApp f refs code env targetEnv) (found : env[index]? = some value) :
    ∃ targetValue, targetEnv[index]? = some targetValue ∧ vRel maxApp f refs code value targetValue := by
  obtain ⟨sourceBound, sourceEq⟩ := List.getElem?_eq_some_iff.mp found
  obtain ⟨targetBound, valuesRelated⟩ := envRel_index maxApp f refs code env targetEnv index
    ⟨sourceBound, related⟩
  refine ⟨holEl index targetEnv, ?_, ?_⟩
  · rw [holEl_eq_getElem index targetEnv targetBound, List.getElem?_eq_getElem targetBound]
  · rw [holEl_eq_getElem index env sourceBound, sourceEq] at valuesRelated
    exact valuesRelated

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
