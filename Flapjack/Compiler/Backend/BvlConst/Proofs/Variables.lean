import Flapjack.Compiler.Backend.BvlConst.Proofs.SmartOpCorrect
import Flapjack.Compiler.Backend.BvlConst.Proofs.Relations
import Flapjack.Compiler.Backend.BvlConst.Proofs.CompileProduction
/-! Variable and force cases of constant-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Variable case of constant-propagation simulation. The source relation has
an evaluator quantified over finite-map states, so this remains untagged until
that nested representation has an approved qualifier. -/
theorem evaluate_compile_var {C F : Type} (index : Nat) (annotations : List (Option Bvl.Exp))
    (source target : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.var index], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.var index)], target, state) = (result, final) := by
  cases hv : source[index]? with
  | none =>
    simp [evaluateTuple, evaluate, hv] at run
    exact False.elim (notTypeError run.1.symm)
  | some value =>
    have hb : index < source.length := List.getElem?_eq_some_iff.mp hv |>.1
    have hsrc : @Flapjack.holEl Value ⟨unitValue⟩ index source = value := by
      rw [Flapjack.holEl_eq_getElem index source hb]
      exact (List.getElem?_eq_some_iff.mp hv).2
    have htgt : index < target.length := by
      have := envRel_length C F annotations source target related
      omega
    have finish : result = .val [value] ∧ final = state := by
      simpa [evaluateTuple, evaluate, hv, eq_comm] using run.symm
    rcases finish with ⟨rfl, rfl⟩
    cases ha : annotations[index]? with
    | none =>
      have eq := envRel_lookup_none C F annotations source target index related (Or.inl ha)
      have hs : @Flapjack.holEl Value ⟨unitValue⟩ index target = value := eq.trans hsrc
      have get : target[index]? = some value := by
        rw [Flapjack.holEl_eq_getElem index target htgt] at hs
        exact List.getElem?_eq_some_iff.mpr ⟨htgt, hs⟩
      simp [compileSing, ha, evaluateTuple, evaluate, get]
    | some ann =>
      cases ann with
      | none =>
        have eq := envRel_lookup_none C F annotations source target index related (Or.inr ha)
        have hs : @Flapjack.holEl Value ⟨unitValue⟩ index target = value := eq.trans hsrc
        have get : target[index]? = some value := by
          rw [Flapjack.holEl_eq_getElem index target htgt] at hs
          exact List.getElem?_eq_some_iff.mpr ⟨htgt, hs⟩
        simp [compileSing, ha, evaluateTuple, evaluate, get]
      | some expression =>
        have rel := envRel_lookup_some C F annotations source target expression index related ha
        rw [hsrc] at rel
        cases expression with
        | var offset =>
          have lookup : target[index + offset]? = some value := by
            simpa [valueRel, List.getElem?_drop] using rel
          simp [compileSing, ha, evaluateTuple, evaluate, lookup]
        | op op args =>
          simp only [valueRel] at rel
          simp only [compileSing, ha]
          exact rel.2 final target
        | _ => simp [valueRel] at rel

/-- Force case of constant-propagation simulation. Untagged for the same
nested finite-map representation gap as the environment relation. -/
theorem evaluate_compile_force {C F : Type} (location index : Nat) (annotations : List (Option Bvl.Exp))
    (source target : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.force location index], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.force location index)], target, state) = (result, final) := by
  cases hv : source[index]? with
  | none =>
    simp [evaluateTuple, evaluate, hv] at run
    exact False.elim (notTypeError run.1.symm)
  | some value =>
    have hb : index < source.length := List.getElem?_eq_some_iff.mp hv |>.1
    have hsrc : @Flapjack.holEl Value ⟨unitValue⟩ index source = value := by
      rw [Flapjack.holEl_eq_getElem index source hb]
      exact (List.getElem?_eq_some_iff.mp hv).2
    have htgt : index < target.length := by
      have := envRel_length C F annotations source target related
      omega
    have target_get (same : @Flapjack.holEl Value ⟨unitValue⟩ index target = value) :
        target[index]? = some value := by
      rw [Flapjack.holEl_eq_getElem index target htgt] at same
      exact List.getElem?_eq_some_iff.mpr ⟨htgt, same⟩
    cases ha : annotations[index]? with
    | none =>
      have eq := envRel_lookup_none C F annotations source target index related (Or.inl ha)
      have get := target_get (eq.trans hsrc)
      simpa [compileSing, ha, evaluateTuple, evaluate, hv, get] using run
    | some ann =>
      cases ann with
      | none =>
        have eq := envRel_lookup_none C F annotations source target index related (Or.inr ha)
        have get := target_get (eq.trans hsrc)
        simpa [compileSing, ha, evaluateTuple, evaluate, hv, get] using run
      | some expression =>
        have rel := envRel_lookup_some C F annotations source target expression index related ha
        rw [hsrc] at rel
        cases expression with
        | var offset =>
          have get : target[index + offset]? = some value := by
            simpa [valueRel, List.getElem?_drop] using rel
          simpa [compileSing, ha, evaluateTuple, evaluate, hv, get] using run
        | op op args =>
          have same : value = @Flapjack.holEl Value ⟨unitValue⟩ index target := (by simpa [valueRel] using rel.1)
          have get := target_get same.symm
          simpa [compileSing, ha, evaluateTuple, evaluate, hv, get] using run
        | _ => simp [valueRel] at rel


/-- The executed bounded traversal agrees with the variable simulation for
any fuel, including its retry path. This is Flapjack infrastructure. -/
theorem evaluate_compileBounded_var {C F : Type} (fuel index : Nat)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.var index], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel annotations (.var index) = some output ∧
      evaluateTuple ([output], target, state) = (result, final) := by
  exact ⟨compileSing annotations (.var index), compileBounded_eq fuel annotations _,
    evaluate_compile_var index annotations source target state final result run related notTypeError⟩

/-- The executed bounded traversal agrees with the force simulation for any
fuel. This is Flapjack infrastructure for the production path. -/
theorem evaluate_compileBounded_force {C F : Type} (fuel location index : Nat)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.force location index], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel annotations (.force location index) = some output ∧
      evaluateTuple ([output], target, state) = (result, final) := by
  exact ⟨compileSing annotations (.force location index), compileBounded_eq fuel annotations _,
    evaluate_compile_force location index annotations source target state final result run related notTypeError⟩

end Flapjack.Compiler.Backend.BvlConst.Proofs
