module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.Induction
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Initial-state consequences of the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CompileSemantics
open BviTmc BviSem BvlSem BackendProps SemanticPrimitivesProps ResultRelation

namespace CompileWitness
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end CompileWitness

theorem holFmapAsFiniteSupportExistentialWitness_evaluate_compile_each_assembled_f
    (f : HolFiniteMapExact Nat Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup = f.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- Evaluation of the initial call is preserved by TMC compilation under the
original program and oracle conditions. Evaluation inherits the rational-cuts
real model documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_compile_each"
  (fmap_as_finite_support_relation := [BviState.refs])
  (fmap_as_finite_support_existentials := [f])]
theorem evaluate_compile_each_assembled {C F : Type} (next start clock : Nat)
    (program : List (Nat × Nat × Bvi.Exp)) (ffi : HolFfiState F)
    (oracle : BviSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (result : BviResult) (final : BviState (Nat × C) F)
    (h : inputCondition next program ∧
      (∀ n next cfg prog, oracle n = ((next, cfg), prog) → inputCondition next prog) ∧
      (∀ n, n ∈ ((compileEachSource next program).2.map Prod.fst) ∧
        inWorkerNamespace n → n < (oracle 0).1.1) ∧
      evaluate [.call 0 (some start) [] none] []
        (initialState ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) clock) = (result, final) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ (f : HolFiniteMapExact Nat Nat) (targetFinal : BviState C F) (targetResult : BviResult),
      evaluate [.call 0 (some start) [] none] []
        (initialState ffi (sptFromAList (compileEachSource next program).2)
          (stateCo compileEachSource oracle) compiler clock) = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (valueRel f)) (eorRel f) result targetResult ∧
      stateRel f final targetFinal := by
  obtain ⟨condition, oracleConditions, workerBound, run, notTypeError⟩ := h
  have oracleConditions' : ∀ n, inputCondition (oracle n).1.1 (oracle n).2 := by
    intro n
    exact oracleConditions n (oracle n).1.1 (oracle n).1.2 (oracle n).2 (by cases oracle n; rfl)
  have workerBound' : ∀ n, n ∈ ((compileEachSource next program).2.map Prod.fst) →
      inWorkerNamespace n → n < (oracle 0).1.1 := fun n member worker => workerBound n ⟨member, worker⟩
  have states : stateRel HolFiniteMapExact.empty
      (initialState ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) clock)
      (initialState ffi (sptFromAList (compileEachSource next program).2)
        (stateCo compileEachSource oracle) compiler clock) := by
    have compiled : compileEachSource next program =
        ((compileEachSource next program).1, (compileEachSource next program).2) := by rfl
    have codes := compileEachSource_codeRel next _ program _ compiled condition.2.2.1 condition.1 condition.2.1
    have names := compileEachSource_namespaceRel next _ program _ compiled condition.2.2.2.2.2
      condition.2.2.2.2.1 condition.2.2.2.1
    refine ⟨?_, rfl, trivial, rfl, rfl, rfl, codes, names, oracleConditions', ?_, ?_⟩
    · constructor
      · ext key
        simp [BviSem.initialState, HolFiniteMapExact.domain, HolFiniteMapExact.empty]
      · intro key value found
        simp [BviSem.initialState, HolFiniteMapExact.empty] at found
    · intro n ⟨member, worker⟩
      exact workerBound' n ((BviTailrec.sptFromAList_mem_iff _ n).mp member) worker
    · intro a b c ⟨found, _⟩
      simp [HolFiniteMapExact.empty] at found
  have env : envRel false HolFiniteMapExact.empty [] [] := by
    refine ⟨[], [], rfl, .nil, ?_⟩
    simp
  have safe : noMutcons (.call 0 (some start) [] none) := by
    rw [noMutcons.eq_def]
    simp
  have post := Induction.evaluate_general start [.call 0 (some start) [] none]
    (initialState ffi (sptFromAList program) oracle (stateCc compileEachSource compiler) clock)
    (initialState ffi (sptFromAList (compileEachSource next program).2) (stateCo compileEachSource oracle) compiler clock)
    [] [] false HolFiniteMapExact.empty result final run notTypeError (by simpa using safe) env states (by simp)
  obtain ⟨targetFinal, f, targetResult, targetRun, related, finalStates, _⟩ := post.1
  exact ⟨f, targetFinal, targetResult, targetRun, related, finalStates⟩

end Flapjack.Compiler.Backend.BviTmc.CompileSemantics
