import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateHandle
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Sequential expression-list evaluation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Removing function bodies from the free-variable requirement preserves
the environment relation. -/
theorem envRelFuel_subset {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    {offset : Nat} {fns smaller : List (Nat × ClosLang.Exp)}
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv offset fns)
    (subset : ∀ item ∈ smaller, item ∈ fns) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv offset smaller := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x used
  obtain ⟨item, member, free⟩ := used
  exact h x ⟨item, subset item member, free⟩

/-- Source-driven simulation for expression lists. -/
def ExprsSimFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F),
    evaluate sourceExps sourceEnv source = (sourceResult, sourceFinal) →
    sourceResult ≠ .err (.abort .typeError) →
    EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
    StateRelFuel fuel g allowed source target →
    ∃ targetResult targetFinal,
      evaluate targetExps targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value)

/-- Pointwise expression simulations compose in evaluation order. -/
theorem exprsSimFuel_of_forall₂ {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (distinct : (g.2.map Prod.fst).Nodup)
    (sims : List.Forall₂ (ExprSimFuel (C := C) (F := F) fuel g allowed) sourceExps targetExps) :
    ExprsSimFuel (C := C) (F := F) fuel g allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro sourceEnv targetEnv source target sourceResult sourceFinal run _ _ states
    have sourceEq : sourceResult = .val [] ∧ sourceFinal = source := by
      simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    exact ⟨.val [], target, by simp [evaluate], .nil, states, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headIH tailSims tailIH =>
    intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
    have headEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headNotType : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have : sourceResult = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType this
      obtain ⟨targetHeadResult, targetHeadFinal, targetHeadRun, headRel, headStates, headGrowth⟩ :=
        headIH sourceEnv targetEnv source target headResult headFinal headRun headNotType headEnv states
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := sourceEq
          exact ⟨.err targetError, targetHeadFinal,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv target targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv target targetHeadFinal targetValues targetHeadRun
          have valuesRel : ValueRelFuel fuel g allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv (stateExtends_refl g distinct) Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailNotType : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            obtain ⟨targetTailResult, targetFinal, targetTailRun, tailRel, finalStates, tailGrowth⟩ :=
              tailIH sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal tailRun tailNotType tailEnv' headStates
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv target targetHeadFinal targetValue targetHeadRun
            rw [targetTailRun] at targetOuter
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨.err targetError, targetFinal, targetOuter, tailRel, finalStates,
                  fun key item lookup => tailGrowth key item (headGrowth key item lookup)⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valuesRel (stateExtends_refl g distinct) Set.Subset.rfl tailGrowth
                exact ⟨.val (targetValue :: targetTailValues), targetFinal, targetOuter,
                  .cons grownValue tailRel, finalStates,
                  fun key item lookup => tailGrowth key item (headGrowth key item lookup)⟩

end Flapjack.Compiler.Backend.ClosCall
