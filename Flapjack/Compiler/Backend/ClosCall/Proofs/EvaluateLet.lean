module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateList

@[expose] public section

/-! Environment management for let-bound expression lists. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

theorem freeVars_of_mem (x : Nat) (e : ClosLang.Exp) (es : List ClosLang.Exp)
    (member : e ∈ es) (free : ClosProps.freeVarExp x e) : ClosProps.freeVars x es := by
  induction es with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [ClosProps.freeVars]
    rcases member with rfl | member
    · exact Or.inl free
    · exact Or.inr (ih member)

/-- Each binding expression only uses variables used by the whole let. -/
theorem envRelFuel_let_bindings {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .let trace bindings body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 (bindings.map (0, ·)) := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x ⟨item, member, free⟩
  obtain ⟨expr, exprMember, rfl⟩ := List.mem_map.mp member
  apply h x
  refine ⟨(0, .let trace bindings body), by simp, ?_⟩
  simp only [Nat.zero_add, ClosProps.freeVar, ClosProps.freeVars,
    ClosProps.freeVarExp, or_false] at free ⊢
  exact Or.inl (freeVars_of_mem x expr bindings exprMember free)

/-- The let body uses the outer environment at an offset equal to the number
of bindings. -/
theorem envRelFuel_let_body_outer {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .let trace bindings body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv bindings.length [(0, body)] := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x used
  apply h x
  simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
  simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
  exact Or.inr (by simpa [Nat.add_comm] using used)

/-- Prepending one related value decreases the environment offset by one. -/
theorem envRelFuel_prepend_one {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    {sourceValue targetValue : ClosSem.Value} {offset : Nat} {fns : List (Nat × ClosLang.Exp)}
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv (offset + 1) fns)
    (payload : ValueRelFuel fuel g allowed code sourceValue targetValue) :
    EnvRelFuel fuel g allowed code (sourceValue :: sourceEnv) (targetValue :: targetEnv) offset fns := by
  cases related with
  | equalLength same values =>
    exact .equalLength (by simpa using same) (.cons payload values)
  | unequalLength different left right values =>
    have shift : ∀ n, (∃ fn ∈ fns, ClosProps.freeVar (fn.1 + offset + (n + 1)) fn.2) →
        ∃ fn ∈ fns, ClosProps.freeVar (fn.1 + (offset + 1) + n) fn.2 := by
      intro n ⟨fn, member, free⟩
      exact ⟨fn, member, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using free⟩
    apply EnvRelFuel.unequalLength (by simpa using different)
    · intro x used
      cases x with
      | zero => simp
      | succ n => simpa using left n (shift n used)
    · intro x used
      cases x with
      | zero => simp
      | succ n => simpa using right n (shift n used)
    · intro x used sourceIndex targetIndex
      cases x with
      | zero => simpa using payload
      | succ n =>
        have src : n < sourceEnv.length := by simpa using sourceIndex
        have dst : n < targetEnv.length := by simpa using targetIndex
        simpa using values n (shift n used) src dst

/-- A related prefix of bindings moves the body offset across that prefix. -/
theorem envRelFuel_prepend {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    {sourceValues targetValues : List ClosSem.Value} {offset : Nat} {fns : List (Nat × ClosLang.Exp)}
    (values : List.Forall₂ (ValueRelFuel fuel g allowed code) sourceValues targetValues)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv (offset + sourceValues.length) fns) :
    EnvRelFuel fuel g allowed code (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) offset fns := by
  induction values generalizing offset with
  | nil => simpa using related
  | @cons sourceValue targetValue sourceTail targetTail head tail ih =>
    have tailEnv : EnvRelFuel fuel g allowed code (sourceTail ++ sourceEnv) (targetTail ++ targetEnv)
        (offset + 1) fns := by
      apply ih
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using related
    simpa using envRelFuel_prepend_one tailEnv head

/-- A let expression simulates when its binding list and body simulate. -/
theorem exprSimFuel_let {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBindings targetBindings : List ClosLang.Exp)
    (sourceBody targetBody : ClosLang.Exp) (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ExprsSimFuel (C := C) (F := F) fuel g allowed sourceBindings targetBindings)
    (bodyIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuel (C := C) (F := F) fuel g allowed
      (.let trace sourceBindings sourceBody) (.let trace targetBindings targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody envs
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    have bindingNotType : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetBindingResult, targetBindingFinal, targetBindingRun, bindingRel, bindingStates, bindingGrowth⟩ :=
      bindingsIH sourceEnv targetEnv source target bindingResult bindingFinal bindingRun bindingNotType bindingsEnv states
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextStates : StateRelFuel fuel g allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextGrowth : ∀ key item, target.code.lookup key = some item →
        targetNext.code.lookup key = some item := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetNext, ?_, bindingRel, nextStates, nextGrowth⟩
        simp [evaluate, targetBindingRun, fixClock, targetNext]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valueRel : List.Forall₂ (ValueRelFuel fuel g allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv target
            targetBindingFinal targetValues targetBindingRun
          exact valueRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody envs
        have outerEnv' := envRelFuel_mono outerEnv (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel fuel g allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valueRel
          simpa [valuesLength] using outerEnv'
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
          bodyIH _ _ sourceNext targetNext sourceResult sourceFinal bodyRun notType bodyEnv nextStates
        refine ⟨result, final, ?_, results, finalStates, ?_⟩
        · simpa [evaluate, targetBindingRun, fixClock, targetNext] using targetRun
        · intro key item lookup
          exact growth key item (nextGrowth key item lookup)

end Flapjack.Compiler.Backend.ClosCall
