import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateIf

/-! Exception handlers for the direct-call simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The protected expression uses only free variables of the whole handler. -/
theorem envRelFuel_handle_body {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .handle trace body handler)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, body)] := by
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
  exact Or.inl used

/-- A related exception payload may be prepended when entering a handler. -/
theorem envRelFuel_handle_enter {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    {sourceValue targetValue : ClosSem.Value} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .handle trace body handler)])
    (payload : ValueRelFuel fuel g allowed code sourceValue targetValue) :
    EnvRelFuel fuel g allowed code (sourceValue :: sourceEnv) (targetValue :: targetEnv)
      0 [(0, handler)] := by
  cases related with
  | equalLength same values =>
    exact .equalLength (by simpa using same) (.cons payload values)
  | unequalLength different left right values =>
    apply EnvRelFuel.unequalLength (by simpa using different)
    · intro x used
      cases x with
      | zero => simp
      | succ n =>
        have original : ∃ fn ∈ [(0, .handle trace body handler)],
            ClosProps.freeVar (fn.1 + 0 + n) fn.2 := by
          simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
          simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
          exact Or.inr (by simpa [Nat.add_comm] using used)
        simpa using left n original
    · intro x used
      cases x with
      | zero => simp
      | succ n =>
        have original : ∃ fn ∈ [(0, .handle trace body handler)],
            ClosProps.freeVar (fn.1 + 0 + n) fn.2 := by
          simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
          simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
          exact Or.inr (by simpa [Nat.add_comm] using used)
        simpa using right n original
    · intro x used sourceIndex targetIndex
      cases x with
      | zero => simpa using payload
      | succ n =>
        have original : ∃ fn ∈ [(0, .handle trace body handler)],
            ClosProps.freeVar (fn.1 + 0 + n) fn.2 := by
          simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
          simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
          exact Or.inr (by simpa [Nat.add_comm] using used)
        have src : n < sourceEnv.length := by simpa using sourceIndex
        have dst : n < targetEnv.length := by simpa using targetIndex
        simpa using values n original src dst

/-- Matching handlers simulate protected evaluation and, on a raised value,
continue with related payloads in their extended environments. -/
theorem exprSimFuel_handle {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sb sh tb th : ClosLang.Exp)
    (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ExprSimFuel (C := C) (F := F) fuel g allowed sb tb)
    (handlerIH : ExprSimFuel (C := C) (F := F) fuel g allowed sh th) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.handle trace sb sh) (.handle trace tb th) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  have bodyEnv := envRelFuel_handle_body trace tb th envs
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetBodyResult, targetBodyFinal, targetBodyRun, bodyRel, bodyStates, bodyGrowth⟩ :=
      bodyIH sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodyNotType bodyEnv states
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextStates : StateRelFuel fuel g allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextGrowth : ∀ key item, target.code.lookup key = some item →
        targetNext.code.lookup key = some item := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have sourceEq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.val targetValues, targetNext, ?_, bodyRel, nextStates, nextGrowth⟩
        simp [evaluate, targetBodyRun, fixClock, targetNext]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have sourceEq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := sourceEq
            refine ⟨.err (.abort targetAbort), targetNext, ?_, bodyRel, nextStates, nextGrowth⟩
            simp [evaluate, targetBodyRun, fixClock, targetNext]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel fuel g allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv : EnvRelFuel fuel g allowed targetNext.code sourceEnv targetEnv 0
                [(0, .handle trace tb th)] :=
              envRelFuel_mono envs (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
              handlerIH _ _ sourceNext targetNext sourceResult sourceFinal handlerRun notType handlerEnv nextStates
            refine ⟨result, final, ?_, results, finalStates, ?_⟩
            · simpa [evaluate, targetBodyRun, fixClock, targetNext] using targetRun
            · intro key item lookup
              exact growth key item (nextGrowth key item lookup)

end Flapjack.Compiler.Backend.ClosCall
