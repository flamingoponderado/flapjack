import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# HOL whole-evaluator clock theorems over the exact finite-map PanSem evaluator

Untagged Flapjack-specific rendering of HOL `panSemScript.sml:755` `evaluate_clock`
and `panSemScript.sml:768` `fix_clock_evaluate` over the exact finite-map evaluator
`evalPanSemRecursiveCallFiniteContext` / `evalPanSemNonrecursiveHOLFinite`.
No `@[hol]` tag until coordinator source/carrier review (bead flapjack-pxn.18.4.3.77.2.8).
-/

namespace Flapjack

open Flapjack.PanSemStateFiniteExact
open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL ShapeHOL)

/-! ## Nonrecursive dispatcher clock bound -/

/-- Exact `Assign` clause keeps the clock. -/
@[simp] theorem assignStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (assignStepHOLExact state kind name source evalExpression).2.clock = state.clock := by
  unfold assignStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `Primitive` clause keeps the clock. -/
@[simp] theorem primitiveStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width))) :
    (primitiveStepHOLExact state name operator arguments evalExpressions).2.clock =
      state.clock := by
  unfold primitiveStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `Store` clause keeps the clock. -/
@[simp] theorem storeStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeStepHOLExact state destination source evalExpression).2.clock = state.clock := by
  unfold storeStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `Store32` clause keeps the clock. -/
@[simp] theorem store32StepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (store32StepHOLExact state address value evalExpression).2.clock = state.clock := by
  unfold store32StepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `StoreByte` clause keeps the clock. -/
@[simp] theorem storeByteStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeByteStepHOLExact state address value evalExpression).2.clock = state.clock := by
  unfold storeByteStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `ExtCall` clause keeps the clock. -/
@[simp] theorem extCallStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.clock =
      state.clock := by
  unfold extCallStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `Raise` clause keeps the clock. -/
@[simp] theorem raiseStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (raiseStepHOLExact state exceptionId expression evalExpression).2.clock = state.clock := by
  unfold raiseStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `Return` clause keeps the clock. -/
@[simp] theorem returnStepHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (returnStepHOLExact state expression evalExpression).2.clock = state.clock := by
  unfold returnStepHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `ShMemLoad` clause keeps the clock. -/
@[simp] theorem shMemLoadClauseHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.clock =
      state.clock := by
  unfold shMemLoadClauseHOLExact shMemLoadHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- Exact `ShMemStore` clause keeps the clock. -/
@[simp] theorem shMemStoreClauseHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.clock =
      state.clock := by
  unfold shMemStoreClauseHOLExact shMemStoreHOLExact
  all_goals (repeat' (first | split))
  all_goals (first | rfl | (cases kind <;> rfl) | omega)

/-- HOL `evaluate_clock` (`panSemScript.sml:755-766`) over the nonrecursive exact
    dispatcher: a successful nonrecursive clause never increases the clock. -/
theorem evalPanSemNonrecursiveHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (result : Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalPanSemNonrecursiveHOLExact program state = some result) :
    result.2.clock ≤ state.clock := by
  cases program <;>
    simp only [evalPanSemNonrecursiveHOLExact] at h
  case «skip» =>
    cases h
    exact Nat.le_refl _
  case «dec» name shape value body =>
    cases h
  case «assign» kind name value =>
    cases h
    rw [assignStepHOLExact_clock]
    exact Nat.le_refl _
  case «primitive» name operator args =>
    cases h
    rw [primitiveStepHOLExact_clock]
    exact Nat.le_refl _
  case «store» address value =>
    cases h
    rw [storeStepHOLExact_clock]
    exact Nat.le_refl _
  case «store32» address value =>
    cases h
    rw [store32StepHOLExact_clock]
    exact Nat.le_refl _
  case «storeByte» address value =>
    cases h
    rw [storeByteStepHOLExact_clock]
    exact Nat.le_refl _
  case «seq» first second =>
    cases h
  case «ite» condition thenBranch elseBranch =>
    cases h
  case «while» condition body =>
    cases h
  case «break» =>
    cases h
    exact Nat.le_refl _
  case «continue» =>
    cases h
    exact Nat.le_refl _
  case «call» info name args =>
    cases h
  case «decCall» name shape function args body =>
    cases h
  case «extCall» function configuration configurationLength array arrayLength =>
    cases h
    rw [extCallStepHOLExact_clock]
    exact Nat.le_refl _
  case «raise» exception value =>
    cases h
    rw [raiseStepHOLExact_clock]
    exact Nat.le_refl _
  case «return» value =>
    cases h
    rw [returnStepHOLExact_clock]
    exact Nat.le_refl _
  case «shMemLoad» size kind name address =>
    cases h
    rw [shMemLoadClauseHOLExact_clock]
    exact Nat.le_refl _
  case «shMemStore» size address value =>
    cases h
    rw [shMemStoreClauseHOLExact_clock]
    exact Nat.le_refl _
  case «tick» =>
    cases h
    exact tickStepHOLExact_clock_le state
  case «annot» tag text =>
    cases h
    exact Nat.le_refl _

/-- HOL `evaluate_clock` over the finite-support nonrecursive dispatcher. -/
theorem evalPanSemNonrecursiveHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (result : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (hres : PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite state program = some result) :
    result.2.clock ≤ state.clock := by
  unfold PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite at hres
  split at hres
  · cases hres
  · rename_i pair hpair
    simp only [Option.some.injEq] at hres
    subst hres
    exact evalPanSemNonrecursiveHOLExact_clock_le program state.toExact pair hpair

/-- Finite local write keeps the clock. -/
theorem setVarHOLFinite_clock {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setVarHOLFinite name value state).clock = state.clock := rfl

/-- Finite global write keeps the clock. -/
theorem setGlobalHOLFinite_clock {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setGlobalHOLFinite name value state).clock = state.clock := rfl

/-- Finite keyed write keeps the clock. -/
theorem setKvarHOLFinite_clock {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) :
    (setKvarHOLFinite kind name value state).clock = state.clock := by
  cases kind <;> rfl

/-- Finite locals clearing keeps the clock. -/
theorem emptyLocalsHOLFinite_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    (emptyLocalsHOLFinite state).clock = state.clock := rfl

/-- Finite dec-clock never increases the clock. -/
theorem decClockHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    (decClockHOLFinite state).clock ≤ state.clock := by
  simp only [decClockHOLFinite]
  omega

/-- Finite call-entry state never increases the clock. -/
theorem callEntryStateHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) :
    (callEntryStateHOLFinite state callee).clock ≤ state.clock := by
  simp only [callEntryStateHOLFinite]
  omega

/-- Finite handler state keeps the fixed context clock. -/
theorem handlerStateHOLFinite_clock {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedContext : FiniteEvalContext width σ)
    (name : MlS) (value : ValueHOL width) :
    (handlerStateHOLFinite context fixedContext name value).clock =
      fixedContext.state.clock := rfl

/-- Finite fixed `Call`/`DecCall` context clock is bounded by the entry clock. -/
theorem callFixedContextHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ) :
    (callFixedContextHOLFinite entry bodyResult bodyContext).state.clock ≤ entry.clock := by
  show (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.clock ≤ entry.clock
  exact fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state)

/-- Finite `DecCall` continuation context clock is bounded by the fixed context. -/
theorem callContinuationContextHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedContext : FiniteEvalContext width σ)
    (resultName : MlS) (value : ValueHOL width) :
    (callContinuationContextHOLFinite context fixedContext resultName value).state.clock ≤
      fixedContext.state.clock := by
  show (handlerStateHOLFinite context fixedContext resultName value).clock ≤
    fixedContext.state.clock
  rw [handlerStateHOLFinite_clock]
  exact Nat.le_refl _

macro "clockDirect" : tactic => `(tactic|
  first
  | exact Nat.le_refl _
  | (simp only [FiniteEvalContext.withState_state, emptyLocalsHOLFinite_clock,
       FiniteEvalContext.emptyLocalsContextHOLFinite_state]; exact Nat.le_refl _)
  | exact decClockHOLFinite_clock_le _
  | exact fixClockHOLFinite_clock_le _ _
  | exact Nat.le_trans (fixClockHOLFinite_clock_le _ _) (decClockHOLFinite_clock_le _)
  | exact callFixedContextHOLFinite_clock_le _ _ _
  | exact Nat.le_trans (callFixedContextHOLFinite_clock_le _ _ _)
      (callEntryStateHOLFinite_clock_le _ _))

set_option maxHeartbeats 4000000 in
theorem evalPanSemRecursiveCallFiniteContext_clock_le_aux {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    ∀ (result : Option (PanSemResultExact width) × FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext program context = some result →
      result.2.state.clock ≤ context.state.clock := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context
  case case3 =>
    rename_i inst context state name shape initializer body value x1 hshape bodyState bodyContext
      r postContext hrec restored ih1
    intro result hres
    cases hres
    have hbody := ih1 (r, postContext) hrec
    have hctx : bodyContext.state.clock = context.state.clock := rfl
    rw [hctx] at hbody
    exact hbody
  case case6 =>
    rename_i inst context state first second postContext x fixed fixedContext ih2 ih1
    intro result hres
    exact Nat.le_trans (ih1 result hres)
      (fixClockHOLFinite_clock_le state (none, postContext.state))
  case case7 =>
    rename_i inst context state first second postContext val x fixed fixedContext ih1
    intro result hres
    cases hres
    exact fixClockHOLFinite_clock_le state (some val, postContext.state)
  case case8 =>
    rename_i inst context state condition thenBranch elseBranch value x h ih1
    intro result hres
    exact ih1 result hres
  case case9 =>
    rename_i inst context state condition thenBranch elseBranch value x h ih1
    intro result hres
    exact ih1 result hres
  case case13 =>
    rename_i inst context state condition body value x1 hne hclock entry entryContext postContext
      xrec fixed fixedContext ih2 ih1
    intro result hres
    exact Nat.le_trans (ih1 result hres)
      (Nat.le_trans (fixClockHOLFinite_clock_le entry (_, postContext.state))
        (decClockHOLFinite_clock_le state))
  case case14 =>
    rename_i inst context state condition body value x1 hne hclock entry entryContext postContext
      xrec fixed fixedContext ih2 ih1
    intro result hres
    exact Nat.le_trans (ih1 result hres)
      (Nat.le_trans (fixClockHOLFinite_clock_le entry (_, postContext.state))
        (decClockHOLFinite_clock_le state))
  case case15 =>
    rename_i inst context state condition body value x1 hne hclock entry entryContext postContext
      xrec fixed fixedContext ih1
    intro result hres
    cases hres
    exact Nat.le_trans (fixClockHOLFinite_clock_le entry (_, postContext.state))
      (decClockHOLFinite_clock_le state)
  case case16 =>
    rename_i inst context state condition body value x4 hne hclock entry entryContext r postContext
      xrec fixed fixedContext hcont hnone hbreak ih1
    intro result hres
    cases hres
    exact Nat.le_trans (fixClockHOLFinite_clock_le entry (_, postContext.state))
      (decClockHOLFinite_clock_le state)
  case case27 =>
    rename_i inst context state function arguments values x2 body callee returnShape x1 hclock entry
      entryContext postContext value hshape snd xrec fixedContext ih1
    intro result hres
    cases hres
    exact Nat.le_trans (callFixedContextHOLFinite_clock_le entry _ postContext)
      (callEntryStateHOLFinite_clock_le state callee)
  case case28 =>
    rename_i inst context state function arguments values x2 body callee returnShape x1 hclock entry
      entryContext postContext value hshape kind name snd hvalid xrec fixedContext ih1
    intro result hres
    cases hres
    cases kind <;>
      exact Nat.le_trans (callFixedContextHOLFinite_clock_le entry _ postContext)
        (callEntryStateHOLFinite_clock_le state callee)
  case case33 =>
    rename_i inst context state function arguments values x3 body callee returnShape x2 hclock entry
      entryContext postContext value fst handlerId handlerVar handlerProgram shape hshape
      xeshapes xrec fixedContext handlerState handlerContext ih2 ih1
    intro result hres
    exact Nat.le_trans (ih1 result hres)
      (Nat.le_trans (Nat.le_of_eq (handlerStateHOLFinite_clock context fixedContext handlerVar value))
        (Nat.le_trans (callFixedContextHOLFinite_clock_le entry _ postContext)
          (callEntryStateHOLFinite_clock_le state callee)))
  case case46 =>
    rename_i inst context state resultName shape function arguments continuation values x3 body callee
      returnShape x2 hclock entry entryContext postContext1 value hshape result0 postContext restored
      xbody fixedContext continuationContext xcont ih2 ih1
    intro result hres
    cases hres
    have hcont := ih1 (result0, postContext) xcont
    have h1c := callContinuationContextHOLFinite_clock_le context fixedContext resultName value
    have h2c : fixedContext.state.clock ≤ context.state.clock :=
      Nat.le_trans (callFixedContextHOLFinite_clock_le entry _ postContext1)
        (callEntryStateHOLFinite_clock_le state callee)
    exact Nat.le_trans hcont (Nat.le_trans h1c h2c)
  case case63 =>
    rename_i inst context state size kind name address evalExpression output
    intro result hres
    cases hres
    letI : DecidablePred state.toExact.shMemaddrs := context.shMemaddrsDecidable
    exact Nat.le_of_eq (shMemLoadClauseHOLExact_clock state.toExact size kind name address evalExpression)
  case case64 =>
    rename_i inst context state size address value evalExpression output
    intro result hres
    cases hres
    letI : DecidablePred state.toExact.shMemaddrs := context.shMemaddrsDecidable
    exact Nat.le_of_eq (shMemStoreClauseHOLExact_clock state.toExact size address value evalExpression)
  case case66 =>
    rename_i inst context state other h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 pair hresNonrec
    intro result hres
    cases hres
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    letI : DecidablePred state.shMemaddrs := context.shMemaddrsDecidable
    exact evalPanSemNonrecursiveHOLFinite_clock_le state other pair hresNonrec
  all_goals
    (intro result hres
     cases hres <;> clockDirect)

/-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag): the analogue
    of HOL `evaluate_clock` (`panSemScript.sml:755-766`,
    `!prog s r s'. evaluate (prog,s) = (r,s') ==> s'.clock <= s.clock`).
    HOL quantifies over the faithful `panSem$state`; this theorem is stated over
    the exact finite-support clause-for-clause evaluator
    `evalPanSemRecursiveCallFiniteContext`, which takes a `FiniteEvalContext`
    (state plus threaded `DecidablePred` `memaddrs`/`shMemaddrs` fields) instead
    of a bare state, and whose carrier `PanSemStateFiniteExact` uses canonical
    `HolFiniteMapExact` maps rather than HOL's mlstring-keyed finite maps. The
    extra decider context argument and the finite-map carrier representation are
    differences beyond `names_as_string`, so the tag is withheld; the faithful
    HOL `evaluate`/`evaluate_clock` port over the exact context is tracked by
    `flapjack-qj5` (bead `flapjack-4ac.3.48`). -/
theorem evalPanSemRecursiveCallFiniteContext_clock_le {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ)
    (result : Option (PanSemResultExact width) × FiniteEvalContext width σ)
    (h : evalPanSemRecursiveCallFiniteContext program context = some result) :
    result.2.state.clock ≤ context.state.clock :=
  evalPanSemRecursiveCallFiniteContext_clock_le_aux program context result h

/-- HOL `fix_clock_evaluate` (`panSemScript.sml:768-775`) over the finite-map
    source evaluator: the evaluated result clock already lies below the input
    clock, so clamping it leaves the pair unchanged. -/
theorem fixClockHOLFinite_evaluate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    fixClockHOLFinite state (evaluateHOLFiniteState state program) =
      evaluateHOLFiniteState state program := by
  classical
  have hle : (evaluateHOLFiniteState state program).2.clock ≤ state.clock := by
    rw [evaluateHOLFiniteState_eq_withDeciders state program]
    unfold evaluateHOLFiniteStateWithDeciders
    split
    · rename_i pair hpair
      exact evalPanSemRecursiveCallFiniteContext_clock_le program ⟨state, h, hshared⟩ pair hpair
    · exact Nat.le_refl _
  cases hres : evaluateHOLFiniteState state program with
  | mk r st =>
    rw [hres] at hle
    change st.clock ≤ state.clock at hle
    simp only [fixClockHOLFinite]
    rw [if_neg (by omega)]

end Flapjack
