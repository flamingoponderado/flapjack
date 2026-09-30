import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

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
      xeshapes xrec fixedContext handlerContext ih2 ih1
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

namespace PanSemStateFiniteExact

/-- The line-780 rewrite-restated While conjunct of HOL `evaluate_def`
    (`panSemScript.sml:780`). Unlike the line-556 equation, HOL has rewritten
    `fix_clock` away using `fix_clock_evaluate`; the finite evaluator does the
    same through `fixClockHOLFinite_evaluate`. The clock-zero timeout,
    condition failure, recursive Continue/NONE cases, Break, and propagation
    branches remain exactly those of the source definition. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_while_fixClockRewrite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (condition : ExpHOL width)
    (body : ProgHOL width) :
    evaluateHOLFiniteState state (.while condition body : ProgHOL width) =
    (match @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) condition with
       | some (.val (.word word)) =>
           if word ≠ 0 then
             if state.clock = 0 then (some .timeOut, emptyLocalsHOLFinite state)
             else
               let bodyOutput :=
                 evaluateHOLFiniteState (decClockHOLFinite state) body
               match bodyOutput.1 with
               | none => evaluateHOLFiniteState bodyOutput.2 (.while condition body)
               | some .continue => evaluateHOLFiniteState bodyOutput.2 (.while condition body)
               | some .break => (none, bodyOutput.2)
               | some result => (some result, bodyOutput.2)
           else (none, state)
       | _ => (some .error, state)) := by
  classical
  rw [evaluateHOLFiniteState_while_total]
  simp only [fixClockHOLFinite_evaluate]
  rfl

end PanSemStateFiniteExact

/-! ## Public HOL-shaped clock theorems over the pair-shaped finite evaluator

These are the coordinator-requested public statements: HOL `evaluate_clock` and
`fix_clock_evaluate` shape over `PanSemStateFiniteExact` /
`evaluateHOLFiniteState`, with **no** explicit `DecidablePred` binders and **no**
success premise. The decidability witnesses are chosen classically inside
`evaluateHOLFiniteState`, so they add no logical premise, and the pair-shaped
evaluator is total, so the earlier `= some result` hypotheses are unnecessary.
The stronger premise-free bound `evaluateHOLFiniteState_clock_le` below stays
untagged (it omits HOL's result/post-state variables and equality premise),
while the exact-shape corollary `evaluateHOLFiniteState_clock_le_result` and
`fixClockHOLFinite_evaluateState` carry the reviewed
`(fmap_as_finite_support := [locals, globals, code, eshapes])`
`(words_as_type_indexed_bitvec)` tags after coordinator source/carrier review
(bead `flapjack-pxn.18.3.6.9.23.1`). -/

/-- Stronger untagged clock bound over the pair-shaped finite source evaluator:
    for every program and source state the evaluated result clock is bounded by
    the input clock. No `DecidablePred` binder (chosen classically in
    `evaluateHOLFiniteState`) and no success premise. Kept untagged: it is
    mathematically derivable from HOL `evaluate_clock` but omits HOL's result and
    post-state variables and its equality premise, so it is not an exact
    statement-shape port. The exact-shape tagged corollary is
    `evaluateHOLFiniteState_clock_le_result` below. -/
theorem evaluateHOLFiniteState_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width) :
    (evaluateHOLFiniteState state program).2.clock ≤ state.clock := by
  classical
  rw [evaluateHOLFiniteState_eq_withDeciders state program]
  unfold evaluateHOLFiniteStateWithDeciders
  split
  · rename_i pair hpair
    exact evalPanSemRecursiveCallFiniteContext_clock_le program _ pair hpair
  · exact Nat.le_refl _

/-- Exact-shape port of HOL `evaluate_clock` (`panSemScript.sml:755-766`):
    `!prog s r s'. evaluate (prog,s) = (r,s') ==> s'.clock <= s.clock`. Over the
    pair-shaped finite evaluator this is the result/state-indexed corollary of
    the stronger untagged `evaluateHOLFiniteState_clock_le`; the source state maps
    are the reviewed `HolFiniteMapExact` fields of `PanSemStateFiniteExact`, and
    the words are positive-width `BitVec width`. The equality premise and the
    result/post-state variables match HOL exactly; no `DecidablePred` binder or
    extra premise. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_clock"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_clock_le_result {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width)
    (result : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
    (h : evaluateHOLFiniteState state program = (result, st)) :
    st.clock ≤ state.clock := by
  have hle := evaluateHOLFiniteState_clock_le state program
  rw [h] at hle
  exact hle

/-- Exact-shape port of HOL `fix_clock_evaluate` (`panSemScript.sml:768-775`):
    `fix_clock s (evaluate (prog,s)) = evaluate (prog,s)`. Over the pair-shaped
    finite evaluator, clamping the evaluated pair at the input clock leaves it
    unchanged. No `DecidablePred` binder (chosen classically) and no success
    premise. The source state maps are the reviewed `HolFiniteMapExact` fields of
    `PanSemStateFiniteExact`, and the words are positive-width `BitVec width`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_evaluate"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem fixClockHOLFinite_evaluateState {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width) :
    fixClockHOLFinite state (evaluateHOLFiniteState state program) =
      evaluateHOLFiniteState state program := by
  classical
  exact fixClockHOLFinite_evaluate state program


/-- FLAPJACK-SPECIFIC (not a HOL declaration): the finite `Call`/`DecCall` body
    result already satisfies the evaluated-clock bound, so the finite
    `fix_clock` on the body pair is the identity. This is the rewrite used to
    restate HOL `evaluate_def`'s `Call` clause at line 780 without the source
    definition's inner `fix_clock` (HOL `fix_clock_evaluate`). -/
theorem callFixedContextHOLFinite_eq_of_body {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateFiniteExact width σ) (body : ProgHOL width)
    (bodyResult : Option (PanSemResultExact width)) (bodyContext : FiniteEvalContext width σ)
    (hbodyOutput : evaluateHOLFiniteState entry body = (bodyResult, bodyContext.state)) :
    callFixedContextHOLFinite entry bodyResult bodyContext = bodyContext := by
  have hfix : fixClockHOLFinite entry (bodyResult, bodyContext.state) =
      (bodyResult, bodyContext.state) := by
    rw [← hbodyOutput]
    exact fixClockHOLFinite_evaluateState entry body
  unfold callFixedContextHOLFinite
  apply FiniteEvalContext.ext
  exact congrArg Prod.snd hfix

/-- Flapjack-specific `Call` argument-failure helper for the HOL conjunct at
    `panSemScript.sml:780`. Its branch-selector hypothesis is absent from that
    unconditional equation, so this helper is not tagged as a port. -/
theorem evaluateHOLFiniteState_call_args_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = none) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, state) := by
  classical
  have hargsExact : @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments = none := by
    simpa only [evalListHOLFinite_eq_toExact] using hargs
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext.eq_5, hargsExact]

/-- Flapjack-specific `Call` lookup-failure helper for the HOL conjunct at
    `panSemScript.sml:780`. Its branch-selector hypotheses are absent from
    that unconditional equation, so this helper is not tagged as a port. -/
theorem evaluateHOLFiniteState_call_lookup_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values = none) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, state) := by
  classical
  have hargsExact : @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some values := by
    simpa only [evalListHOLFinite_eq_toExact] using hargs
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext.eq_5, hargsExact, hlookup]

/-- Flapjack-specific `Call` clock-exhaustion helper for the HOL conjunct at
    `panSemScript.sml:780`. Its argument, lookup, and clock branch selectors
    are absent from that unconditional equation, so it is not tagged. -/
theorem evaluateHOLFiniteState_call_clock_zero {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock = 0) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .timeOut, emptyLocalsHOLFinite state) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock = 0 := by
    simpa only [context] using hclock
  have htimeout : evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .timeOut, FiniteEvalContext.emptyLocalsContextHOLFinite context) := by
    rw [evalPanSemRecursiveCallFiniteContext.eq_def]
    dsimp only
    rw [hargsContext]
    dsimp only
    rw [lookupCodeCanonicalHOL, hlookupContext]
    dsimp only
    rw [if_pos hclockContext]
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [htimeout]
  rfl

/-- HOL `evaluate_def` line-780 `Call` body `NONE` branch
    (`panSemScript.sml:668`, with the line-780 rewrite removing the inner
    `fix_clock` on the recursive callee-body evaluation): a callee that falls
    through with no result maps to `Error` at the callee post-state. The RHS
    carries the body output state directly, matching the `fix_clock_evaluate`
    rewrite. One constructor case of the theorem; the full 21-equation theorem
    remains open. This is a Flapjack-specific branch helper: its `hargs`/`hlookup`/`hclock`/`hbody` branch selectors are absent from that unconditional equation, so it is not tagged as a port.
    -/
theorem evaluateHOLFiniteState_call_body_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (none, postState)) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (none, postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        none postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body none postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_body_none
    info function arguments context values body callee returnShape postContext
    hargsContext hlookupContext hclockContext hbodyInternal
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- HOL `evaluate_def` line-780 `Call` body `Break` branch
    (`panSemScript.sml:669`): a callee that breaks maps to `Error` at the callee
    post-state. One constructor case of the theorem. This is a Flapjack-specific branch helper: its branch selectors are absent from that unconditional equation, so it is not tagged as a port.
    -/
theorem evaluateHOLFiniteState_call_body_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some .break, postState)) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some .break, postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some .break) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some .break) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_body_break
    info function arguments context values body callee returnShape postContext    hargsContext hlookupContext hclockContext hbodyInternal
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- HOL `evaluate_def` line-780 `Call` body `Continue` branch
    (`panSemScript.sml:670`): a callee that continues maps to `Error` at the
    callee post-state. One constructor case of the theorem. This is a Flapjack-specific branch helper: its branch selectors are absent from that unconditional equation, so it is not tagged as a port.
    -/
theorem evaluateHOLFiniteState_call_body_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some .continue, postState)) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some .continue, postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some .continue) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some .continue) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_body_continue
    info function arguments context values body callee returnShape postContext    hargsContext hlookupContext hclockContext hbodyInternal
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- HOL `evaluate_def` line-780 `Call` returned-value branch with
    `caltyp = NONE` (`panSemScript.sml:673-674`): the returned value is
    preserved at empty locals of the callee post-state. One constructor case of
    the theorem. This is a Flapjack-specific branch helper: its branch selectors are absent from that unconditional equation, so it is not tagged as a port.
    -/
theorem evaluateHOLFiniteState_call_return_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (value : ValueHOL width)
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), postState))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    evaluateHOLFiniteState state (.call none function arguments : ProgHOL width) =
      (some (.returned value), emptyLocalsHOLFinite postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.returned value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.returned value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.returned value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_return_none
    function arguments context values body callee returnShape value postContext
    hargsContext hlookupContext hclockContext hbodyInternal hshape
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call none function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.emptyLocalsContextHOLFinite_state, hpostContext]

/-- HOL `evaluate_def` line-780 `Call` unhandled-exception branch with
    `caltyp = NONE` (`panSemScript.sml:683-684`): the exception propagates at
    empty locals of the callee post-state. One constructor case of the theorem. This is a Flapjack-specific branch helper: its branch selectors are absent from that unconditional equation, so it is not tagged as a port.
    -/
theorem evaluateHOLFiniteState_call_exception_unhandled {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (exceptionId : MlS) (value : ValueHOL width)
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception exceptionId value), postState)) :
    evaluateHOLFiniteState state (.call none function arguments : ProgHOL width) =
      (some (.exception exceptionId value), emptyLocalsHOLFinite postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception exceptionId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception exceptionId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception exceptionId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_exception_unhandled
    function arguments context values body callee returnShape exceptionId value postContext
    hargsContext hlookupContext hclockContext hbodyInternal
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call none function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.emptyLocalsContextHOLFinite_state, hpostContext]

/-- Flapjack-specific `Call` returned-value shape-mismatch helper for the HOL
    conjunct at `panSemScript.sml:780`. Its branch selectors are absent from the
    unconditional equation, so it is not tagged as a port. -/
theorem evaluateHOLFiniteState_call_return_shape_mismatch {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), postState))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = false) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.returned value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.returned value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.returned value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_return_shape_mismatch info function arguments context values body callee returnShape value postContext hargsContext hlookupContext hclockContext hbodyInternal hshape
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- Flapjack-specific `Call` returned-value `caltyp = SOME (NONE, h)` helper
    for HOL `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_return_caller_locals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), postState))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    evaluateHOLFiniteState state (.call (some (none, handler)) function arguments : ProgHOL width) =
      (none, { postState with locals := state.locals }) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.returned value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.returned value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.returned value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_return_caller_locals handler function arguments context values body callee returnShape value postContext hargsContext hlookupContext hclockContext hbodyInternal hshape
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (none, handler)) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.withState_state, callRestoreLocalsContextHOLFinite,
    hpostContext, context]

/-- Flapjack-specific `Call` wrapped-result valid-target helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_return_set_kvar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), postState))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (hvalid : isValidValueHOLExact state.toExact kind name value = true) :
    evaluateHOLFiniteState state
        (.call (some (some (kind, name), handler)) function arguments : ProgHOL width) =
      (none, setKvarHOLFinite kind name value { postState with locals := state.locals }) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.returned value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.returned value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.returned value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_return_set_kvar kind name handler function arguments context values body callee returnShape value postContext hargsContext hlookupContext hclockContext hbodyInternal hshape hvalid
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (some (kind, name), handler)) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.withState_state, callSetKvarContextHOLFinite,
    hpostContext, context]

/-- Flapjack-specific `Call` wrapped-result invalid-target helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_return_kvar_invalid {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), postState))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (hinvalid : isValidValueHOLExact state.toExact kind name value = false) :
    evaluateHOLFiniteState state
        (.call (some (some (kind, name), handler)) function arguments : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.returned value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.returned value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.returned value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_return_kvar_invalid kind name handler function arguments context values body callee returnShape value postContext hargsContext hlookupContext hclockContext hbodyInternal hshape hinvalid
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (some (kind, name), handler)) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- Flapjack-specific `Call` unhandled-exception `caltyp = SOME (ri, NONE)` helper
    for HOL `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_exception_no_handler {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (returnInfo : Option (VarKind × MlS))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception exceptionId value), postState)) :
    evaluateHOLFiniteState state
        (.call (some (returnInfo, none)) function arguments : ProgHOL width) =
      (some (.exception exceptionId value), emptyLocalsHOLFinite postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception exceptionId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception exceptionId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception exceptionId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_exception_no_handler returnInfo function arguments context values body callee returnShape exceptionId value postContext hargsContext hlookupContext hclockContext hbodyInternal
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (returnInfo, none)) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.emptyLocalsContextHOLFinite_state, hpostContext]

/-- Flapjack-specific `Call` non-matching-handler helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_exception_mismatch {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width)
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception exceptionId value), postState))
    (hne : ¬ exceptionId = handlerId) :
    evaluateHOLFiniteState state
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments
          : ProgHOL width) =
      (some (.exception exceptionId value), emptyLocalsHOLFinite postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception exceptionId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception exceptionId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception exceptionId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_exception_mismatch returnInfo handlerId handlerVar handlerProgram function arguments context values body callee returnShape exceptionId value postContext hargsContext hlookupContext hclockContext hbodyInternal hne
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.emptyLocalsContextHOLFinite_state, hpostContext]

/-- Flapjack-specific `Call` matching-handler missing-shape helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_exception_missing_shape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width)
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception exceptionId value), postState))
    (heq : exceptionId = handlerId)
    (hshapeNone : state.eshapes.lookup exceptionId = none) :
    evaluateHOLFiniteState state
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments
          : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception exceptionId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception exceptionId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception exceptionId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_exception_missing_shape returnInfo handlerId handlerVar handlerProgram function arguments context values body callee returnShape exceptionId value postContext hargsContext hlookupContext hclockContext hbodyInternal heq hshapeNone
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- Flapjack-specific `Call` matching-handler invalid-target/shape helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_exception_invalid {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width) (declaredShape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception exceptionId value), postState))
    (heq : exceptionId = handlerId)
    (hshapeSome : state.eshapes.lookup exceptionId = some declaredShape)
    (hinvalid : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
      isValidValueHOLExact state.toExact VarKind.local handlerVar value) = false) :
    evaluateHOLFiniteState state
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments
          : ProgHOL width) =
      (some .error, postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception exceptionId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception exceptionId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception exceptionId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_exception_invalid returnInfo handlerId handlerVar handlerProgram declaredShape function arguments context values body callee returnShape exceptionId value postContext hargsContext hlookupContext hclockContext hbodyInternal heq hshapeSome hinvalid
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [hpostContext]

/-- Flapjack-specific `Call` matching-handler recursion helper for HOL
    `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_matched_exception_handler {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (function : MlS) (handlerProgram : ProgHOL width)
    (body : ProgHOL width) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (postState : PanSemStateFiniteExact width σ)
    (declaredShape : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception handlerId value), postState))
    (hshape : state.eshapes.lookup handlerId = some declaredShape)
    (hshapeEq : shapeEqHOL (shapeOfHOLExact value) declaredShape = true)
    (hvalid : isValidValueHOLExact state.toExact VarKind.local handlerVar value = true) :
    evaluateHOLFiniteState state
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments
          : ProgHOL width) =
      evaluateHOLFiniteState
        (setVarHOLFinite handlerVar value { postState with locals := state.locals })
        handlerProgram := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some (.exception handlerId value), postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some (.exception handlerId value)) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some (.exception handlerId value)) postContext (by rw [hpostContext]; exact hbody)
  have hcall := evalPanSemRecursiveCallFiniteContext_call_matched_exception_handler
    returnInfo handlerId handlerVar function handlerProgram body arguments context values callee
    returnShape value postContext declaredShape hargsContext hlookupContext hclockContext
    hbodyInternal hshape hshapeEq hvalid
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state
    (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram))) function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  rw [evaluateHOLFiniteState_eq_recursiveContext]
  rw [show (⟨setVarHOLFinite handlerVar value { postState with locals := state.locals },
        fun address => Classical.propDecidable ((setVarHOLFinite handlerVar value
          { postState with locals := state.locals }).memaddrs address),
        fun address => Classical.propDecidable ((setVarHOLFinite handlerVar value
          { postState with locals := state.locals }).shMemaddrs address)⟩ :
        FiniteEvalContext width σ) =
      postContext.withState (handlerStateHOLFinite context postContext handlerVar value)
        rfl rfl from by
    apply FiniteEvalContext.ext
    simp only [FiniteEvalContext.withState_state, handlerStateHOLFinite, hpostContext, context]]
  dsimp only
  have hcontinuationContext :
      callContinuationContextHOLFinite context postContext handlerVar value =
        postContext.withState (handlerStateHOLFinite context postContext handlerVar value)
          rfl rfl := rfl
  rw [← hcontinuationContext]
  obtain ⟨output, houtput⟩ := evalPanSemRecursiveCallFiniteContext_total handlerProgram
    (callContinuationContextHOLFinite context postContext handlerVar value)
  rw [houtput]

/-- Flapjack-specific `Call` fallback result helper (error / timeout / final FFI)
    for HOL `panSemScript.sml:780`; not tagged (branch selectors absent). -/
theorem evaluateHOLFiniteState_call_body_fallback {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (other : PanSemResultExact width)
    (postState : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some other, postState))
    (hother : other = .error ∨ other = .timeOut ∨ ∃ event, other = .finalFfi event) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (some other, emptyLocalsHOLFinite postState) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa only [context] using hargs
  have hlookupContext :
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) := by
    simpa only [context] using hlookup
  have hclockContext : context.state.clock ≠ 0 := by
    simpa only [context] using hclock
  obtain ⟨postContext, hbodyInternal, hpostContext⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee)
      (by rfl) (some other, postState) hbody
  have hfixed :
      callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
        (some other) postContext = postContext :=
    callFixedContextHOLFinite_eq_of_body (callEntryStateHOLFinite context.state callee)
      body (some other) postContext (by rw [hpostContext]; exact hbody)
  have hcall : evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some other,
        (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some other) postContext).withState
          (emptyLocalsHOLFinite (callFixedContextHOLFinite
            (callEntryStateHOLFinite context.state callee) (some other) postContext).state)
          rfl rfl) := by
    rw [evalPanSemRecursiveCallFiniteContext.eq_5]
    simp only [hargsContext, hlookupContext, if_neg hclockContext, hbodyInternal]
    rcases hother with rfl | rfl | ⟨event, rfl⟩ <;> rfl
  rw [hfixed] at hcall
  rw [evaluateHOLFiniteState_eq_withDeciders state (.call info function arguments)]
  simp only [evaluateHOLFiniteStateWithDeciders]
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl]
  rw [hcall]
  simp only [FiniteEvalContext.withState_state, hpostContext]



/-
HOL `evaluate_def` line-780 `Call` conjunct (fix_clock-free restatement) over the
pair-shaped finite source evaluator. This is the single unconditional source
`Definition evaluate_def` (line 556) `Call` clause with the inner `fix_clock` on
the recursive callee-body evaluation rewritten away by line 780's
`REWRITE_RULE [fix_clock_evaluate]` (via the finite `fixClockHOLFinite_evaluateState`).
No extra premise. The full 21-clause assembly is
`evaluateHOLFiniteState_eq_evaluate_def` (bead `flapjack-qj5.9.6`).

Declaration review against `panSemScript.sml:657-693`: the equation preserves
`OPT_MMAP` argument evaluation and `lookup_code`, the clock-zero timeout state,
the callee post-state for invalid results, return-shape check, all call-info
return branches, exception matching/shape/local-validity checks, handler
evaluation, and empty-locals propagation. `ProgHOL.call` has the same nested
option/tuple fields as HOL `Call`; its identifiers use faithful `MlS`
(`MlString`, not Lean `String`) and occur only in map keys or equality tests
here. The owner state `PanSemStateFiniteExact` carries the named four
`HolFiniteMapExact` fields, while `ValueHOL` and `ProgHOL` use the reviewed
positive-width `HolWordLab`/`ExpHOL` carriers. `shapeEqHOL = true` is proved
equivalent to structural HOL shape equality by `shapeEqHOL_eq_true`. Thus the
two tag qualifiers record only the finite-map and word-carrier translations;
no additional premise, name representation, or output behavior difference is
hidden by them.
-/
set_option maxHeartbeats 2000000 in
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_call {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) :
    evaluateHOLFiniteState state (.call info function arguments : ProgHOL width) =
      (match evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
       | none => (some .error, state)
       | some values =>
           match lookupCodeHOLFinite state.code.lookup function values with
           | none => (some .error, state)
           | some (body, callee, returnShape) =>
               if state.clock = 0 then
                 (some .timeOut, emptyLocalsHOLFinite state)
               else
                 match evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
                 | (none, st) => (some .error, st)
                 | (some .break, st) => (some .error, st)
                 | (some .continue, st) => (some .error, st)
                 | (some (.returned value), st) =>
                     if shapeEqHOL (shapeOfHOLExact value) returnShape then
                       (match info with
                        | none => (some (.returned value), emptyLocalsHOLFinite st)
                        | some (none, _) => (none, { st with locals := state.locals })
                        | some (some (kind, name), _) =>
                            if isValidValueHOLExact state.toExact kind name value then
                              (none, setKvarHOLFinite kind name value
                                { st with locals := state.locals })
                            else (some .error, st))
                     else (some .error, st)
                 | (some (.exception exceptionId value), st) =>
                     (match info with
                      | none =>
                          (some (.exception exceptionId value), emptyLocalsHOLFinite st)
                      | some (_, none) =>
                          (some (.exception exceptionId value), emptyLocalsHOLFinite st)
                      | some (_, some (handlerId, handlerVar, handlerProgram)) =>
                          if exceptionId = handlerId then
                            (match state.eshapes.lookup exceptionId with
                             | some shape =>
                                 if shapeEqHOL (shapeOfHOLExact value) shape &&
                                     isValidValueHOLExact state.toExact .local handlerVar value
                                 then
                                   evaluateHOLFiniteState
                                     (setVarHOLFinite handlerVar value
                                       { st with locals := state.locals }) handlerProgram
                                 else (some .error, st)
                             | none => (some .error, st))
                          else (some (.exception exceptionId value),
                            emptyLocalsHOLFinite st))
                 | (some other, st) => (some other, emptyLocalsHOLFinite st)) := by
  classical
  cases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none =>
      rw [evaluateHOLFiniteState_call_args_none state info function arguments hargs]
  | some values =>
      cases hlookup : lookupCodeHOLFinite state.code.lookup function values with
      | none =>
          rw [evaluateHOLFiniteState_call_lookup_none state info function arguments values
            hargs hlookup]
          simp only [hlookup]
      | some entry =>
          obtain ⟨body, callee, returnShape⟩ := entry
          by_cases hclock : state.clock = 0
          · rw [evaluateHOLFiniteState_call_clock_zero state info function arguments values
              body callee returnShape hargs hlookup hclock]
            simp only [hlookup, if_pos hclock]
          · cases hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
            | mk bodyResult postState =>
              cases bodyResult with
              | none =>
                  rw [evaluateHOLFiniteState_call_body_error state info function arguments values
                    body callee returnShape postState hargs hlookup hclock hbody]
                  simp only [hlookup, if_neg hclock, hbody]
              | some r =>
                  cases r with
                  | «break» =>
                      rw [evaluateHOLFiniteState_call_body_break state info function arguments
                        values body callee returnShape postState hargs hlookup hclock hbody]
                      simp only [hlookup, if_neg hclock, hbody]
                  | «continue» =>
                      rw [evaluateHOLFiniteState_call_body_continue state info function arguments
                        values body callee returnShape postState hargs hlookup hclock hbody]
                      simp only [hlookup, if_neg hclock, hbody]
                  | error =>
                      rw [evaluateHOLFiniteState_call_body_fallback state info function arguments
                        values body callee returnShape .error postState hargs hlookup hclock hbody
                        (Or.inl rfl)]
                      simp only [hlookup, if_neg hclock, hbody]
                  | timeOut =>
                      rw [evaluateHOLFiniteState_call_body_fallback state info function arguments
                        values body callee returnShape .timeOut postState hargs hlookup hclock hbody
                        (Or.inr (Or.inl rfl))]
                      simp only [hlookup, if_neg hclock, hbody]
                  | finalFfi event =>
                      rw [evaluateHOLFiniteState_call_body_fallback state info function arguments
                        values body callee returnShape (.finalFfi event) postState hargs hlookup
                        hclock hbody (Or.inr (Or.inr ⟨event, rfl⟩))]
                      simp only [hlookup, if_neg hclock, hbody]
                  | returned value =>
                      by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
                      · cases info with
                        | none =>
                            rw [evaluateHOLFiniteState_call_return_none state value function
                              arguments values body callee returnShape postState hargs hlookup
                              hclock hbody hshape]
                            simp only [hlookup, if_neg hclock, hbody, if_pos hshape]
                        | some istr =>
                            obtain ⟨returns, handler⟩ := istr
                            cases returns with
                            | none =>
                                rw [evaluateHOLFiniteState_call_return_caller_locals state handler
                                  function arguments values body callee returnShape value postState
                                  hargs hlookup hclock hbody hshape]
                                simp only [hlookup, if_neg hclock, hbody, if_pos hshape]
                            | some kn =>
                                obtain ⟨kind, name⟩ := kn
                                by_cases hvalid : isValidValueHOLExact state.toExact kind name value = true
                                · rw [evaluateHOLFiniteState_call_return_set_kvar state kind name
                                    handler function arguments values body callee returnShape value
                                    postState hargs hlookup hclock hbody hshape hvalid]
                                  simp only [hlookup, if_neg hclock, hbody, if_pos hshape,
                                    if_pos hvalid]
                                · have hvalidFalse : isValidValueHOLExact state.toExact kind name value = false := by
                                    cases h : isValidValueHOLExact state.toExact kind name value <;>
                                      simp_all
                                  rw [evaluateHOLFiniteState_call_return_kvar_invalid state kind name
                                    handler function arguments values body callee returnShape value
                                    postState hargs hlookup hclock hbody hshape hvalidFalse]
                                  simp only [hlookup, if_neg hclock, hbody, if_pos hshape,
                                    if_neg hvalid]
                      · have hshapeFalse : shapeEqHOL (shapeOfHOLExact value) returnShape = false := by
                          cases h : shapeEqHOL (shapeOfHOLExact value) returnShape <;> simp_all
                        rw [evaluateHOLFiniteState_call_return_shape_mismatch state info function
                          arguments values body callee returnShape value postState hargs hlookup
                          hclock hbody hshapeFalse]
                        simp only [hlookup, if_neg hclock, hbody, if_neg hshape]
                  | exception eid value =>
                      cases info with
                      | none =>
                          rw [evaluateHOLFiniteState_call_exception_unhandled state eid value
                            function arguments values body callee returnShape postState hargs
                            hlookup hclock hbody]
                          simp only [hlookup, if_neg hclock, hbody]
                      | some istr =>
                          obtain ⟨returns, handler⟩ := istr
                          cases handler with
                          | none =>
                              rw [evaluateHOLFiniteState_call_exception_no_handler state returns
                                function arguments values body callee returnShape eid value
                                postState hargs hlookup hclock hbody]
                              simp only [hlookup, if_neg hclock, hbody]
                          | some hkn =>
                              obtain ⟨handlerId, handlerVar, handlerProgram⟩ := hkn
                              by_cases heq : eid = handlerId
                              · cases hshapeSome : state.eshapes.lookup eid with
                                | none =>
                                    rw [evaluateHOLFiniteState_call_exception_missing_shape state
                                      returns handlerId handlerVar handlerProgram function arguments
                                      values body callee returnShape eid value postState hargs
                                      hlookup hclock hbody heq hshapeSome]
                                    simp only [hlookup, if_neg hclock, hbody, if_pos heq,
                                      hshapeSome]
                                | some declaredShape =>
                                    by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                        isValidValueHOLExact state.toExact VarKind.local handlerVar value) = true
                                    · have hshapeEq := (Bool.and_eq_true_iff.mp hcond).1
                                      have hvalid := (Bool.and_eq_true_iff.mp hcond).2
                                      have hbodyId : evaluateHOLFiniteState
                                          (callEntryStateHOLFinite state callee) body =
                                          (some (.exception handlerId value), postState) := by
                                        rw [← heq]
                                        exact hbody
                                      have hshapeSomeId : state.eshapes.lookup handlerId = some declaredShape := by
                                        rw [← heq]
                                        exact hshapeSome
                                      rw [evaluateHOLFiniteState_call_matched_exception_handler
                                        state returns handlerId handlerVar function handlerProgram
                                        body arguments values callee returnShape value postState
                                        declaredShape hargs hlookup hclock hbodyId hshapeSomeId hshapeEq
                                        hvalid]
                                      simp only [hlookup, if_neg hclock, hbody, if_pos heq,
                                        hshapeSome, if_pos hcond]
                                    · have hcondFalse : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                          isValidValueHOLExact state.toExact VarKind.local handlerVar value) = false := by
                                        cases h : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                            isValidValueHOLExact state.toExact VarKind.local handlerVar value) <;>
                                          simp_all
                                      rw [evaluateHOLFiniteState_call_exception_invalid state
                                        returns handlerId handlerVar handlerProgram declaredShape
                                        function arguments values body callee returnShape eid value
                                        postState hargs hlookup hclock hbody heq hshapeSome
                                        hcondFalse]
                                      simp only [hlookup, if_neg hclock, hbody, if_pos heq,
                                        hshapeSome, if_neg hcond]
                              · rw [evaluateHOLFiniteState_call_exception_mismatch state returns
                                  handlerId handlerVar handlerProgram function arguments values body
                                  callee returnShape eid value postState hargs hlookup hclock hbody
                                  heq]
                                simp only [hlookup, if_neg hclock, hbody, if_neg heq]

/-
Re-export of the canonical finite-map translation witness
 for the owning
    carrier `PanSemStateFiniteExact` (declared in `StateExactFiniteMap.lean`), so
    that this module's `fmap_as_finite_support`-qualified `@[hol]` declarations
    carry the same-module checked witness the reference checker requires. The
    statement is the `toExact`/`ofExact` roundtrip between the finite carrier and
    its broad counterpart. Declared under a fresh local namespace to avoid a
    clash with the imported witness of the same name. -/
namespace PanSem.EvaluateClockWitness

theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanSem.EvaluateClockWitness

namespace PanSemStateFiniteExact

/-- HOL `evaluate_def` line-780 `DecCall` conjunct, restated by
    `REWRITE_RULE [fix_clock_evaluate]` from the original line-556 definition.
    The only semantic change in the displayed right-hand side is that the
    fixed callee-body pair is replaced with the raw total evaluator pair, as
    justified by `fixClockHOLFinite_evaluateState`. Every branch still follows
    the source order: argument evaluation, code lookup, clock timeout, callee
    result dispatch, both return-shape tests, continuation evaluation, and
    caller-local restoration. No branch selector or evaluator-result
    hypothesis is added. The rewrite's output equality is exactly
    `fixClockHOLFinite_evaluateState entry body`; it is applied to the full
    recursive pair before matching its result, so result and post-state remain
    equal branch by branch. The original output rows
    `deccall_code_map_clock_9` and `deccall_restores_existing_local` are
    recorded in `scripts/hol-probes/pan_sem_e2e_probe.out` and checked by the
    direct Lean regressions in `Flapjack/Test/PanSemTotalEvalExactParity.lean`.
    The four finite-map fields and positive word width use the same reviewed
    carriers as the line-556 sibling. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_decCall_fixClockRewrite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (match evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
       | none => (some .error, state)
       | some values =>
           match lookupCodeHOLFinite state.code.lookup function values with
           | none => (some .error, state)
           | some (body, callee, returnShape) =>
               if state.clock = 0 then
                 (some .timeOut, emptyLocalsHOLFinite state)
               else
                 let entry := callEntryStateHOLFinite state callee
                 let bodyOutput := evaluateHOLFiniteState entry body
                 match bodyOutput.1 with
                 | none => (some .error, bodyOutput.2)
                 | some .break => (some .error, bodyOutput.2)
                 | some .continue => (some .error, bodyOutput.2)
                 | some (.returned value) =>
                     if shapeEqHOL (shapeOfHOLExact value) shape &&
                         shapeEqHOL (shapeOfHOLExact value) returnShape then
                       let continuationState :=
                         setVarHOLFinite resultName value
                           { bodyOutput.2 with locals := state.locals }
                       let continuationOutput :=
                         evaluateHOLFiniteState continuationState continuation
                       (continuationOutput.1,
                         { continuationOutput.2 with
                           locals := HolFiniteMapExact.resVarEq
                             continuationOutput.2.locals
                             (resultName, state.locals.lookup resultName) })
                     else (some .error, bodyOutput.2)
                 | some other => (some other, emptyLocalsHOLFinite bodyOutput.2)) := by
  classical
  have hbodyFix (entry : PanSemStateFiniteExact width σ) (body : ProgHOL width) :
      fixClockHOLFinite entry (evaluateHOLFiniteState entry body) =
        evaluateHOLFiniteState entry body :=
    Flapjack.fixClockHOLFinite_evaluateState entry body
  rw [evaluateHOLFiniteState_decCall_total]
  simp only [hbodyFix]
  rfl

end PanSemStateFiniteExact

/-! ## Line-780 `evaluate_def` rewrite (fix_clock eliminated) over the finite evaluator

HOL restates the clause equations at `panSemScript.sml:780` as
`Theorem evaluate_def[allow_rebind,compute] = REWRITE_RULE [fix_clock_evaluate] evaluate_def`,
which removes the explicit `fix_clock` wrapper introduced by the source
`Definition evaluate_def` at line 556. This section ports the `Seq` conjunct of
that line-780 restatement over the pair-shaped finite evaluator: the finite
`fix_clock` lemma `fixClockHOLFinite_evaluateState` rewrites the clamped first
pair back to the raw evaluated pair. It is tagged to line 780 and is distinct
from the line-556 tagged `evaluateHOLFiniteState_seq`. -/

/-- HOL `evaluate_def` line-780 `Seq` conjunct (fix_clock-free restatement) over
    the pair-shaped finite source evaluator: evaluate the first program to a raw
    result-option × state pair, and recurse on the second only when the first
    result is `NONE`; otherwise return that raw pair. This is the source
    `Definition evaluate_def` (line 556) `Seq` clause with its explicit
    `fix_clock` rewritten away by line 780's `REWRITE_RULE [fix_clock_evaluate]`,
    via the finite `fixClockHOLFinite_evaluateState`. No extra premise. The
    carrier/qualifier situation equals the line-556 tagged sibling; the full
    21-clause assembly is `evaluateHOLFiniteState_eq_evaluate_def`
    (bead `flapjack-qj5.9.6`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_seq_line780 {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (first second : ProgHOL width) :
    evaluateHOLFiniteState state (.seq first second : ProgHOL width) =
      (let firstOutput := evaluateHOLFiniteState state first
       match firstOutput.1 with
       | none => evaluateHOLFiniteState firstOutput.2 second
       | some _ => firstOutput) := by
  classical
  rw [evaluateHOLFiniteState_seq state first second]
  simp only [fixClockHOLFinite_evaluateState state first]
  rfl

/- Exact port of HOL `evaluate_def`
`cakeml/pancake/semantics/panSemScript.sml:780`
(`Theorem evaluate_def[allow_rebind,compute] =
 REWRITE_RULE [fix_clock_evaluate] evaluate_def`):
the single HOL-shaped `match program with` equation over all 21 `ProgHOL`
constructors, with each arm copied from the corresponding line-780 clause
equation. The `DecCall` arm is the fix-clock-free line-780 form
`evaluateHOLFiniteState_decCall_fixClockRewrite`; the integer-return arm uses
`evaluateHOLFiniteState_dec_total`, and `Seq`/`While` use their line-780
restatements, so no arm retains the line-556 `fix_clock` wrapper that line 780
rewrites away. No extra premise and no result hypothesis is added. The four
finite-map fields and the positive word width use the same reviewed carriers as
the tagged clause siblings. -/
set_option maxHeartbeats 4000000 in
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_eq_evaluate_def {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width) :
    evaluateHOLFiniteState state program =
      match program with
    | .skip => (none, state)
    | .dec name shape initializer body =>
      (let context : FiniteEvalContext width σ :=
        ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
          fun address => Classical.propDecidable (state.shMemaddrs address)⟩
       match @evalHOLExact width σ _ state.toExact context.memaddrsDecidable initializer with
       | none => (some .error, state)
       | some value =>
           if shapeEqHOL shape (shapeOfHOLExact value) then
             let bodyState := setVarHOLFinite name value state
             let bodyOutput := evaluateHOLFiniteState bodyState body
             (bodyOutput.1,
               { bodyOutput.2 with
                 locals := HolFiniteMapExact.resVarEq bodyOutput.2.locals
                   (name, state.locals.lookup name) })
           else (some .error, state))
    | .assign kind name source => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) source with
      | none => (some .error, state)
      | some value =>
          if isValidValueHOLFinite state kind name value then
            (none, setKvarHOLFinite kind name value state)
          else (some .error, state)
    | .primitive name operator arguments => match @evalListHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
      | none => (some .error, state)
      | some values =>
          match panPrimopHOLExact operator values with
          | none => (some .error, state)
          | some value =>
              if isValidValueHOLFinite state .local name value then
                (none, setVarHOLFinite name value state)
              else (some .error, state)
    | .store destination source => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some value =>
              match @panMemStoresHOL width _ address (flattenHOL value) state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address)) state.memory with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | none => (some .error, state)
      | _ => (some .error, state)
    | .store32 destination source => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some (.val (.word value)) =>
              match @panMemStore32HOL width _ state.memory state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address))
                  state.be address (BitVec.ofNat 32 value.toNat) with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state)
      | _ => (some .error, state)
    | .storeByte destination source => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some (.val (.word value)) =>
              match @panMemStoreByteWord8HOL width _ state.memory state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address))
                  state.be address (BitVec.ofNat 8 value.toNat) with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state)
      | _ => (some .error, state)
    | .seq first second =>
      (let firstOutput := evaluateHOLFiniteState state first
       match firstOutput.1 with
       | none => evaluateHOLFiniteState firstOutput.2 second
       | some _ => firstOutput)
    | .ite condition thenBranch elseBranch => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition with
      | some (.val (.word word)) =>
          if word = 0 then evaluateHOLFiniteState state elseBranch
          else evaluateHOLFiniteState state thenBranch
      | _ => (some .error, state)
    | .while condition body => (match @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) condition with
       | some (.val (.word word)) =>
           if word ≠ 0 then
             if state.clock = 0 then (some .timeOut, emptyLocalsHOLFinite state)
             else
               let bodyOutput :=
                 evaluateHOLFiniteState (decClockHOLFinite state) body
               match bodyOutput.1 with
               | none => evaluateHOLFiniteState bodyOutput.2 (.while condition body)
               | some .continue => evaluateHOLFiniteState bodyOutput.2 (.while condition body)
               | some .break => (none, bodyOutput.2)
               | some result => (some result, bodyOutput.2)
           else (none, state)
       | _ => (some .error, state))
    | .break => (some .break, state)
    | .continue => (some .continue, state)
    | .call info function arguments => (match evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
       | none => (some .error, state)
       | some values =>
           match lookupCodeHOLFinite state.code.lookup function values with
           | none => (some .error, state)
           | some (body, callee, returnShape) =>
               if state.clock = 0 then
                 (some .timeOut, emptyLocalsHOLFinite state)
               else
                 match evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
                 | (none, st) => (some .error, st)
                 | (some .break, st) => (some .error, st)
                 | (some .continue, st) => (some .error, st)
                 | (some (.returned value), st) =>
                     if shapeEqHOL (shapeOfHOLExact value) returnShape then
                       (match info with
                        | none => (some (.returned value), emptyLocalsHOLFinite st)
                        | some (none, _) => (none, { st with locals := state.locals })
                        | some (some (kind, name), _) =>
                            if isValidValueHOLExact state.toExact kind name value then
                              (none, setKvarHOLFinite kind name value
                                { st with locals := state.locals })
                            else (some .error, st))
                     else (some .error, st)
                 | (some (.exception exceptionId value), st) =>
                     (match info with
                      | none =>
                          (some (.exception exceptionId value), emptyLocalsHOLFinite st)
                      | some (_, none) =>
                          (some (.exception exceptionId value), emptyLocalsHOLFinite st)
                      | some (_, some (handlerId, handlerVar, handlerProgram)) =>
                          if exceptionId = handlerId then
                            (match state.eshapes.lookup exceptionId with
                             | some shape =>
                                 if shapeEqHOL (shapeOfHOLExact value) shape &&
                                     isValidValueHOLExact state.toExact .local handlerVar value
                                 then
                                   evaluateHOLFiniteState
                                     (setVarHOLFinite handlerVar value
                                       { st with locals := state.locals }) handlerProgram
                                 else (some .error, st)
                             | none => (some .error, st))
                          else (some (.exception exceptionId value),
                            emptyLocalsHOLFinite st))
                 | (some other, st) => (some other, emptyLocalsHOLFinite st))
    | .decCall resultName shape function arguments continuation => (match evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
       | none => (some .error, state)
       | some values =>
           match lookupCodeHOLFinite state.code.lookup function values with
           | none => (some .error, state)
           | some (body, callee, returnShape) =>
               if state.clock = 0 then
                 (some .timeOut, emptyLocalsHOLFinite state)
               else
                  let entry := callEntryStateHOLFinite state callee
                  let bodyOutput := evaluateHOLFiniteState entry body
                  match bodyOutput.1 with
                  | none => (some .error, bodyOutput.2)
                  | some .break => (some .error, bodyOutput.2)
                  | some .continue => (some .error, bodyOutput.2)
                  | some (.returned value) =>
                      if shapeEqHOL (shapeOfHOLExact value) shape &&
                          shapeEqHOL (shapeOfHOLExact value) returnShape then
                        let continuationState :=
                          setVarHOLFinite resultName value
                            { bodyOutput.2 with locals := state.locals }
                        let continuationOutput :=
                          evaluateHOLFiniteState continuationState continuation
                        (continuationOutput.1,
                          { continuationOutput.2 with
                            locals := HolFiniteMapExact.resVarEq
                              continuationOutput.2.locals
                              (resultName, state.locals.lookup resultName) })
                      else (some .error, bodyOutput.2)
                  | some other => (some other, emptyLocalsHOLFinite bodyOutput.2))
    | .extCall function configuration configurationLength array arrayLength => match
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configuration,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configurationLength,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) array,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) arrayLength with
      | some (.val (.word address1)), some (.val (.word length1)),
        some (.val (.word address2)), some (.val (.word length2)) =>
          match
            readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be),
            readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be) with
          | some bytes1, some bytes2 =>
              match callFFIHOL state.ffi (.extCall function) bytes1 bytes2 with
              | .final event =>
                  (some (.finalFfi event), emptyLocalsHOLFinite state)
              | .ret newFfi newBytes =>
                  let nextState : PanSemStateExact width σ :=
                    { state.toExact with
                      memory := @panWriteBytearrayWord8HOL width _ address2 newBytes
                        state.memory state.memaddrs
                        (fun address => Classical.propDecidable (state.memaddrs address))
                        state.be
                      ffi := newFfi }
                  (none, PanSemStateFiniteExact.ofExact nextState (by
                    change nextState.FiniteSupport
                    simpa [nextState, PanSemStateExact.FiniteSupport] using
                      state.toExact_finiteSupport))
          | _, _ => (some .error, state)
      | _, _, _, _ => (some .error, state)
    | .raise exceptionId expression => match state.eshapes.lookup exceptionId,
          @evalHOLExact width σ _ state.toExact
            (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | some shape, some value =>
          let condition : Prop := shapeOfHOLExact value = shape ∧
            Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32
          letI : Decidable condition := Classical.propDecidable condition
          if condition then
            (some (.exception exceptionId value), emptyLocalsHOLFinite state)
          else (some .error, state)
      | _, _ => (some .error, state)
    | .return expression => match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | none => (some .error, state)
      | some value =>
          if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32 then
            (some (.returned value), emptyLocalsHOLFinite state)
          else (some .error, state)
    | .shMemLoad operator kind name address => match @evalHOLFinite width σ _ state
          (fun current => Classical.propDecidable (state.memaddrs current)) address with
      | some (.val (.word addr)) =>
          match lookupKvarHOLFinite kind name state with
          | some (.val (.word _)) =>
              let loaded := @shMemLoadHOLFiniteExact width σ _ state
                (fun current => Classical.propDecidable (state.shMemaddrs current))
                kind name addr (nbOpHOL operator)
              (loaded.1, loaded.2)
          | _ => (some .error, state)
      | _ => (some .error, state)
    | .shMemStore operator address value =>
      (let hshmem : DecidablePred state.shMemaddrs :=
        fun key => Classical.propDecidable (state.shMemaddrs key)
       let evalAddress := @evalHOLExact width σ _ state.toExact
         (fun key => Classical.propDecidable (state.memaddrs key)) address
       let evalValue := @evalHOLExact width σ _ state.toExact
         (fun key => Classical.propDecidable (state.memaddrs key)) value
       match evalAddress, evalValue with
       | some (.val (.word addr)), some (.val (.word bytes)) =>
           let output := shMemStoreHOLExact state.toExact bytes addr (nbOpHOL operator)
           (output.1, ofExact output.2
             (@shMemStoreHOLExact_finiteSupport width σ _ state.toExact hshmem
               bytes addr (nbOpHOL operator) state.toExact_finiteSupport))
       | _, _ => (some .error, state))
    | .tick => (if state.clock = 0 then (some .timeOut, emptyLocalsHOLFinite state)
       else (none, decClockHOLFinite state))
    | .annot _tag _text => (none, state) := by
  cases program <;> (first | rw [evaluateHOLFiniteState_skip] | rw [evaluateHOLFiniteState_dec_total] | rw [evaluateHOLFiniteState_assign] | rw [evaluateHOLFiniteState_primitive] | rw [evaluateHOLFiniteState_store] | rw [evaluateHOLFiniteState_store32] | rw [evaluateHOLFiniteState_storeByte] | rw [evaluateHOLFiniteState_seq_line780] | rw [evaluateHOLFiniteState_ite] | rw [evaluateHOLFiniteState_while_fixClockRewrite] | rw [evaluateHOLFiniteState_break] | rw [evaluateHOLFiniteState_continue] | rw [evaluateHOLFiniteState_call] | rw [evaluateHOLFiniteState_decCall_fixClockRewrite] | rw [evaluateHOLFiniteState_extCall_source] | rw [evaluateHOLFiniteState_raise] | rw [evaluateHOLFiniteState_return] | rw [evaluateHOLFiniteState_shMemLoad_source] | rw [evaluateHOLFiniteState_shMemStore_total] | rw [evaluateHOLFiniteState_tick] | rw [evaluateHOLFiniteState_annot]) <;> try (dsimp only; rfl)

/-! ## FFI event-prefix monotonicity (HOL `panPropsScript.sml:856`)

Exact port of HOL `Theorem evaluate_io_events_mono`
(`!exps s1 res s2. evaluate (exps,s1) = (res,s2) ==> s1.ffi.io_events ≼ s2.ffi.io_events`)
over the pair-shaped finite evaluator `evaluateHOLFiniteState`, i.e. the tagged
21-clause `evaluate_def` port, with HOL's quantifiers and successful-evaluate
hypothesis. HOL's `IS_PREFIX` (`≼`) is Lean `List.IsPrefix` (`<+:`). The proof
projects the finite run to the exact recursive evaluator through
`evalPanSemRecursiveCallFiniteContext_projection` and applies the Flapjack
event-prefix lemma `evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix`
(which itself mirrors HOL's `recInduct evaluate_ind` + `IS_PREFIX_TRANS`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_ioEvents_mono {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (finalState : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state program = (result, finalState)) :
    state.ffi.ioEvents <+: finalState.ffi.ioEvents := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  obtain ⟨pair, hpair⟩ := evalPanSemRecursiveCallFiniteContext_total program context
  rw [evaluateHOLFiniteState_eq_recursiveContext] at heval
  rw [show (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context from rfl] at heval
  simp only [hpair, Prod.mk.injEq] at heval
  obtain ⟨hres, hst⟩ := heval
  have hproj := evalPanSemRecursiveCallFiniteContext_projection program context
  rw [hpair] at hproj
  simp only [Option.map_some] at hproj
  have hpref := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix program context.toExact
    (pair.1, pair.2.toExact) hproj.symm
  subst hres
  subst hst
  simpa only [context, FiniteEvalContext.toExact, PanSemStateFiniteExact.toExact] using hpref

end Flapjack
