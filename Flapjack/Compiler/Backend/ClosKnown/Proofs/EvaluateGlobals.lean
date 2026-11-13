module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InstallGlobals
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ClosureGlobals
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.PrimitiveGlobals
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean

@[expose] public section


/-! Global-write safety during closure evaluation. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL
open FlatProps (emptyGlobalBag)

namespace EvaluateGlobalsPort
/-- The closure evaluator uses the canonical finite-map state representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Empty expression evaluation preserves the source global invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsNil {C F : Type} (env : List ClosSem.Value)
    (s0 : ClosSem.State C F) (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([] : List ClosLang.Exp), esgcFree e) ∧ (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, _, _⟩
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩

/-- Applying a safe closure to no arguments preserves the source invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppChangedGlobalsNil {C F : Type} (location : Option Nat) (f : ClosSem.Value)
    (s0 : ClosSem.State C F) (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluateApp location f [] s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
      (∀ v ∈ ([] : List ClosSem.Value), vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals := by
  rcases h with ⟨run, safe, fnSafe, _⟩
  simp [evaluateApp] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨safe, by simpa [rsgcFree] using fnSafe, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩


/-- Variable evaluation preserves the source global invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsVar {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.var trace index] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.var trace index] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.var trace index] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, _, envSafe⟩
  cases found : env[index]? with
  | none =>
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
  | some value =>
    have valueSafe := envSafe value (List.mem_of_getElem? found)
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simpa [rsgcFree] using valueSafe, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩


/-- The source evaluator global-safety assertion for a fixed expression list.
This is Lean induction infrastructure, with no separate HOL declaration. -/
def EvalGlobalsInvariant {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F) : Prop :=
  ∀ (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F),
    evaluate expressions env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ expressions, esgcFree e) ∧ (∀ v ∈ env, vsgcFree v) →
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals expressions k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals

/-- Concatenated expression write sets compose by union. -/
private theorem expressionWritesAppend (xs ys : List ClosLang.Exp) :
    {k | elistGlobals (xs ++ ys) k ≠ 0} =
      {k | elistGlobals xs k ≠ 0} ∪ {k | elistGlobals ys k ≠ 0} := by
  ext k
  simp [elistGlobals_append]
  classical
  by_cases h : elistGlobals xs k = 0 <;> simp_all

/-- Sequential evaluation preserves global safety, assuming the source
induction hypotheses for its head and tail evaluations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsCons {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (headIH : EvalGlobalsInvariant [first] env s0)
    (tailIH : ∀ values next, evaluate [first] env s0 = (.val values, next) →
      EvalGlobalsInvariant (second :: rest) env next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate (first :: second :: rest) env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ first :: second :: rest, esgcFree e) ∧ (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals (first :: second :: rest) k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionsSafe, envSafe⟩
  have firstSafe : ∀ e ∈ [first], esgcFree e := by simpa using expressionsSafe first (by simp)
  have restSafe : ∀ e ∈ second :: rest, esgcFree e := by
    intro e member
    exact expressionsSafe e (by simp [member])
  cases headRun : evaluate [first] env s0 with
  | mk headResult headState =>
    have headProp := headIH headResult headState ⟨headRun, safe, firstSafe, envSafe⟩
    rcases headProp with ⟨headSafe, headResultSafe, n, headOracle, headFrame⟩
    have clockBound : headState.clock ≤ s0.clock := by
      simpa [headRun] using evaluate_clock_le [first] env s0
    cases headResult with
    | err error =>
      simp only [evaluate, headRun, fixClock] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨?_, headResultSafe, n, headOracle, ?_⟩
      · exact (ssgcFreeClock headState (fun clock => min s0.clock clock)).2 headSafe
      · apply mglobalsExtendSubset _ _ _ _ ⟨headFrame, ?_⟩
        intro k member
        rcases member with member | member
        · left
          rw [show first :: second :: rest = [first] ++ (second :: rest) by rfl, expressionWritesAppend]
          exact Or.inl member
        · exact Or.inr member
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value first env s0 headState values headRun
      cases tailRun : evaluate (second :: rest) env headState with
      | mk tailResult tailState =>
        have tailProp := tailIH [value] headState headRun tailResult tailState ⟨tailRun, headSafe, restSafe, envSafe⟩
        rcases tailProp with ⟨tailSafe, tailResultSafe, m, tailOracle, tailFrame⟩
        have finalOracle : tailState.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
          simpa only [headOracle, shiftSeqAdd] using tailOracle
        have frame2 : mglobalsExtend headState.globals
            ({k | elistGlobals (second :: rest) k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0})
            tailState.globals := by
          simpa only [headOracle] using tailFrame
        have composed := mglobalsExtendTrans _ _ _ _ _ ⟨headFrame, frame2⟩
        have finalFrame : mglobalsExtend s0.globals
            ({k | elistGlobals (first :: second :: rest) k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0})
            tailState.globals := by
          rw [show first :: second :: rest = [first] ++ (second :: rest) by rfl,
            expressionWritesAppend]
          rw [Nat.add_comm n m, firstNExpsWritesShift]
          simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using composed
        cases tailResult with
        | err error =>
          simp [evaluate, headRun, fixClock, Nat.min_eq_right clockBound, tailRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨tailSafe, tailResultSafe, n + m, finalOracle, finalFrame⟩
        | val tailValues =>
          simp [evaluate, headRun, fixClock, Nat.min_eq_right clockBound, tailRun] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨tailSafe, ?_, n + m, finalOracle, finalFrame⟩
          simpa [rsgcFree] using And.intro (by simpa [rsgcFree] using headResultSafe) (by simpa [rsgcFree] using tailResultSafe)


/-- Raising a safe expression result preserves the source global invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsRaise {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (bodyIH : EvalGlobalsInvariant [body] env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.raise trace body] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.raise trace body] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.raise trace body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionsSafe, envSafe⟩
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    simpa [esgcFree] using expressionsSafe (.raise trace body) (by simp)
  cases bodyRun : evaluate [body] env s0 with
  | mk bodyResult bodyState =>
    have prop := bodyIH bodyResult bodyState ⟨bodyRun, safe, bodySafe, envSafe⟩
    rcases prop with ⟨stateSafe, resultSafe, n, oracle, frame⟩
    have frame' : mglobalsExtend s0.globals
        ({k | elistGlobals [.raise trace body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) bodyState.globals := by
      simpa [elistGlobals, setGlobals] using frame
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨stateSafe, resultSafe, n, oracle, frame'⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value body env s0 bodyState values bodyRun
      simp [evaluate, bodyRun] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨stateSafe, ?_, n, oracle, frame'⟩
      simpa [rsgcFree] using resultSafe

/-- A tick preserves global safety using the body induction hypothesis when
its clock is nonzero. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsTick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (bodyIH : s0.clock ≠ 0 → EvalGlobalsInvariant [body] env (decClock 1 s0))
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.tick trace body] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.tick trace body] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.tick trace body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionsSafe, envSafe⟩
  by_cases zero : s0.clock = 0
  · simp [evaluate, zero] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
  · have bodySafe : ∀ e ∈ [body], esgcFree e := by
      simpa [esgcFree] using expressionsSafe (.tick trace body) (by simp)
    have startSafe := (ssgcFreeDecClock 1 s0).2 safe
    have bodyRun : evaluate [body] env (decClock 1 s0) = (res, s) := by
      simpa [evaluate, zero] using run
    have ⟨stateSafe, resultSafe, n, oracle, frame⟩ :=
      bodyIH zero res s ⟨bodyRun, startSafe, bodySafe, envSafe⟩
    refine ⟨stateSafe, resultSafe, n, ?_, ?_⟩
    · simpa [decClock] using oracle
    · simpa [decClock, elistGlobals, setGlobals] using frame


/-- Selecting values from a safe environment preserves value safety. This
helper has no separate HOL declaration. -/
theorem lookupVarsSafe (indices : List Nat) (env selected : List ClosSem.Value)
    (safe : ∀ v ∈ env, vsgcFree v) (run : lookupVars indices env = some selected) :
    ∀ v ∈ selected, vsgcFree v := by
  induction indices generalizing selected with
  | nil => simp [lookupVars] at run; subst selected; simp
  | cons index rest ih =>
    simp only [lookupVars] at run
    cases found : env[index]? with
    | none => simp [found] at run
    | some value =>
      simp only [found] at run
      cases remaining : lookupVars rest env with
      | none => simp [remaining] at run
      | some values =>
        simp [remaining] at run
        subst selected
        have valueSafe := safe value (List.mem_of_getElem? found)
        have restSafe := ih values remaining
        simpa using And.intro valueSafe restSafe

/-- Creating a closure from a safe environment preserves global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsFn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.fn name location selected arity body] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.fn name location selected arity body] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.fn name location selected arity body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have bodySafe : setGlobals body = emptyGlobalBag := by
    simpa [esgcFree] using expressionSafe (.fn name location selected arity body) (by simp)
  unfold evaluate at run
  repeat' split at run
  all_goals simp_all [rsgcFree]
  · rcases run with ⟨rfl, _⟩
    refine ⟨?_, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
    simpa [vsgcFree] using And.intro bodySafe envSafe
  · split at run <;> simp_all
    · rcases run with ⟨rfl, _⟩
      exact ⟨by simp, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
    · have selectedSafe := lookupVarsSafe _ _ _ envSafe (by assumption)
      rcases run with ⟨rfl, _⟩
      refine ⟨?_, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
      simpa [vsgcFree] using And.intro bodySafe selectedSafe
  · rcases run with ⟨rfl, _⟩
    exact ⟨by simp, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩


/-- A let expression's write set is the union of its bindings and body.
This is Lean proof infrastructure without a separate HOL declaration. -/
private theorem letWrites (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp)
    (body : ClosLang.Exp) :
    {k | elistGlobals [.let trace bindings body] k ≠ 0} =
      {k | elistGlobals bindings k ≠ 0} ∪ {k | elistGlobals [body] k ≠ 0} := by
  ext k
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  classical
  by_cases h : setGlobals body k = 0 <;> simp_all

/-- Let evaluation preserves global safety, assuming the source induction
hypotheses for its bindings and for the body after successful bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsLet {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (s0 : ClosSem.State C F)
    (bindingsIH : EvalGlobalsInvariant bindings env s0)
    (bodyIH : ∀ values next, evaluate bindings env s0 = (.val values, next) →
      EvalGlobalsInvariant [body] (values ++ env) next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.let trace bindings body] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.let trace bindings body] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.let trace bindings body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have safeParts : esgcFreeList bindings ∧ esgcFree body := by
    simpa [esgcFree] using expressionSafe (.let trace bindings body) (by simp)
  have bindingsSafe := (esgcFreeList_iff bindings).1 safeParts.1
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
  cases bindingsRun : evaluate bindings env s0 with
  | mk bindingsResult next =>
    have ⟨nextSafe, bindingsResultSafe, n, nextOracle, bindingsFrame⟩ :=
      bindingsIH bindingsResult next ⟨bindingsRun, safe, bindingsSafe, envSafe⟩
    have clockBound : next.clock ≤ s0.clock := by
      simpa [bindingsRun] using evaluate_clock_le bindings env s0
    cases bindingsResult with
    | err error =>
      simp only [evaluate, bindingsRun, fixClock] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
        bindingsResultSafe, n, nextOracle, ?_⟩
      apply mglobalsExtendSubset _ _ _ _ ⟨bindingsFrame, ?_⟩
      intro k member
      rcases member with member | member
      · left; rw [letWrites]; exact Or.inl member
      · exact Or.inr member
    | val values =>
      have extendedSafe : ∀ v ∈ values ++ env, vsgcFree v := by
        simpa [rsgcFree, List.mem_append, or_imp, forall_and] using And.intro bindingsResultSafe envSafe
      cases bodyRun : evaluate [body] (values ++ env) next with
      | mk bodyResult last =>
        have ⟨lastSafe, bodyResultSafe, m, lastOracle, bodyFrame⟩ :=
          bodyIH values next bindingsRun bodyResult last ⟨bodyRun, nextSafe, bodySafe, extendedSafe⟩
        have finalOracle : last.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
          simpa only [nextOracle, shiftSeqAdd] using lastOracle
        have frame2 : mglobalsExtend next.globals
            ({k | elistGlobals [body] k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0})
            last.globals := by
          simpa only [nextOracle] using bodyFrame
        have composed := mglobalsExtendTrans _ _ _ _ _ ⟨bindingsFrame, frame2⟩
        have finalFrame : mglobalsExtend s0.globals
            ({k | elistGlobals [.let trace bindings body] k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0})
            last.globals := by
          rw [letWrites, Nat.add_comm n m, firstNExpsWritesShift]
          simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using composed
        simp [evaluate, bindingsRun, fixClock, Nat.min_eq_right clockBound, bodyRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨lastSafe, bodyResultSafe, n + m, finalOracle, finalFrame⟩


/-- A handler's write set combines the protected expression and handler.
This is Lean proof infrastructure without a separate HOL declaration. -/
private theorem handleWrites (trace : BackendCommon.Tra) (body handler : ClosLang.Exp) :
    {k | elistGlobals [.handle trace body handler] k ≠ 0} =
      {k | elistGlobals [body] k ≠ 0} ∪ {k | elistGlobals [handler] k ≠ 0} := by
  ext k
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  classical
  by_cases h : setGlobals body k = 0 <;> simp_all

/-- Exception handling preserves global safety under the original body and
conditional handler induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsHandle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (bodyIH : EvalGlobalsInvariant [body] env s0)
    (handlerIH : ∀ value next, evaluate [body] env s0 = (.err (.raise value), next) →
      EvalGlobalsInvariant [handler] (value :: env) next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.handle trace body handler] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.handle trace body handler] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.handle trace body handler] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have safeParts : esgcFree body ∧ esgcFree handler := by
    simpa [esgcFree] using expressionSafe (.handle trace body handler) (by simp)
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.1
  have handlerSafe : ∀ e ∈ [handler], esgcFree e := by simpa using safeParts.2
  cases bodyRun : evaluate [body] env s0 with
  | mk bodyResult next =>
    have ⟨nextSafe, bodyResultSafe, n, nextOracle, bodyFrame⟩ :=
      bodyIH bodyResult next ⟨bodyRun, safe, bodySafe, envSafe⟩
    have clockBound : next.clock ≤ s0.clock := by
      simpa [bodyRun] using evaluate_clock_le [body] env s0
    have enlarged : mglobalsExtend s0.globals
        ({k | elistGlobals [.handle trace body handler] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      apply mglobalsExtendSubset _ _ _ _ ⟨bodyFrame, ?_⟩
      intro k member
      rcases member with member | member
      · left; rw [handleWrites]; exact Or.inl member
      · exact Or.inr member
    cases bodyResult with
    | val values =>
      simp only [evaluate, bodyRun, fixClock] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
        bodyResultSafe, n, nextOracle, enlarged⟩
    | err error =>
      cases error with
      | abort reason =>
        simp only [evaluate, bodyRun, fixClock] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
          bodyResultSafe, n, nextOracle, enlarged⟩
      | raise value =>
        have valueSafe : vsgcFree value := by simpa [rsgcFree] using bodyResultSafe
        have extendedSafe : ∀ v ∈ value :: env, vsgcFree v := by simpa using And.intro valueSafe envSafe
        cases handlerRun : evaluate [handler] (value :: env) next with
        | mk handlerResult last =>
          have ⟨lastSafe, resultSafe, m, lastOracle, handlerFrame⟩ :=
            handlerIH value next bodyRun handlerResult last ⟨handlerRun, nextSafe, handlerSafe, extendedSafe⟩
          have finalOracle : last.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
            simpa only [nextOracle, shiftSeqAdd] using lastOracle
          have frame2 : mglobalsExtend next.globals
              ({k | elistGlobals [handler] k ≠ 0} ∪
               {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0})
              last.globals := by
            simpa only [nextOracle] using handlerFrame
          have composed := mglobalsExtendTrans _ _ _ _ _ ⟨bodyFrame, frame2⟩
          have finalFrame : mglobalsExtend s0.globals
              ({k | elistGlobals [.handle trace body handler] k ≠ 0} ∪
               {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0})
              last.globals := by
            rw [handleWrites, Nat.add_comm n m, firstNExpsWritesShift]
            simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using composed
          simp [evaluate, bodyRun, fixClock, Nat.min_eq_right clockBound, handlerRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨lastSafe, resultSafe, n + m, finalOracle, finalFrame⟩


/-- A conditional may write globals in its condition or either branch.
This is Lean proof infrastructure without a separate HOL declaration. -/
private theorem ifWrites (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp) :
    {k | elistGlobals [.ifThenElse trace condition yes no] k ≠ 0} =
      {k | elistGlobals [condition] k ≠ 0} ∪
      {k | elistGlobals [yes] k ≠ 0} ∪ {k | elistGlobals [no] k ≠ 0} := by
  ext k
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  omega

/-- Conditional evaluation preserves global safety under the original
condition and branch induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsIf {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (conditionIH : EvalGlobalsInvariant [condition] env s0)
    (yesIH : ∀ values next, evaluate [condition] env s0 = (.val values, next) →
      ClosSem.boolValue true = @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values →
      EvalGlobalsInvariant [yes] env next)
    (noIH : ∀ values next, evaluate [condition] env s0 = (.val values, next) →
      ClosSem.boolValue true ≠ @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values →
      ClosSem.boolValue false = @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values →
      EvalGlobalsInvariant [no] env next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.ifThenElse trace condition yes no] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.ifThenElse trace condition yes no] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.ifThenElse trace condition yes no] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have safeParts : esgcFree condition ∧ esgcFree yes ∧ esgcFree no := by
    simpa [esgcFree] using expressionSafe (.ifThenElse trace condition yes no) (by simp)
  have conditionSafe : ∀ e ∈ [condition], esgcFree e := by simpa using safeParts.1
  cases conditionRun : evaluate [condition] env s0 with
  | mk conditionResult next =>
    have ⟨nextSafe, conditionResultSafe, n, nextOracle, conditionFrame⟩ :=
      conditionIH conditionResult next ⟨conditionRun, safe, conditionSafe, envSafe⟩
    have clockBound : next.clock ≤ s0.clock := by
      simpa [conditionRun] using evaluate_clock_le [condition] env s0
    have enlarged : mglobalsExtend s0.globals
        ({k | elistGlobals [.ifThenElse trace condition yes no] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      apply mglobalsExtendSubset _ _ _ _ ⟨conditionFrame, ?_⟩
      intro k member
      rcases member with member | member
      · left; rw [ifWrites]; exact Or.inl (Or.inl member)
      · exact Or.inr member
    have finishBranch (branch : ClosLang.Exp)
        (branchSafe : ∀ e ∈ [branch], esgcFree e)
        (included : {k | elistGlobals [branch] k ≠ 0} ⊆
          {k | elistGlobals [.ifThenElse trace condition yes no] k ≠ 0})
        (branchIH : EvalGlobalsInvariant [branch] env next)
        (branchRun : evaluate [branch] env next = (res, s)) :
        ssgcFree s ∧ rsgcFree res ∧ ∃ total,
          s.compileOracle = Flapjack.holShiftSeq total s0.compileOracle ∧
          mglobalsExtend s0.globals
            ({k | elistGlobals [.ifThenElse trace condition yes no] k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps s0.compileOracle total)) k ≠ 0}) s.globals := by
      have ⟨lastSafe, resultSafe, m, lastOracle, branchFrame⟩ :=
        branchIH res s ⟨branchRun, nextSafe, branchSafe, envSafe⟩
      refine ⟨lastSafe, resultSafe, n + m, ?_, ?_⟩
      · simpa only [nextOracle, shiftSeqAdd] using lastOracle
      · have frame2 : mglobalsExtend next.globals
            ({k | elistGlobals [branch] k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0})
            s.globals := by simpa only [nextOracle] using branchFrame
        have combined := mglobalsExtendTrans _ _ _ _ _ ⟨conditionFrame, frame2⟩
        apply mglobalsExtendSubset _ _ _ _ ⟨combined, ?_⟩
        rw [Nat.add_comm n m, firstNExpsWritesShift]
        intro k member
        rcases member with (member | member) | (member | member)
        · left; rw [ifWrites]; exact Or.inl (Or.inl member)
        · exact Or.inr (Or.inl member)
        · exact Or.inl (included member)
        · exact Or.inr (Or.inr member)
    cases conditionResult with
    | err error =>
      simp only [evaluate, conditionRun, fixClock] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
        conditionResultSafe, n, nextOracle, enlarged⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env s0 next values conditionRun
      cases boolRun : asBool value with
      | none =>
        simp [evaluate, conditionRun, fixClock, boolRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
          by simp [rsgcFree], n, nextOracle, enlarged⟩
      | some flag =>
        cases flag with
        | false =>
          have boolEq : value = ClosSem.boolValue false := (asBool_eq_some value false).1 boolRun
          have notTrue : ClosSem.boolValue true ≠ value := by simp [boolEq, ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
          have selectedIH := noIH [value] next conditionRun (by simpa [Flapjack.holHd] using notTrue) (by simpa [Flapjack.holHd] using boolEq.symm)
          refine finishBranch no (by simpa using safeParts.2.2) ?_ selectedIH ?_
          · intro k member; rw [ifWrites]; exact Or.inr member
          · simpa [evaluate, conditionRun, fixClock, Nat.min_eq_right clockBound, boolRun] using run
        | true =>
          have boolEq : value = ClosSem.boolValue true := (asBool_eq_some value true).1 boolRun
          have selectedIH := yesIH [value] next conditionRun (by simpa [Flapjack.holHd] using boolEq.symm)
          refine finishBranch yes (by simpa using safeParts.2.1) ?_ selectedIH ?_
          · intro k member; rw [ifWrites]; exact Or.inl (Or.inr member)
          · simpa [evaluate, conditionRun, fixClock, Nat.min_eq_right clockBound, boolRun] using run


/-- Recursive closures built from safe captures and bodies are safe. This is
Lean proof infrastructure without a separate HOL declaration. -/
private theorem recursiveClosuresSafe (location : Option Nat) (captures : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (capturesSafe : ∀ v ∈ captures, vsgcFree v)
    (bodiesSafe : funGlobals functions = emptyGlobalBag) :
    ∀ v ∈ (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] captures functions i), vsgcFree v := by
  intro value member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  simpa [vsgcFree, ← funGlobals_eq_elist] using And.intro bodiesSafe capturesSafe

/-- Recursive binding evaluation preserves global safety under the original
conditional body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsLetrec {C F : Type}
    (names : List Flapjack.Basis.Pure.MlString.MlString) (location : Option Nat)
    (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (bodyIH : ∀ (buildRc : List ClosSem.Value → List ClosSem.Value)
      (envdelta : Option (List ClosSem.Value)) (ed : List ClosSem.Value),
      (∀ entry ∈ functions, entry.1 ≤ s0.maxApp ∧ entry.1 ≠ 0) ∧
      buildRc = (fun captures => (List.range functions.length).map
        (fun i => ClosSem.Value.recclosure location [] captures functions i)) ∧
      envdelta = (match selected with
        | none => some (buildRc env)
        | some indices => (lookupVars indices env).map buildRc) ∧
      envdelta = some ed → EvalGlobalsInvariant [body] (ed ++ env) s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.letrec names location selected functions body] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.letrec names location selected functions body] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.letrec names location selected functions body] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have safeParts : funGlobals functions = emptyGlobalBag ∧ esgcFree body := by
    simpa [esgcFree] using expressionSafe (.letrec names location selected functions body) (by simp)
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
  by_cases valid : (functions.all (fun (arity, _) => arity ≤ s0.maxApp && arity != 0)) = true
  · have allValid : ∀ entry ∈ functions, entry.1 ≤ s0.maxApp ∧ entry.1 ≠ 0 := by
      simpa [List.all_eq_true] using valid
    cases selected with
    | none =>
      let buildRc := fun captures => (List.range functions.length).map
        (fun i => ClosSem.Value.recclosure location [] captures functions i)
      have recSafe := recursiveClosuresSafe location env functions envSafe safeParts.1
      have extendedSafe : ∀ v ∈ buildRc env ++ env, vsgcFree v := by
        simpa [buildRc, List.mem_append, or_imp, forall_and] using And.intro recSafe envSafe
      have ih := bodyIH buildRc (some (buildRc env)) (buildRc env) ⟨allValid, rfl, rfl, rfl⟩
      have bodyRun : evaluate [body] (buildRc env ++ env) s0 = (res, s) := by
        simpa [evaluate, valid, buildRc] using run
      have ⟨lastSafe, resultSafe, n, oracle, frame⟩ := ih res s ⟨bodyRun, safe, bodySafe, extendedSafe⟩
      refine ⟨lastSafe, resultSafe, n, oracle, ?_⟩
      simpa [elistGlobals, setGlobals, safeParts.1, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using frame
    | some indices =>
      cases selectedRun : lookupVars indices env with
      | none =>
        simp [evaluate, valid, selectedRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
      | some captures =>
        let buildRc := fun captures => (List.range functions.length).map
          (fun i => ClosSem.Value.recclosure location [] captures functions i)
        have capturesSafe := lookupVarsSafe indices env captures envSafe selectedRun
        have recSafe := recursiveClosuresSafe location captures functions capturesSafe safeParts.1
        have extendedSafe : ∀ v ∈ buildRc captures ++ env, vsgcFree v := by
          simpa [buildRc, List.mem_append, or_imp, forall_and] using And.intro recSafe envSafe
        have ih := bodyIH buildRc (some (buildRc captures)) (buildRc captures)
          ⟨allValid, rfl, by simp [selectedRun], rfl⟩
        have bodyRun : evaluate [body] (buildRc captures ++ env) s0 = (res, s) := by
          simpa [evaluate, valid, selectedRun, buildRc] using run
        have ⟨lastSafe, resultSafe, n, oracle, frame⟩ := ih res s ⟨bodyRun, safe, bodySafe, extendedSafe⟩
        refine ⟨lastSafe, resultSafe, n, oracle, ?_⟩
        simpa [elistGlobals, setGlobals, safeParts.1, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using frame
  · cases selected <;> simp [evaluate, valid] at run <;>
      rcases run with ⟨rfl, rfl⟩ <;>
      exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩


/-- A successful code lookup returns the original arguments and a body with
no global writes in a safe state. This helper has no separate HOL declaration. -/
private theorem findCodeSafe {C F : Type} (location : Nat) (args selected : List ClosSem.Value)
    (body : ClosLang.Exp) (state : ClosSem.State C F) (safe : ssgcFree state)
    (found : findCode location args state.code = some (selected, body)) :
    selected = args ∧ setGlobals body = emptyGlobalBag := by
  change (state.code.lookup location).bind
    (fun entry => if args.length = entry.1 then some (args, entry.2) else none) = some (selected, body) at found
  simp only [Option.bind_eq_some_iff] at found
  rcases found with ⟨⟨arity, codeBody⟩, lookup, found⟩
  split at found <;> simp_all
  exact safe.1 _ _ _ lookup


/-- Direct calls preserve global safety under the source argument and
conditional code-body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsCall {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (s0 : ClosSem.State C F) (argsIH : EvalGlobalsInvariant args env s0)
    (bodyIH : ∀ values next callArgs body,
      evaluate args env s0 = (.val values, next) →
      findCode location values next.code = some (callArgs, body) →
      ¬ next.clock < ticks + 1 → EvalGlobalsInvariant [body] callArgs (decClock (ticks + 1) next))
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.call trace ticks location args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.call trace ticks location args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.call trace ticks location args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have argsSafe : ∀ e ∈ args, esgcFree e := by
    apply (esgcFreeList_iff args).1
    simpa [esgcFree] using expressionSafe (.call trace ticks location args) (by simp)
  cases argsRun : evaluate args env s0 with
  | mk argsResult next =>
    have ⟨nextSafe, argsResultSafe, n, nextOracle, argsFrame⟩ :=
      argsIH argsResult next ⟨argsRun, safe, argsSafe, envSafe⟩
    have clockBound : next.clock ≤ s0.clock := by
      simpa [argsRun] using evaluate_clock_le args env s0
    have frame : mglobalsExtend s0.globals
        ({k | elistGlobals [.call trace ticks location args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      simpa [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using argsFrame
    cases argsResult with
    | err error =>
      simp only [evaluate, argsRun, fixClock] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
        argsResultSafe, n, nextOracle, frame⟩
    | val values =>
      cases codeRun : findCode location values next.code with
      | none =>
        simp [evaluate, argsRun, fixClock, Nat.min_eq_right clockBound, codeRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨nextSafe, by simp [rsgcFree], n, nextOracle, frame⟩
      | some pair =>
        rcases pair with ⟨callArgs, body⟩
        have ⟨sameArgs, noWrites⟩ := findCodeSafe location values callArgs body next nextSafe codeRun
        have callArgsSafe : ∀ v ∈ callArgs, vsgcFree v := by
          subst callArgs
          simpa [rsgcFree] using argsResultSafe
        have bodySafe : ∀ e ∈ [body], esgcFree e := by
          simpa using setGlobalsEmptyEsgcFree body noWrites
        by_cases timeout : next.clock < ticks + 1
        · simp [evaluate, argsRun, fixClock, Nat.min_eq_right clockBound, codeRun, timeout] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨(ssgcFreeClock next (fun _ => 0)).2 nextSafe,
            by simp [rsgcFree], n, nextOracle, frame⟩
        · cases bodyRun : evaluate [body] callArgs (decClock (ticks + 1) next) with
          | mk bodyResult last =>
            have startSafe := (ssgcFreeDecClock (ticks + 1) next).2 nextSafe
            have ⟨lastSafe, resultSafe, m, lastOracle, bodyFrame⟩ :=
              bodyIH values next callArgs body argsRun codeRun timeout bodyResult last
                ⟨bodyRun, startSafe, bodySafe, callArgsSafe⟩
            have finalOracle : last.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
              simpa only [decClock, nextOracle, shiftSeqAdd] using lastOracle
            have frame2 : mglobalsExtend next.globals
                {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0}
                last.globals := by
              simpa [decClock, nextOracle, elistGlobals, noWrites, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using bodyFrame
            have composed := mglobalsExtendTrans _ _ _ _ _ ⟨argsFrame, frame2⟩
            have finalFrame : mglobalsExtend s0.globals
                ({k | elistGlobals [.call trace ticks location args] k ≠ 0} ∪
                 {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0}) last.globals := by
              rw [Nat.add_comm n m, firstNExpsWritesShift]
              simpa [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag,
                Set.union_assoc, Flapjack.bagUnion, Flapjack.emptyBag] using composed
            simp [evaluate, argsRun, fixClock, Nat.min_eq_right clockBound, codeRun, timeout, bodyRun] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨lastSafe, resultSafe, n + m, finalOracle, finalFrame⟩


/-- The source global-safety assertion for a fixed closure application.
This is Lean induction infrastructure, with no separate HOL declaration. -/
def EvalAppGlobalsInvariant {C F : Type} (location : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : ClosSem.State C F) : Prop :=
  ∀ (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F),
    evaluateApp location f args s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
      (∀ v ∈ args, vsgcFree v) →
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals

/-- Applying a closure to a nonempty argument list preserves global safety
under the original conditional body and subsequent-application hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppChangedGlobalsCons {C F : Type} (location : Option Nat)
    (f first : ClosSem.Value) (args : List ClosSem.Value) (s0 : ClosSem.State C F)
    (bodyIH : ∀ body env rest,
      destClosure s0.maxApp location f (first :: args) = some (.fullApp body env rest) →
      ¬ s0.clock < (first :: args).length - rest.length →
      EvalGlobalsInvariant [body] env (decClock ((first :: args).length - rest.length) s0))
    (appIH : ∀ body env rest value next,
      destClosure s0.maxApp location f (first :: args) = some (.fullApp body env rest) →
      ¬ s0.clock < (first :: args).length - rest.length →
      evaluate [body] env (decClock ((first :: args).length - rest.length) s0) = (.val [value], next) →
      EvalAppGlobalsInvariant location value rest next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluateApp location f (first :: args) s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
      (∀ v ∈ first :: args, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals := by
  rcases h with ⟨run, safe, fnSafe, argsSafe⟩
  rw [evaluateApp] at run
  cases closureRun : destClosure s0.maxApp location f (first :: args) with
  | none =>
    rw [closureRun] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
  | some kind =>
    rw [closureRun] at run
    dsimp only at run
    cases kind with
    | partialApp value =>
      dsimp only at run
      have valueSafe := destClosurePartialSafe _ _ _ _ _ fnSafe argsSafe closureRun
      by_cases timeout : s0.clock < (first :: args).length
      · rw [ite_eq_left timeout] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeClock s0 (fun _ => 0)).2 safe,
          by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
      · rw [ite_eq_right timeout] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeDecClock (first :: args).length s0).2 safe,
          by simpa [rsgcFree] using valueSafe, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
    | fullApp body env rest =>
      dsimp only at run
      by_cases timeout : s0.clock < (first :: args).length - rest.length
      · rw [ite_eq_left timeout] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeClock s0 (fun _ => 0)).2 safe,
          by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
      · rw [ite_eq_right timeout, fixClock_evaluate] at run
        have ⟨noWrites, envSafe, restSafe⟩ :=
          destClosureFullSgcFree _ _ _ _ _ _ _ _ ⟨closureRun, fnSafe, argsSafe first (by simp),
            by intro v member; exact argsSafe v (by simp [member])⟩
        have bodySafe : ∀ e ∈ [body], esgcFree e := by
          simpa using setGlobalsEmptyEsgcFree body noWrites
        let start := decClock ((first :: args).length - rest.length) s0
        have startSafe : ssgcFree start := (ssgcFreeDecClock _ s0).2 safe
        cases bodyRun : evaluate [body] env start with
        | mk bodyResult next =>
          have ⟨nextSafe, bodyResultSafe, n, nextOracle, bodyFrame⟩ :=
            bodyIH body env rest closureRun timeout bodyResult next ⟨bodyRun, startSafe, bodySafe, envSafe⟩
          have frame : mglobalsExtend s0.globals
              {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} next.globals := by
            simpa [start, decClock, elistGlobals, noWrites, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using bodyFrame
          have nextOracle' : next.compileOracle = Flapjack.holShiftSeq n s0.compileOracle := by
            simpa [start, decClock] using nextOracle
          cases bodyResult with
          | err error =>
            dsimp only [start] at bodyRun
            rw [bodyRun] at run
            simp only at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨nextSafe, bodyResultSafe, n, nextOracle', frame⟩
          | val values =>
            obtain ⟨value, rfl⟩ := evaluate_singleton_value body env start next values bodyRun
            have valueSafe : vsgcFree value := by simpa [rsgcFree] using bodyResultSafe
            cases appRun : evaluateApp location value rest next with
            | mk appResult last =>
              have ⟨lastSafe, resultSafe, m, lastOracle, appFrame⟩ :=
                appIH body env rest value next closureRun timeout bodyRun appResult last
                  ⟨appRun, nextSafe, valueSafe, restSafe⟩
              have finalOracle : last.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
                simpa only [nextOracle', shiftSeqAdd] using lastOracle
              have frame2 : mglobalsExtend next.globals
                  {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0}
                  last.globals := by simpa only [nextOracle'] using appFrame
              have finalFrame := mglobalsExtendTrans _ _ _ _ _ ⟨frame, frame2⟩
              have composed : mglobalsExtend s0.globals
                  {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0} last.globals := by
                rw [Nat.add_comm n m, firstNExpsWritesShift]
                exact finalFrame
              dsimp only [start] at bodyRun
              rw [bodyRun] at run
              simp only at run
              rw [appRun] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨lastSafe, resultSafe, n + m, finalOracle, composed⟩


/-- Combining successive global frames also combines their oracle prefixes.
This helper has no separate HOL declaration. -/
private theorem combineOracleFrames {C F : Type} (s0 middle last : ClosSem.State C F)
    (a b : Set Nat) (n m : Nat)
    (oracle : middle.compileOracle = Flapjack.holShiftSeq n s0.compileOracle)
    (first : mglobalsExtend s0.globals
      (a ∪ {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) middle.globals)
    (second : mglobalsExtend middle.globals
      (b ∪ {k | elistGlobals (List.flatten (firstNExps middle.compileOracle m)) k ≠ 0}) last.globals) :
    mglobalsExtend s0.globals ((a ∪ b) ∪
      {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0}) last.globals := by
  have second' : mglobalsExtend middle.globals
      (b ∪ {k | elistGlobals (List.flatten (firstNExps (Flapjack.holShiftSeq n s0.compileOracle) m)) k ≠ 0}) last.globals := by
    simpa only [oracle] using second
  have combined := mglobalsExtendTrans _ _ _ _ _ ⟨first, second'⟩
  rw [Nat.add_comm n m, firstNExpsWritesShift]
  simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using combined

/-- An application writes only through its argument expressions and function
expression. This helper has no separate HOL declaration. -/
private theorem appWrites (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) :
    {k | elistGlobals [.app trace location function args] k ≠ 0} =
      {k | elistGlobals args k ≠ 0} ∪ {k | elistGlobals [function] k ≠ 0} := by
  ext k
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  omega

/-- Expression-level application preserves global safety under the original
argument, function and closure-application induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsApp {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : args.length > 0 → EvalGlobalsInvariant args env s0)
    (fnIH : ∀ values next, args.length > 0 → evaluate args env s0 = (.val values, next) →
      EvalGlobalsInvariant [function] env next)
    (appIH : ∀ values next functions last, args.length > 0 →
      evaluate args env s0 = (.val values, next) → evaluate [function] env next = (.val functions, last) →
      EvalAppGlobalsInvariant location (@Flapjack.holHd ClosSem.Value ⟨unitValue⟩ functions) values last)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.app trace location function args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.app trace location function args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.app trace location function args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have safeParts : esgcFree function ∧ esgcFreeList args := by
    simpa [esgcFree] using expressionSafe (.app trace location function args) (by simp)
  have argsSafe := (esgcFreeList_iff args).1 safeParts.2
  have functionSafe : ∀ e ∈ [function], esgcFree e := by simpa using safeParts.1
  cases args with
  | nil =>
    simp [evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
  | cons arg rest =>
    have positive : (arg :: rest).length > 0 := by simp
    cases argsRun : evaluate (arg :: rest) env s0 with
    | mk argsResult next =>
      have ⟨nextSafe, argsResultSafe, n, nextOracle, argsFrame⟩ :=
        argsIH positive argsResult next ⟨argsRun, safe, argsSafe, envSafe⟩
      have nextClock : next.clock ≤ s0.clock := by
        simpa [argsRun] using evaluate_clock_le (arg :: rest) env s0
      have enlarged : mglobalsExtend s0.globals
          ({k | elistGlobals [.app trace location function (arg :: rest)] k ≠ 0} ∪
           {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
        apply mglobalsExtendSubset _ _ _ _ ⟨argsFrame, ?_⟩
        intro k member
        rcases member with member | member
        · left; rw [appWrites]; exact Or.inl member
        · exact Or.inr member
      cases argsResult with
      | err error =>
        simp only [evaluate, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, argsRun, fixClock] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨(ssgcFreeClock next (fun clock => min s0.clock clock)).2 nextSafe,
          argsResultSafe, n, nextOracle, enlarged⟩
      | val values =>
        cases fnRun : evaluate [function] env next with
        | mk fnResult mid =>
          have ⟨midSafe, fnResultSafe, m, midOracle, fnFrame⟩ :=
            fnIH values next positive argsRun fnResult mid ⟨fnRun, nextSafe, functionSafe, envSafe⟩
          have midClock : mid.clock ≤ next.clock := by
            simpa [fnRun] using evaluate_clock_le [function] env next
          have composed := combineOracleFrames s0 next mid _ _ n m nextOracle argsFrame fnFrame
          have finalOracle : mid.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
            simpa only [nextOracle, shiftSeqAdd] using midOracle
          have finalFrame : mglobalsExtend s0.globals
              ({k | elistGlobals [.app trace location function (arg :: rest)] k ≠ 0} ∪
               {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0}) mid.globals := by
            simpa only [appWrites] using composed
          cases fnResult with
          | err error =>
            simp [evaluate, argsRun, fixClock, Nat.min_eq_right nextClock, fnRun] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨(ssgcFreeClock mid (fun clock => min next.clock clock)).2 midSafe,
              fnResultSafe, n + m, finalOracle, finalFrame⟩
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value function env next mid fnValues fnRun
            have fnValueSafe : vsgcFree fnValue := by simpa [rsgcFree] using fnResultSafe
            have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using argsResultSafe
            cases appRun : evaluateApp location fnValue values mid with
            | mk appResult last =>
              have appProp := appIH values next [fnValue] mid positive argsRun fnRun
              have ⟨lastSafe, resultSafe, q, lastOracle, appFrame⟩ :=
                appProp appResult last ⟨by simpa [Flapjack.holHd] using appRun, midSafe, fnValueSafe, valuesSafe⟩
              have fullOracle : last.compileOracle = Flapjack.holShiftSeq ((n + m) + q) s0.compileOracle := by
                simpa only [finalOracle, shiftSeqAdd] using lastOracle
              have appFrame' : mglobalsExtend mid.globals
                  (∅ ∪ {k | elistGlobals (List.flatten (firstNExps mid.compileOracle q)) k ≠ 0}) last.globals := by
                simpa using appFrame
              have combined := combineOracleFrames s0 mid last _ ∅ (n + m) q finalOracle finalFrame appFrame'
              have fullFrame : mglobalsExtend s0.globals
                  ({k | elistGlobals [.app trace location function (arg :: rest)] k ≠ 0} ∪
                   {k | elistGlobals (List.flatten (firstNExps s0.compileOracle ((n + m) + q))) k ≠ 0}) last.globals := by
                simpa using combined
              simp [evaluate, argsRun, fixClock, Nat.min_eq_right nextClock, fnRun,
                Nat.min_eq_right midClock, appRun] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨lastSafe, resultSafe, (n + m) + q, fullOracle, fullFrame⟩


/-- A primitive expression's write set combines argument and operator writes.
This helper has no separate HOL declaration. -/
private theorem opWrites (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp) :
    {k | elistGlobals [.op trace op args] k ≠ 0} =
      {k | elistGlobals args k ≠ 0} ∪ {k | opGlobalBag op k ≠ 0} := by
  ext k
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  omega

/-- Global safety for the ordinary primitive-dispatch branch. The two
operation exclusions select a branch of the evaluator; this Lean helper has
no separate HOL declaration. -/
private theorem evaluateOrdinaryOpGlobals {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace op args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace op args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace op args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have argsSafe : ∀ e ∈ args, esgcFree e := by
    apply (esgcFreeList_iff args).1
    simpa [esgcFree] using expressionSafe (.op trace op args) (by simp)
  rw [evaluate_ordinaryOp_eq trace op args env s0 notInstall notForce] at run
  cases argsRun : evaluate args env s0 with
  | mk argsResult next =>
    have ⟨nextSafe, argsResultSafe, n, nextOracle, argsFrame⟩ :=
      argsIH argsResult next ⟨argsRun, safe, argsSafe, envSafe⟩
    have enlarged : mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace op args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      apply mglobalsExtendSubset _ _ _ _ ⟨argsFrame, ?_⟩
      intro k member
      rcases member with member | member
      · left; rw [opWrites]; exact Or.inl member
      · exact Or.inr member
    cases argsResult with
    | err error =>
      simp [argsRun] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨nextSafe, argsResultSafe, n, nextOracle, enlarged⟩
    | val values =>
      have valuesSafe : ∀ v ∈ values.reverse, vsgcFree v := by
        simpa [rsgcFree] using argsResultSafe
      cases doRun : doApp op values.reverse next with
      | err error =>
        have primitive := DoAppSafety.doAppSsgc op values.reverse next (.err error) ⟨doRun, valuesSafe, nextSafe⟩
        simp [argsRun, doRun] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨nextSafe, ?_, n, nextOracle, enlarged⟩
        cases error with
        | abort reason => simp [rsgcFree]
        | raise value => simpa [rsgcFree] using primitive.2 value rfl
      | val pair =>
        rcases pair with ⟨value, last⟩
        have primitive := DoAppSafety.doAppSsgc op values.reverse next (.val (value, last)) ⟨doRun, valuesSafe, nextSafe⟩
        have ⟨valueSafe, lastSafe, lastOracle, primitiveFrame⟩ := primitive.1 value last rfl
        have combined := mglobalsExtendTrans _ _ _ _ _ ⟨argsFrame, primitiveFrame⟩
        have finalFrame : mglobalsExtend s0.globals
            ({k | elistGlobals [.op trace op args] k ≠ 0} ∪
             {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) last.globals := by
          rw [opWrites]
          simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using combined
        simp [argsRun, doRun] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨lastSafe, ?_, n, ?_, finalFrame⟩
        · simpa [rsgcFree] using valueSafe
        · exact lastOracle.trans nextOracle

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpLabel {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.label label) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.label label) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.label label) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.label label) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpFfi {C F : Type} (trace : BackendCommon.Tra) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.ffi name) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.ffi name) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.ffi name) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.ffi name) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpInt {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.IntOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.intOp op) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.intOp op) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.intOp op) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.intOp op) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpWord {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.WordOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.wordOp op) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.wordOp op) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.wordOp op) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.wordOp op) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpBlock {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.BlockOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.blockOp op) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.blockOp op) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.blockOp op) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.blockOp op) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpGlobal {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.GlobOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.globOp op) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.globOp op) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.globOp op) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.globOp op) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpMemory {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.MemOp)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.memOp op) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.memOp op) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.memOp op) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.memOp op) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpAllocThunk {C F : Type} (trace : BackendCommon.Tra) (mode : Flapjack.AstHOL.ThunkMode)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.thunkOp (.allocThunk mode)) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.thunkOp (.allocThunk mode)) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.thunkOp (.allocThunk mode)) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.thunkOp (.allocThunk mode)) args env s0 (by simp) (by simp) argsIH res s h

/-- This primitive operation preserves the source evaluator safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpUpdateThunk {C F : Type} (trace : BackendCommon.Tra) (mode : Flapjack.AstHOL.ThunkMode)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.thunkOp (.updateThunk mode)) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.thunkOp (.updateThunk mode)) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.thunkOp (.updateThunk mode)) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  exact evaluateOrdinaryOpGlobals trace (.thunkOp (.updateThunk mode)) args env s0 (by simp) (by simp) argsIH res s h


/-- Inspecting a thunk in a safe store yields its safe payload and singleton
pointer. This helper has no separate HOL declaration. -/
private theorem destThunkSafe {C F : Type} (values : List ClosSem.Value)
    (s : ClosSem.State C F) (mode : Flapjack.AstHOL.ThunkMode) (value : ClosSem.Value)
    (safe : ssgcFree s) (found : ClosSem.destThunk values s.refs = .isThunk mode value) :
    (∃ flag ptr, values = [.refPtr flag ptr]) ∧ vsgcFree value := by
  unfold ClosSem.destThunk at found
  repeat' split at found
  all_goals simp_all
  exact safe.2.2.1 _ _ _ (by assumption)


/-- Forcing a thunk preserves global safety under the original argument and
conditional thunk-body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpForceThunk {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (forceIH : ∀ values next value, evaluate args env s0 = (.val values, next) →
      ClosSem.destThunk values next.refs = .isThunk .notEvaluated value →
      EvalGlobalsInvariant [appUnit (.var .none 0)] [value] next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace (.thunkOp .forceThunk) args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace (.thunkOp .forceThunk) args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.thunkOp .forceThunk) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have argsSafe : ∀ e ∈ args, esgcFree e := by
    apply (esgcFreeList_iff args).1
    simpa [esgcFree] using expressionSafe (.op trace (.thunkOp .forceThunk) args) (by simp)
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env s0 with
  | mk argsResult next =>
    have ⟨nextSafe, argsResultSafe, n, nextOracle, argsFrame⟩ :=
      argsIH argsResult next ⟨argsRun, safe, argsSafe, envSafe⟩
    have frame : mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace (.thunkOp .forceThunk) args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      rw [opWrites]
      simpa [opGlobalBag, emptyGlobalBag, Flapjack.emptyBag] using argsFrame
    cases argsResult with
    | err error =>
      simp [argsRun] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨nextSafe, argsResultSafe, n, nextOracle, frame⟩
    | val values =>
      rw [argsRun] at run
      dsimp only at run
      cases inspected : ClosSem.destThunk values next.refs with
      | badRef | notThunk =>
        rw [inspected] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨nextSafe, by simp [rsgcFree], n, nextOracle, frame⟩
      | isThunk mode value =>
        have ⟨⟨flag, ptr, valuesEq⟩, valueSafe⟩ := destThunkSafe values next mode value nextSafe inspected
        cases mode with
        | evaluated =>
          rw [inspected] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨nextSafe, by simpa [rsgcFree] using valueSafe, n, nextOracle, frame⟩
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] next with
          | mk forceResult last =>
            have forceExprSafe : ∀ e ∈ [appUnit (.var .none 0)], esgcFree e := by
              simp [appUnit, esgcFree, esgcFreeList]
            have ⟨lastSafe, forceResultSafe, m, lastOracle, forceFrame⟩ :=
              forceIH values next value argsRun inspected forceResult last
                ⟨forceRun, nextSafe, forceExprSafe, by simpa using valueSafe⟩
            have finalOracle : last.compileOracle = Flapjack.holShiftSeq (n + m) s0.compileOracle := by
              simpa only [nextOracle, shiftSeqAdd] using lastOracle
            have forceFrame' : mglobalsExtend next.globals
                (∅ ∪ {k | elistGlobals (List.flatten (firstNExps next.compileOracle m)) k ≠ 0}) last.globals := by
              simpa [appUnit, elistGlobals, setGlobals, opGlobalBag,
                FlatProps.unionGlobalBag, emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using forceFrame
            have combined := combineOracleFrames s0 next last _ ∅ n m nextOracle argsFrame forceFrame'
            have finalFrame : mglobalsExtend s0.globals
                ({k | elistGlobals [.op trace (.thunkOp .forceThunk) args] k ≠ 0} ∪
                 {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + m))) k ≠ 0}) last.globals := by
              rw [opWrites]
              simpa [opGlobalBag, emptyGlobalBag, Flapjack.emptyBag] using combined
            rw [forceRun] at run
            cases forceResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨lastSafe, forceResultSafe, n + m, finalOracle, finalFrame⟩
            | val forced =>
              dsimp only at run
              cases updated : updateThunk values last.refs forced with
              | none =>
                rw [updated] at run
                simp at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨lastSafe, by simp [rsgcFree], n + m, finalOracle, finalFrame⟩
              | some refs =>
                have forcedSafe : ∀ v ∈ forced, vsgcFree v := by simpa [rsgcFree] using forceResultSafe
                have updatedSafe : ssgcFree {last with refs := refs} := by
                  apply updateThunkSsgcFree last flag ptr forced refs
                  exact ⟨lastSafe, forcedSafe, by simpa [valuesEq] using updated⟩
                rw [updated] at run
                simp at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨updatedSafe, forceResultSafe, n + m, finalOracle, finalFrame⟩


/-- A program contained in an oracle prefix contributes its writes to the
flattened prefix. This helper has no separate HOL declaration. -/
private theorem prefixContainsWrites (programs : List (List ClosLang.Exp)) (program : List ClosLang.Exp)
    (member : program ∈ programs) :
    {k | elistGlobals program k ≠ 0} ⊆ {k | elistGlobals programs.flatten k ≠ 0} := by
  intro k writes
  change elistGlobals program k ≠ 0 at writes
  change elistGlobals programs.flatten k ≠ 0
  induction programs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    simp only [List.flatten_cons, elistGlobals_append]
    rcases member with rfl | member
    · omega
    · have rest := ih member
      omega

/-- The HOL last element of a nonempty list belongs to that list. This helper
has no separate HOL declaration. -/
private theorem holLastMember {α : Type} [Nonempty α] (xs : List α) (nonempty : xs ≠ []) :
    Flapjack.holLast xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons head tail ih =>
    cases tail with
    | nil => simp [Flapjack.holLast]
    | cons next rest =>
      rw [Flapjack.holLast_cons]
      simp only [List.cons_ne_nil, ↓reduceIte]
      exact List.mem_cons_of_mem _ (ih (by simp))


/-- Dynamic installation preserves global safety under the original
argument and successful-installation body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOpInstall {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (installIH : ∀ values next program installed,
      evaluate args env s0 = (.val values, next) →
      doInstall values.reverse next = (.val program, installed) →
      EvalGlobalsInvariant program [] installed)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace .install args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace .install args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace .install args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, expressionSafe, envSafe⟩
  have argsSafe : ∀ e ∈ args, esgcFree e := by
    apply (esgcFreeList_iff args).1
    simpa [esgcFree] using expressionSafe (.op trace .install args) (by simp)
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env s0 with
  | mk argsResult next =>
    have ⟨nextSafe, argsResultSafe, n, nextOracle, argsFrame⟩ :=
      argsIH argsResult next ⟨argsRun, safe, argsSafe, envSafe⟩
    have frame : mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace .install args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) next.globals := by
      rw [opWrites]
      simpa [opGlobalBag, emptyGlobalBag, Flapjack.emptyBag] using argsFrame
    cases argsResult with
    | err error =>
      simp [argsRun] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨nextSafe, argsResultSafe, n, nextOracle, frame⟩
    | val values =>
      rw [argsRun] at run
      dsimp only at run
      cases installRun : doInstall values.reverse next with
      | mk installResult installed =>
        cases installResult with
        | err error =>
          have ⟨installedSafe, errorSafe, q, installedOracle, globalsEq⟩ :=
            doInstallErrorSafety values.reverse next installed error nextSafe installRun
          have installedFrame : mglobalsExtend next.globals
              (∅ ∪ {k | elistGlobals (List.flatten (firstNExps next.compileOracle q)) k ≠ 0}) installed.globals := by
            rw [globalsEq]
            exact mglobalsExtendRefl _ _
          have combined := combineOracleFrames s0 next installed _ ∅ n q nextOracle argsFrame installedFrame
          have finalFrame : mglobalsExtend s0.globals
              ({k | elistGlobals [.op trace .install args] k ≠ 0} ∪
               {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + q))) k ≠ 0}) installed.globals := by
            rw [opWrites]
            simpa [opGlobalBag, emptyGlobalBag, Flapjack.emptyBag] using combined
          have finalOracle : installed.compileOracle = Flapjack.holShiftSeq (n + q) s0.compileOracle := by
            simpa only [nextOracle, shiftSeqAdd] using installedOracle
          rw [installRun] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨installedSafe, errorSafe, n + q, finalOracle, finalFrame⟩
        | val program =>
          have ⟨installedSafe, programSafe, programNonempty, installedOracle, firstProgram, globalsFrame⟩ :=
            doInstallSsgc values.reverse next program installed ⟨installRun, nextSafe⟩
          have installedFrame : mglobalsExtend next.globals
              (∅ ∪ {k | elistGlobals (List.flatten (firstNExps next.compileOracle 1)) k ≠ 0}) installed.globals := by
            apply mglobalsExtendSubset _ _ _ _ ⟨globalsFrame, ?_⟩
            simp
          have firstCombined := combineOracleFrames s0 next installed _ ∅ n 1 nextOracle argsFrame installedFrame
          have firstOracle : installed.compileOracle = Flapjack.holShiftSeq (n + 1) s0.compileOracle := by
            simpa only [nextOracle, shiftSeqAdd] using installedOracle
          cases programRun : evaluate program [] installed with
          | mk programResult last =>
            have ⟨lastSafe, programResultSafe, m, lastOracle, programFrame⟩ :=
              installIH values next program installed argsRun installRun programResult last
                ⟨programRun, installedSafe, programSafe, by simp⟩
            have finalOracle : last.compileOracle = Flapjack.holShiftSeq ((n + 1) + m) s0.compileOracle := by
              simpa only [firstOracle, shiftSeqAdd] using lastOracle
            have firstCombined' : mglobalsExtend s0.globals
                ({k | elistGlobals args k ≠ 0} ∪
                 {k | elistGlobals (List.flatten (firstNExps s0.compileOracle (n + 1))) k ≠ 0}) installed.globals := by
              simpa using firstCombined
            have combined := combineOracleFrames s0 installed last _ _ (n + 1) m firstOracle firstCombined' programFrame
            have programEq : (s0.compileOracle n).2.1 = program := by
              simpa [firstNExps, nextOracle, Flapjack.holShiftSeq] using firstProgram
            have programMember : program ∈ firstNExps s0.compileOracle ((n + 1) + m) := by
              rw [← programEq]
              exact memFirstNExps n ((n + 1) + m) (by omega) s0.compileOracle
            have programIncluded := prefixContainsWrites _ _ programMember
            have finalFrame : mglobalsExtend s0.globals
                ({k | elistGlobals [.op trace .install args] k ≠ 0} ∪
                 {k | elistGlobals (List.flatten (firstNExps s0.compileOracle ((n + 1) + m))) k ≠ 0}) last.globals := by
              apply mglobalsExtendSubset _ _ _ _ ⟨combined, ?_⟩
              rw [opWrites]
              simp only [opGlobalBag, emptyGlobalBag, ne_eq, not_true_eq_false, Set.ofPred_false, Set.union_empty, Flapjack.emptyBag]
              intro k member
              rcases member with (member | member) | member
              · exact Or.inl member
              · exact Or.inr (programIncluded member)
              · exact Or.inr member
            rw [installRun] at run
            dsimp only at run
            rw [programRun] at run
            cases programResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨lastSafe, programResultSafe, (n + 1) + m, finalOracle, finalFrame⟩
            | val results =>
              have resultLength := (evaluate_length (C := C) (F := F)).1 program [] installed last results programRun
              have resultsNonempty : results ≠ [] := by
                intro empty
                subst results
                simp at resultLength
                exact programNonempty (List.eq_nil_of_length_eq_zero resultLength.symm)
              have lastSafeValue : vsgcFree (@Flapjack.holLast ClosSem.Value ⟨unitValue⟩ results) := by
                apply programResultSafe
                exact @holLastMember ClosSem.Value ⟨unitValue⟩ results resultsNonempty
              dsimp only at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨lastSafe, ?_, (n + 1) + m, finalOracle, finalFrame⟩
              simp only [rsgcFree, List.mem_singleton, forall_eq]
              change vsgcFree (@Flapjack.holLast ClosSem.Value ⟨unitValue⟩ results)
              exact lastSafeValue


/-- Every primitive-expression operation preserves global safety under the
original argument, installation and thunk-forcing induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsOp {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (argsIH : EvalGlobalsInvariant args env s0)
    (installIH : ∀ values next program installed,
      evaluate args env s0 = (.val values, next) → op = .install →
      doInstall values.reverse next = (.val program, installed) →
      EvalGlobalsInvariant program [] installed)
    (forceIH : ∀ values next value, evaluate args env s0 = (.val values, next) →
      op ≠ .install → op = .thunkOp .forceThunk →
      ClosSem.destThunk values next.refs = .isThunk .notEvaluated value →
      EvalGlobalsInvariant [appUnit (.var .none 0)] [value] next)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.op trace op args] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.op trace op args] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.op trace op args] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  cases op with
  | label label => exact evaluateChangedGlobalsOpLabel trace label args env s0 argsIH res s h
  | ffi name => exact evaluateChangedGlobalsOpFfi trace name args env s0 argsIH res s h
  | intOp op => exact evaluateChangedGlobalsOpInt trace op args env s0 argsIH res s h
  | wordOp op => exact evaluateChangedGlobalsOpWord trace op args env s0 argsIH res s h
  | blockOp op => exact evaluateChangedGlobalsOpBlock trace op args env s0 argsIH res s h
  | globOp op => exact evaluateChangedGlobalsOpGlobal trace op args env s0 argsIH res s h
  | memOp op => exact evaluateChangedGlobalsOpMemory trace op args env s0 argsIH res s h
  | install =>
    apply evaluateChangedGlobalsOpInstall trace args env s0 argsIH ?_ res s h
    intro values next program installed argsRun installRun
    exact installIH values next program installed argsRun rfl installRun
  | thunkOp op =>
    cases op with
    | allocThunk mode => exact evaluateChangedGlobalsOpAllocThunk trace mode args env s0 argsIH res s h
    | updateThunk mode => exact evaluateChangedGlobalsOpUpdateThunk trace mode args env s0 argsIH res s h
    | forceThunk =>
      apply evaluateChangedGlobalsOpForceThunk trace args env s0 argsIH ?_ res s h
      intro values next value argsRun inspected
      exact forceIH values next value argsRun (by simp) rfl inspected

end EvaluateGlobalsPort
end Flapjack.Compiler.Backend.ClosKnown
