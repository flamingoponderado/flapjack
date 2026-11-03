import Flapjack.Compiler.Backend.ClosKnown.Proofs.InstallGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.ClosureGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.PrimitiveGlobals
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

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
private theorem lookupVarsSafe (indices : List Nat) (env selected : List ClosSem.Value)
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
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag]
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
  simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, emptyGlobalBag]
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

end EvaluateGlobalsPort
end Flapjack.Compiler.Backend.ClosKnown
