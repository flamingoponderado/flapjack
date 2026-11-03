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

end EvaluateGlobalsPort
end Flapjack.Compiler.Backend.ClosKnown
