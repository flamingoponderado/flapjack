module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

@[expose] public section

/-! Sequencing case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace SequencePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end SequencePort

/-- The nonempty sequencing case of the reverse evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_cons {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (firstIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate [first] envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code [first] →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (restIH : ∀ (values : List Value) (middle : State C F),
      evaluate [first] envTarget target = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate (second :: rest) envTarget middle = (result, next) ∧
          List.Forall₂ ValueRel envSource envTarget ∧ StateRel source middle ∧
          CodeRel code (second :: rest) →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate (first :: second :: rest) envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode (first :: second :: rest)) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode (first :: second :: rest) code
  cases sourceCode with
  | nil => simp at length
  | cons sourceFirst sourceTail =>
    cases sourceTail with
    | nil => simp at length
    | cons sourceSecond sourceRest =>
      have codeParts : first = removeSing sourceFirst ∧
          second :: rest = removeList (sourceSecond :: sourceRest) := by
        simpa [CodeRel, removeList] using code
      have firstCode : CodeRel [sourceFirst] [first] := by
        simp [CodeRel, removeList, codeParts.1]
      have tailCode : CodeRel (sourceSecond :: sourceRest) (second :: rest) := codeParts.2
      cases firstRun : evaluate [first] envTarget target with
      | mk firstResult targetMiddle =>
        cases firstResult with
        | err error =>
          rw [ClosProps.evaluate_cons_error first (second :: rest) envTarget target targetMiddle error firstRun] at run
          cases run
          obtain ⟨extra, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
            firstIH (.err error) targetNext envSource source [sourceFirst] ⟨firstRun, envRel, states, firstCode⟩
          cases sourceResult with
          | val values => cases error <;> simp [ResultRel] at related
          | err sourceError =>
            exact ⟨extra, .err sourceError, sourceMiddle,
              ClosProps.evaluate_cons_error _ _ _ _ _ _ sourceRun, related, middleRel⟩
        | val values =>
          obtain ⟨value, rfl⟩ := evaluate_singleton_value first envTarget target targetMiddle values firstRun
          obtain ⟨extraFirst, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
            firstIH (.val [value]) targetMiddle envSource source [sourceFirst] ⟨firstRun, envRel, states, firstCode⟩
          cases sourceResult with
          | err error => cases error <;> simp [ResultRel] at related
          | val sourceValues =>
            cases related with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i sourceValue
              rw [ClosProps.evaluate_cons_value first (second :: rest) envTarget target targetMiddle value firstRun] at run
              cases tailRun : evaluate (second :: rest) envTarget targetMiddle with
              | mk tailResult targetLast =>
                rw [tailRun] at run
                obtain ⟨extraRest, sourceTailResult, sourceLast, sourceTailRun, tailRel, lastRel⟩ :=
                  restIH [value] targetMiddle firstRun tailResult targetLast envSource sourceMiddle
                    (sourceSecond :: sourceRest) ⟨tailRun, envRel, middleRel, tailCode⟩
                have shifted := (evaluate_addClock (C := C) (F := F)).1 [sourceFirst] envSource
                  { source with clock := source.clock + extraFirst } sourceMiddle (.val [sourceValue]) extraRest
                  sourceRun (by simp)
                have shiftedRun : evaluate [sourceFirst] envSource
                    { source with clock := source.clock + (extraFirst + extraRest) } =
                      (.val [sourceValue], { sourceMiddle with clock := sourceMiddle.clock + extraRest }) := by
                  simpa [Nat.add_assoc] using shifted
                cases tailResult with
                | err error =>
                  simp only at run
                  cases run
                  cases sourceTailResult with
                  | val values => cases error <;> simp [ResultRel] at tailRel
                  | err sourceError =>
                    refine ⟨extraFirst + extraRest, .err sourceError, sourceLast, ?_, tailRel, lastRel⟩
                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ shiftedRun, sourceTailRun]
                | val values =>
                  simp only at run
                  cases run
                  cases sourceTailResult with
                  | err error => cases error <;> simp [ResultRel] at tailRel
                  | val sourceValues =>
                    refine ⟨extraFirst + extraRest, .val (sourceValue :: sourceValues), sourceLast, ?_, ?_, lastRel⟩
                    · rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ shiftedRun, sourceTailRun]
                    · exact .cons valueRel tailRel

end Flapjack.Compiler.Backend.ClosTicks
