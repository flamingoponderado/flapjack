import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateRefs

/-! Sequential expression-list simulation for the TMC proof. -/
namespace Flapjack.Compiler.Backend.BviTmc.ListSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: the ordinary simulation conclusion, factored out
for the head and tail induction hypotheses. -/
def Core {C F : Type} (xs : List Bvi.Exp) (env2 : List Value)
    (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (result : BviResult) (final : BviState (Nat × C) F) : Prop :=
  ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
    evaluate xs env2 target = (nextResult, next) ∧
    resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
    stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
    onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
    holesStillNotFinalised f target.refs next.refs

/-- Flapjack infrastructure: the non-singleton list induction step. Its two
hypotheses are the specialized ordinary simulations of the head and tail;
the original well-founded measure and safety premises are omitted. -/
theorem evaluate_cons_cons {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate (first :: second :: rest) env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel false f env1 env2)
    (headIH : ∀ r mid, evaluate [first] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [first] env2 f target r mid)
    (tailIH : ∀ r mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      (∃ value, evaluate [first] env1 source = (.val [value], mid)) →
      evaluate (second :: rest) env1 mid = (r, final) →
      envRel false g env1 env2 → stateRel g mid t →
      r ≠ .err (.abort .typeError) → Core (second :: rest) env2 g t r final) :
    Core (first :: second :: rest) env2 f target result final := by
  change BviSem.evaluateTuple (first :: second :: rest, env1, source) = _ at run
  rw [evaluateConsCons] at run
  cases headRun : evaluate [first] env1 source with
  | mk headResult middle =>
    have headSafe : headResult ≠ .err (.abort .typeError) := by
      intro bad
      subst headResult
      simp [BviSem.evaluateTuple, headRun] at run
      exact notTypeError run.1.symm
    obtain ⟨middleTarget, g, headTargetResult, headTargetRun, headRel, middleStates,
      firstExtension, firstFresh, firstUnchanged, firstStill⟩ := headIH headResult middle headRun headSafe
    cases headResult with
    | err error =>
      cases headTargetResult with
      | val values => simp [resultRel] at headRel
      | err error' =>
        simp [BviSem.evaluateTuple, headRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨middleTarget, g, .err error', ?_, headRel, middleStates, firstExtension,
          firstFresh, firstUnchanged, firstStill⟩
        change BviSem.evaluateTuple (first :: second :: rest, env2, target) = _
        rw [evaluateConsCons]
        simp [BviSem.evaluateTuple, headTargetRun]
    | val values =>
      obtain ⟨headValue, rfl⟩ := evaluate_singleton first env1 source middle values headRun
      cases headTargetResult with
      | err error => simp [resultRel] at headRel
      | val values' =>
        obtain ⟨headValue', rfl⟩ := evaluate_singleton first env2 target middleTarget values' headTargetRun
        have headValueRel : valueRel g headValue headValue' := by
          simp only [resultRel] at headRel
          cases headRel with | cons related _ => exact related
        cases tailRun : evaluate (second :: rest) env1 middle with
        | mk tailResult tailFinal =>
          have outerRun : (match tailResult with
              | .err error => (.err error, tailFinal)
              | .val tailValues => (.val (headValue :: tailValues), tailFinal)) = (result, final) := by
            cases tailResult <;> simpa [BviSem.evaluateTuple, headRun, tailRun, Flapjack.holHd] using run
          have tailSafe : tailResult ≠ .err (.abort .typeError) := by
            intro bad
            subst tailResult
            exact notTypeError (congrArg Prod.fst outerRun.symm)
          have finalEq : tailFinal = final := by
            cases tailResult <;> exact congrArg Prod.snd outerRun
          subst tailFinal
          obtain ⟨last, h, tailTargetResult, tailTargetRun, tailRel, lastStates,
            secondExtension, secondFresh, secondUnchanged, secondStill⟩ :=
            tailIH tailResult middle g middleTarget ⟨headValue, headRun⟩ tailRun
              (envRel_submap false f g env1 env2 environments firstExtension) middleStates tailSafe
          have extension : finiteSubmap f h := by
            intro key value found; exact secondExtension key value (firstExtension key value found)
          have domain := BviProps.evaluate_refs_subset [first] env2 target middleTarget (.val [headValue']) headTargetRun
          have fresh := onlyFresh_trans f g h target.refs middleTarget.refs firstFresh secondFresh domain
          have unchanged := holesUnchanged_trans f g target.refs middleTarget.refs last.refs ∅
            firstUnchanged secondUnchanged firstFresh firstExtension
          have still := holesStill_trans f g target.refs middleTarget.refs last.refs ()
            firstStill secondStill firstFresh firstExtension
          cases tailResult with
          | err error =>
            cases tailTargetResult with
            | val vals => simp [resultRel] at tailRel
            | err error' =>
              simp at outerRun
              subst result
              refine ⟨last, h, .err error', ?_, tailRel, lastStates, extension, fresh, unchanged, still⟩
              change BviSem.evaluateTuple (first :: second :: rest, env2, target) = _
              rw [evaluateConsCons]
              simp [BviSem.evaluateTuple, headTargetRun, tailTargetRun]
          | val tailValues =>
            cases tailTargetResult with
            | err error => simp [resultRel] at tailRel
            | val tailValues' =>
              simp at outerRun
              subst result
              refine ⟨last, h, .val (headValue' :: tailValues'), ?_, ?_, lastStates,
                extension, fresh, unchanged, still⟩
              · change BviSem.evaluateTuple (first :: second :: rest, env2, target) = _
                rw [evaluateConsCons]
                simp [BviSem.evaluateTuple, headTargetRun, tailTargetRun, Flapjack.holHd]
              · exact List.Forall₂.cons (valueRel_submap g h _ _ headValueRel secondExtension) tailRel

end Flapjack.Compiler.Backend.BviTmc.ListSimulation
