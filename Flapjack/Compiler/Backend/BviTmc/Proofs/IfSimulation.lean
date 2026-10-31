import Flapjack.Compiler.Backend.BviTmc.Proofs.ListSimulation

/-! Ordinary conditional simulation for the TMC proof. -/
namespace Flapjack.Compiler.Backend.BviTmc.IfSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation

private theorem asBool_related (f : HolFiniteMapExact Nat Nat) (v w : Value)
    (related : valueRel f v w) : asBool v = asBool w := by
  cases related with
  | number i => rfl
  | word64 w => rfl
  | codePtr n => rfl
  | refPtr n m flag mapped => rfl
  | block tag xs ys fields => cases fields <;> simp [asBool]

/-- Flapjack infrastructure: ordinary conditional simulation from the
condition and selected-branch induction hypotheses. The source measure,
safety premises, and optimized wrapper/worker conclusions are not included. -/
theorem evaluate_if_core {C F : Type} (condition yes no : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (conditionIH : ∀ r mid, evaluate [condition] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [condition] env2 f target r mid)
    (branchIH : ∀ branch mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      (branch = yes ∨ branch = no) → evaluate [branch] env1 mid = (result, final) →
      envRel opt g env1 env2 → stateRel g mid t → Core [branch] env2 g t result final) :
    Core [.ifThenElse condition yes no] env2 f target result final := by
  cases conditionRun : evaluate [condition] env1 source with
  | mk conditionResult middle =>
    have conditionSafe : conditionResult ≠ .err (.abort .typeError) := by
      intro bad
      subst conditionResult
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
      exact notTypeError (congrArg Prod.fst run.symm)
    obtain ⟨middleTarget, g, targetResult, targetRun, related, middleStates, extension,
      fresh, unchanged, still⟩ := conditionIH conditionResult middle conditionRun conditionSafe
    cases conditionResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err error' =>
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨middleTarget, g, .err error', ?_, related, middleStates, extension, fresh, unchanged, still⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton condition env1 source middle values conditionRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val values' =>
        obtain ⟨value', rfl⟩ := evaluate_singleton condition env2 target middleTarget values' targetRun
        have valuesRelated : valueRel g value value' := by
          simp only [resultRel] at related
          cases related with | cons h _ => exact h
        have boolEq := asBool_related g value value' valuesRelated
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, conditionRun] at run
        change (match asBool value with
          | none => (.err (.abort .typeError), middle)
          | some true => evaluate [yes] env1 middle
          | some false => evaluate [no] env1 middle) = (result, final) at run
        cases decoded : asBool value with
        | none =>
          simp [decoded] at run
          exact False.elim (notTypeError run.1.symm)
        | some boolean =>
          have decoded' : asBool value' = some boolean := by rw [← boolEq, decoded]
          cases boolean <;> simp only [decoded] at run
          all_goals
            obtain ⟨last, h, branchResult, branchRun, branchRel, states, branchExtension,
              branchFresh, branchUnchanged, branchStill⟩ :=
              branchIH _ middle g middleTarget (by simp) run
                (envRel_submap opt f g env1 env2 environments extension) middleStates
            have submap : finiteSubmap f h := by
              intro k v found; exact branchExtension k v (extension k v found)
            have domain := BviProps.evaluate_refs_subset [condition] env2 target middleTarget (.val [value']) targetRun
            have allFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh branchFresh domain
            have allUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs last.refs ∅
              unchanged branchUnchanged fresh extension
            have allStill := holesStill_trans f g target.refs middleTarget.refs last.refs ()
              still branchStill fresh extension
            refine ⟨last, h, branchResult, ?_, branchRel, states, submap, allFresh, allUnchanged, allStill⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
            change (match asBool value' with
              | none => ((.err (.abort .typeError) : BviResult), middleTarget)
              | some true => evaluate [yes] env2 middleTarget
              | some false => evaluate [no] env2 middleTarget) = _
            simpa [decoded'] using branchRun

end Flapjack.Compiler.Backend.BviTmc.IfSimulation
