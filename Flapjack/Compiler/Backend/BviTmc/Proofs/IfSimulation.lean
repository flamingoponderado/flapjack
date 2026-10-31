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

/-- Flapjack infrastructure: conditional simulation with independently selected target branches from the
condition and selected-branch induction hypotheses. The source measure,
safety premises, and optimized wrapper/worker conclusions are not included. -/
theorem evaluate_if_to_core {C F : Type} (condition yes no yesTarget noTarget : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (conditionIH : ∀ r mid, evaluate [condition] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [condition] env2 f target r mid)
    (branchIH : ∀ branch branchTarget mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      ((branch = yes ∧ branchTarget = yesTarget) ∨ (branch = no ∧ branchTarget = noTarget)) → evaluate [branch] env1 mid = (result, final) →
      envRel opt g env1 env2 → stateRel g mid t → Core [branchTarget] env2 g t result final) :
    Core [.ifThenElse condition yesTarget noTarget] env2 f target result final := by
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
          let selected := if boolean then yes else no
          let selectedTarget := if boolean then yesTarget else noTarget
          have branchSource : evaluate [selected] env1 middle = (result, final) := by
            cases boolean <;> simpa [selected, decoded] using run
          have branchPair : (selected = yes ∧ selectedTarget = yesTarget) ∨
              (selected = no ∧ selectedTarget = noTarget) := by
            cases boolean <;> simp [selected, selectedTarget]
          obtain ⟨last, h, branchResult, branchRun, branchRel, states, branchExtension,
            branchFresh, branchUnchanged, branchStill⟩ :=
            branchIH selected selectedTarget middle g middleTarget branchPair branchSource
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
            | some true => evaluate [yesTarget] env2 middleTarget
            | some false => evaluate [noTarget] env2 middleTarget) = _
          cases boolean <;> simpa [decoded', selectedTarget] using branchRun

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
  apply evaluate_if_to_core condition yes no yes no source env1 result final opt f target env2
    run notTypeError environments conditionIH
  intro branch branchTarget mid g t pair branchRun env states
  rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact branchIH _ mid g t (Or.inl rfl) branchRun env states
  · exact branchIH _ mid g t (Or.inr rfl) branchRun env states

/-- Flapjack infrastructure: the wrapper branch of conditional simulation,
assuming the condition and selected-branch induction hypotheses. The branch
hypothesis covers both a rewritten branch and an unchanged branch. -/
theorem evaluate_if_wrapper {C F : Type} (condition yes no wrapper : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc locOpt : Nat)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (wrapperRun : rewriteWrapperSource loc locOpt env1.length (.ifThenElse condition yes no) = some wrapper)
    (conditionIH : ∀ r mid, evaluate [condition] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [condition] env2 f target r mid)
    (branchIH : ∀ branch branchTarget mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      (branch = yes ∨ branch = no) →
      (rewriteWrapperSource loc locOpt env1.length branch = some branchTarget ∨ branchTarget = branch) →
      evaluate [branch] env1 mid = (result, final) →
      envRel opt g env1 env2 → stateRel g mid t → Core [branchTarget] env2 g t result final) :
    Core [wrapper] env2 f target result final := by
  rw [rewriteWrapperSource.eq_def] at wrapperRun
  cases hy : rewriteWrapperSource loc locOpt env1.length yes <;>
    cases hn : rewriteWrapperSource loc locOpt env1.length no <;> simp_all
  all_goals
    subst wrapper
    apply evaluate_if_to_core condition yes no _ _ source env1 result final opt f target env2
      run notTypeError environments conditionIH
    intro branch branchTarget mid g t pair branchRun env states
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply branchIH _ _ mid g t (Or.inl rfl) ?_ branchRun env states
      simp_all
    · apply branchIH _ _ mid g t (Or.inr rfl) ?_ branchRun env states
      simp_all

end Flapjack.Compiler.Backend.BviTmc.IfSimulation
