import Flapjack.Compiler.Backend.BviTmc.Proofs.IfSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.MutableBlockOld
import Flapjack.Compiler.Backend.BviTmc.Proofs.WrapperCases

/-! Optimized conditional worker simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.IfWorker
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation MutableBlockOld

private theorem asBool_related (f : HolFiniteMapExact Nat Nat) (v w : Value)
    (related : valueRel f v w) : asBool v = asBool w := by
  cases related with
  | number i => rfl
  | word64 w => rfl
  | codePtr n => rfl
  | refPtr n m flag mapped => rfl
  | block tag xs ys fields => cases fields <;> simp [asBool]

/-- Flapjack infrastructure: the worker conclusion of TMC simulation. -/
def WorkerCore {C F : Type} (work : Bvi.Exp) (env1 env2 : List Value)
    (f : HolFiniteMapExact Nat Nat) (target : BviState C F) (holePtr : Nat)
    (result : BviResult) (final : BviState (Nat × C) F) : Prop :=
  ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
    evaluate [work] env2 target = (workResult, workState) ∧
    optResRel workMap result workResult ∧ stateRel workMap final workState ∧
    finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
    holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
    holesStillNotFinalised f target.refs workState.refs ∧
    ∀ resValue, result = .val [resValue] →
      ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
        holeHasVal f env1 env2 workState.refs resValue'

/-- Flapjack infrastructure: the conditional worker induction step, using
ordinary condition simulation and the selected worker's induction hypothesis.
The source measure and safety premises are omitted. -/
theorem evaluate_if_worker {C F : Type} (condition yes no : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc locOpt holePtr : Nat)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel true f env1 env2)
    (c : Value) (hole : holeHasVal f env1 env2 target.refs c)
    (notFinal : holeNotFinalised target.refs holePtr)
    (pointer : holEl env1.length env2 = .refPtr false holePtr)
    (code : optimisedCode loc locOpt source.code target.code)
    (conditionIH : ∀ r mid, evaluate [condition] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [condition] env2 f target r mid)
    (branchIH : ∀ branch mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      (branch = yes ∨ branch = no) → evaluate [branch] env1 mid = (result, final) →
      envRel true g env1 env2 → stateRel g mid t →
      holeHasVal g env1 env2 t.refs c → holeNotFinalised t.refs holePtr →
      optimisedCode loc locOpt mid.code t.code →
      WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length branch)
        env1 env2 g t holePtr result final) :
    WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length
      (.ifThenElse condition yes no)) env1 env2 f target holePtr result final := by
  have outside : holePtr ∉ mapRange f := by
    obtain ⟨_, ptr, _, _, _, _, ptrEq, _, _, out, _⟩ := hole
    rw [pointer] at ptrEq
    have same : ptr = holePtr := by simpa using ptrEq.symm
    simpa [same] using out
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
        refine ⟨.err error', g, middleTarget, ?_, related, middleStates, extension, fresh,
          holesUnchanged_subset f target.refs middleTarget.refs ∅ {holePtr} unchanged (by simp), still, ?_⟩
        · simp only [rewriteWorkerSource]
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
        · intro _ impossible; cases impossible
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
          have nextHole : holeHasVal g env1 env2 middleTarget.refs c := by
            obtain ⟨length, ptr, tag, finalised, left, right, ptrEq, idxEq, small, ptrOutside, found⟩ := hole
            obtain ⟨nextFinal, nextChild, nextFound, sameChild⟩ := unchanged ptr tag finalised left c right ptrOutside found
            have childEq : c = nextChild := sameChild (by simp)
            have allocated : ptr ∈ target.refs.domain := by simp [HolFiniteMapExact.domain, found]
            have nextOutside := nonFresh_not_in_range f g target.refs ptr allocated ptrOutside fresh
            exact ⟨length, ptr, tag, nextFinal, left, right, ptrEq, idxEq, small, nextOutside, by simpa [childEq] using nextFound⟩
          have nextNotFinal : holeNotFinalised middleTarget.refs holePtr := still holePtr outside notFinal
          let selected := if boolean then yes else no
          have branchSource : evaluate [selected] env1 middle = (result, final) := by
            cases boolean <;> simpa [selected, decoded] using run
          have branchMember : selected = yes ∨ selected = no := by cases boolean <;> simp [selected]
          obtain ⟨workResult, h, workState, workRun, workRel, states, branchExtension,
            branchFresh, branchUnchanged, branchStill, filled⟩ :=
            branchIH selected middle g middleTarget branchMember branchSource
              (envRel_submap true f g env1 env2 environments extension) middleStates nextHole nextNotFinal
              (WrapperCases.evaluate_pres_opt_code loc locOpt source middle target middleTarget
                [condition] env1 env2 (.val [value]) (.val [value']) code conditionRun targetRun)
          have submap : finiteSubmap f h := by
            intro k v found; exact branchExtension k v (extension k v found)
          have domain := BviProps.evaluate_refs_subset [condition] env2 target middleTarget (.val [value']) targetRun
          have allFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh branchFresh domain
          have widened := holesUnchanged_subset f target.refs middleTarget.refs ∅ {holePtr} unchanged (by simp)
          have allUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs workState.refs {holePtr}
            widened branchUnchanged fresh extension
          have allStill := holesStill_trans f g target.refs middleTarget.refs workState.refs ()
            still branchStill fresh extension
          refine ⟨workResult, h, workState, ?_, workRel, states, submap, allFresh, allUnchanged, allStill, ?_⟩
          · simp only [rewriteWorkerSource]
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
            change (match asBool value' with
              | none => ((.err (.abort .typeError) : BviResult), middleTarget)
              | some true => evaluate [rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length yes] env2 middleTarget
              | some false => evaluate [rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length no] env2 middleTarget) = _
            cases boolean <;> simpa [decoded', selected] using workRun
          · intro resValue success
            obtain ⟨resValue', block, filledHole⟩ := filled resValue success
            refine ⟨resValue', ?_, holeHasVal_submap f g env1 env2 workState.refs resValue' filledHole extension⟩
            exact mutableBlockRel_old_subset h middleTarget.refs (workState.refs.eraseEq holePtr)
              resValue resValue' target.refs block domain

end Flapjack.Compiler.Backend.BviTmc.IfWorker
