import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksRelation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift

/-! Evaluator cases for BVI tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

/-- Flapjack infrastructure: cleaned expressions can be simulated by the
original expressions with enough extra clock, preserving related states. -/
def Property {C F : Type} (xs : List Bvi.Exp) (env : List Value) (target : BviState C F) : Prop :=
  ∀ (source : BviState C F) (result : BviResult) (targetNext : BviState C F),
    RemoveStateRel source target → evaluate (removeTicksListSource xs) env target = (result, targetNext) →
    ∃ extra sourceNext, evaluate xs env { source with clock := source.clock + extra } = (result, sourceNext) ∧
      RemoveStateRel sourceNext targetNext

/-- Flapjack infrastructure: the empty expression list needs no extra clock. -/
theorem nil {C F : Type} (env : List Value) (target : BviState C F) : Property [] env target := by
  intro source result targetNext states run
  simp [removeTicksListSource, evaluate] at run
  obtain ⟨rfl, rfl⟩ := run.symm
  exact ⟨0, source, by simp [evaluate], states⟩

/-- Flapjack infrastructure: variable lookup is unaffected by tick removal. -/
theorem var {C F : Type} (index : Nat) (env : List Value) (target : BviState C F) :
    Property [.var index] env target := by
  intro source result targetNext states run
  cases found : env[index]? with
  | none =>
    simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate, found], states⟩
  | some value =>
    simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate, found], states⟩

/-- Flapjack infrastructure: restoring a removed tick costs exactly one
additional clock unit beyond those required by its body. -/
theorem tick {C F : Type} (body : Bvi.Exp) (env : List Value) (target : BviState C F)
    (bodyIH : Property [body] env target) : Property [.tick body] env target := by
  intro source result targetNext states run
  have bodyRun : evaluate (removeTicksListSource [body]) env target = (result, targetNext) := by
    simpa [removeTicksListSource, removeTicksSource] using run
  obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := bodyIH source result targetNext states bodyRun
  refine ⟨extra + 1, sourceNext, ?_, finalRel⟩
  have nonzero : source.clock + (extra + 1) ≠ 0 := by omega
  have decremented : BviSem.decClock 1 { source with clock := source.clock + (extra + 1) } =
      { source with clock := source.clock + extra } := by
    simp [BviSem.decClock]
  simpa [evaluate, nonzero, decremented] using sourceRun

/-- Flapjack infrastructure: raising a tick-cleaned body propagates the
simulated body result without consuming additional clock. -/
theorem raiseExp {C F : Type} (body : Bvi.Exp) (env : List Value) (target : BviState C F)
    (bodyIH : Property [body] env target) : Property [.raise body] env target := by
  intro source result targetNext states run
  cases bodyRun : evaluate (removeTicksListSource [body]) env target with
  | mk bodyResult bodyNext =>
    obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := bodyIH source bodyResult bodyNext states bodyRun
    have bodyRun' : evaluate [removeTicksSource body] env target = (bodyResult, bodyNext) := by
      simpa [removeTicksListSource] using bodyRun
    cases bodyResult with
    | err error =>
      simp [removeTicksListSource, removeTicksSource, evaluate, bodyRun'] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩
    | val values =>
      simp [removeTicksListSource, removeTicksSource, evaluate, bodyRun'] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩

/-- Flapjack infrastructure: returned values and errors transfer from a
cleaned argument list to the original return expression. -/
theorem returnExp {C F : Type} (args : List Bvi.Exp) (env : List Value) (target : BviState C F)
    (argsIH : Property args env target) : Property [.return args] env target := by
  intro source result targetNext states run
  cases argsRun : evaluate (removeTicksListSource args) env target with
  | mk argsResult argsNext =>
    obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := argsIH source argsResult argsNext states argsRun
    cases argsResult with
    | err error =>
      simp [removeTicksListSource, removeTicksSource, evaluate, argsRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩
    | val values =>
      simp [removeTicksListSource, removeTicksSource, evaluate, argsRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩

/-- Flapjack infrastructure: primitive operations preserve the result and
state relation after their argument expressions are restored. -/
theorem op {C F : Type} (operator : ClosLang.Op) (args : List Bvi.Exp) (env : List Value)
    (target : BviState C F) (argsIH : Property args env target) : Property [.op operator args] env target := by
  intro source result targetNext states run
  cases argsRun : evaluate (removeTicksListSource args) env target with
  | mk argsResult middle =>
    obtain ⟨extra, sourceMiddle, sourceRun, middleRel⟩ := argsIH source argsResult middle states argsRun
    cases argsResult with
    | err error =>
      have targetEq : (.err error, middle) = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource, removeTicksSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨extra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceRun]
    | val values =>
      have operations := removeStateRel_doApp_reverse sourceMiddle middle middleRel operator values.reverse
      cases targetApp : BviSem.doApp operator values.reverse middle with
      | err error =>
        rw [targetApp] at operations
        have targetEq : (.err error, middle) = (result, targetNext) := by
          have h := run
          simp only [removeTicksListSource, removeTicksSource] at h
          rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
          simpa [targetApp] using h
        obtain ⟨rfl, rfl⟩ := targetEq.symm
        refine ⟨extra, sourceMiddle, ?_, middleRel⟩
        rw [evaluate, BviSem.fixClock_evaluate, sourceRun]
        simp [operations]
      | val pair =>
        obtain ⟨value, last⟩ := pair
        rw [targetApp] at operations
        obtain ⟨sourceLast, sourceApp, lastRel⟩ := operations
        have targetEq : (.val [value], last) = (result, targetNext) := by
          have h := run
          simp only [removeTicksListSource, removeTicksSource] at h
          rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
          simpa [targetApp] using h
        obtain ⟨rfl, rfl⟩ := targetEq.symm
        refine ⟨extra, sourceLast, ?_, lastRel⟩
        rw [evaluate, BviSem.fixClock_evaluate, sourceRun]
        simp [sourceApp]

/-- Flapjack infrastructure: sequential list simulation adds the extra
clocks needed by the head and tail, shifting a successful head evaluation. -/
theorem consCons {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (env : List Value) (target : BviState C F) (headIH : Property [first] env target)
    (tailIH : ∀ values middle, evaluate [removeTicksSource first] env target = (.val values, middle) →
      Property (second :: rest) env middle) : Property (first :: second :: rest) env target := by
  intro source result targetNext states run
  cases headRun : evaluate [removeTicksSource first] env target with
  | mk headResult middle =>
    have cleanHead : evaluate (removeTicksListSource [first]) env target = (headResult, middle) := by
      simpa [removeTicksListSource] using headRun
    obtain ⟨headExtra, sourceMiddle, sourceHead, middleRel⟩ := headIH source headResult middle states cleanHead
    cases headResult with
    | err error =>
      have targetEq : (.err error, middle) = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
        exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨headExtra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceHead]
    | val values =>
      cases tailRun : evaluate (removeTicksListSource (second :: rest)) env middle with
      | mk tailResult last =>
        obtain ⟨tailExtra, sourceLast, sourceTail, lastRel⟩ :=
          tailIH values middle headRun sourceMiddle tailResult last middleRel tailRun
        have shiftedHead := BviProps.evaluate_addClock [first] env
          { source with clock := source.clock + headExtra } sourceMiddle (.val values) tailExtra sourceHead (by simp)
        have combinedHead : evaluate [first] env { source with clock := source.clock + (headExtra + tailExtra) } =
            (.val values, { sourceMiddle with clock := sourceMiddle.clock + tailExtra }) := by
          simpa [Nat.add_assoc] using shiftedHead
        have h := run
        simp only [removeTicksListSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, headRun] at h
        simp only at h
        have tailRun' : evaluate (removeTicksSource second :: removeTicksListSource rest) env middle =
            (tailResult, last) := by simpa [removeTicksListSource] using tailRun
        rw [tailRun'] at h
        cases tailResult with
        | err error =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h.symm
          refine ⟨headExtra + tailExtra, sourceLast, ?_, lastRel⟩
          rw [evaluate, BviSem.fixClock_evaluate, combinedHead]
          simp only
          rw [sourceTail]
        | val tail =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h.symm
          refine ⟨headExtra + tailExtra, sourceLast, ?_, lastRel⟩
          rw [evaluate, BviSem.fixClock_evaluate, combinedHead]
          simp only
          rw [sourceTail]

/-- Flapjack infrastructure: let bindings and their continuation combine
their individual clock requirements without changing the returned result. -/
theorem letExp {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (target : BviState C F) (bindingsIH : Property bindings env target)
    (bodyIH : ∀ values middle, evaluate (removeTicksListSource bindings) env target = (.val values, middle) →
      Property [body] (values ++ env) middle) : Property [.let bindings body] env target := by
  intro source result targetNext states run
  cases bindingsRun : evaluate (removeTicksListSource bindings) env target with
  | mk bindingResult middle =>
    obtain ⟨bindingExtra, sourceMiddle, sourceBindings, middleRel⟩ :=
      bindingsIH source bindingResult middle states bindingsRun
    cases bindingResult with
    | err error =>
      have targetEq : (.err error, middle) = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource, removeTicksSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
        exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨bindingExtra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceBindings]
    | val values =>
      have bodyRun : evaluate (removeTicksListSource [body]) (values ++ env) middle = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource, removeTicksSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, bindingsRun] at h
        simpa [removeTicksListSource] using h
      obtain ⟨bodyExtra, sourceLast, sourceBody, lastRel⟩ :=
        bodyIH values middle bindingsRun sourceMiddle result targetNext middleRel bodyRun
      have shiftedBindings := BviProps.evaluate_addClock bindings env
        { source with clock := source.clock + bindingExtra } sourceMiddle (.val values)
          bodyExtra sourceBindings (by simp)
      have combinedBindings : evaluate bindings env { source with clock := source.clock + (bindingExtra + bodyExtra) } =
          (.val values, { sourceMiddle with clock := sourceMiddle.clock + bodyExtra }) := by
        simpa [Nat.add_assoc] using shiftedBindings
      refine ⟨bindingExtra + bodyExtra, sourceLast, ?_, lastRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, combinedBindings]
      exact sourceBody

/-- Flapjack infrastructure: cleaned conditionals evaluate the same boolean
and take the same branch after restoring the condition's required clock. -/
theorem ifThenElse {C F : Type} (condition yes no : Bvi.Exp) (env : List Value)
    (target : BviState C F) (conditionIH : Property [condition] env target)
    (branchIH : ∀ value middle, evaluate [removeTicksSource condition] env target = (.val [value], middle) →
      Property [yes] env middle ∧ Property [no] env middle) :
    Property [.ifThenElse condition yes no] env target := by
  intro source result targetNext states run
  cases conditionRun : evaluate [removeTicksSource condition] env target with
  | mk conditionResult middle =>
    have cleanCondition : evaluate (removeTicksListSource [condition]) env target = (conditionResult, middle) := by
      simpa [removeTicksListSource] using conditionRun
    obtain ⟨conditionExtra, sourceMiddle, sourceCondition, middleRel⟩ :=
      conditionIH source conditionResult middle states cleanCondition
    cases conditionResult with
    | err error =>
      have targetEq : (.err error, middle) = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource, removeTicksSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, conditionRun] at h
        exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨conditionExtra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceCondition]
    | val values =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (removeTicksSource condition) env target middle values conditionRun
      have targetIf : evaluate (removeTicksListSource [.ifThenElse condition yes no]) env target =
          (match BvlSem.asBool value with
            | none => ((.err (.abort .typeError) : BviResult), middle)
            | some true => evaluate [removeTicksSource yes] env middle
            | some false => evaluate [removeTicksSource no] env middle) := by
        simp only [removeTicksListSource, removeTicksSource]
        rw [evaluate, BviSem.fixClock_evaluate, conditionRun]
        rfl
      rw [targetIf] at run
      cases selected : BvlSem.asBool value with
      | none =>
        simp only [selected] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨conditionExtra, sourceMiddle, ?_, middleRel⟩
        rw [evaluate, BviSem.fixClock_evaluate, sourceCondition]
        change (match BvlSem.asBool value with
          | none => ((.err (.abort .typeError) : BviResult), sourceMiddle)
          | some true => evaluate [yes] env sourceMiddle
          | some false => evaluate [no] env sourceMiddle) = _
        simp [selected]
      | some choice =>
        cases choice with
        | false =>
          have branchRun : evaluate (removeTicksListSource [no]) env middle = (result, targetNext) := by
            simpa [selected, removeTicksListSource] using run
          obtain ⟨branchExtra, sourceLast, sourceBranch, lastRel⟩ :=
            (branchIH value middle conditionRun).2 sourceMiddle result targetNext middleRel branchRun
          have shifted := BviProps.evaluate_addClock [condition] env
            { source with clock := source.clock + conditionExtra } sourceMiddle (.val [value])
              branchExtra sourceCondition (by simp)
          have combined : evaluate [condition] env { source with clock := source.clock + (conditionExtra + branchExtra) } =
              (.val [value], { sourceMiddle with clock := sourceMiddle.clock + branchExtra }) := by
            simpa [Nat.add_assoc] using shifted
          refine ⟨conditionExtra + branchExtra, sourceLast, ?_, lastRel⟩
          rw [evaluate, BviSem.fixClock_evaluate, combined]
          change (match BvlSem.asBool value with
            | none => ((.err (.abort .typeError) : BviResult), { sourceMiddle with clock := sourceMiddle.clock + branchExtra })
            | some true => evaluate [yes] env { sourceMiddle with clock := sourceMiddle.clock + branchExtra }
            | some false => evaluate [no] env { sourceMiddle with clock := sourceMiddle.clock + branchExtra }) = _
          simpa [selected] using sourceBranch
        | true =>
          have branchRun : evaluate (removeTicksListSource [yes]) env middle = (result, targetNext) := by
            simpa [selected, removeTicksListSource] using run
          obtain ⟨branchExtra, sourceLast, sourceBranch, lastRel⟩ :=
            (branchIH value middle conditionRun).1 sourceMiddle result targetNext middleRel branchRun
          have shifted := BviProps.evaluate_addClock [condition] env
            { source with clock := source.clock + conditionExtra } sourceMiddle (.val [value])
              branchExtra sourceCondition (by simp)
          have combined : evaluate [condition] env { source with clock := source.clock + (conditionExtra + branchExtra) } =
              (.val [value], { sourceMiddle with clock := sourceMiddle.clock + branchExtra }) := by
            simpa [Nat.add_assoc] using shifted
          refine ⟨conditionExtra + branchExtra, sourceLast, ?_, lastRel⟩
          rw [evaluate, BviSem.fixClock_evaluate, combined]
          change (match BvlSem.asBool value with
            | none => ((.err (.abort .typeError) : BviResult), { sourceMiddle with clock := sourceMiddle.clock + branchExtra })
            | some true => evaluate [yes] env { sourceMiddle with clock := sourceMiddle.clock + branchExtra }
            | some false => evaluate [no] env { sourceMiddle with clock := sourceMiddle.clock + branchExtra }) = _
          simpa [selected] using sourceBranch

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
