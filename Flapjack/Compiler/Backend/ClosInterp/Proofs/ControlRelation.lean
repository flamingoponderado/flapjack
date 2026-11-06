import Flapjack.Compiler.Backend.ClosInterp.Proofs.ApplicationRelation

/-! Control-flow simulation for the proof-side evaluator. The evaluator and
state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Let evaluation preserves the state relation from its binding-list and
body simulations. -/
theorem evaluate_let_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bindingsIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate bindings env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate bindings env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (bodyIH : ∀ (values : List ClosSem.Value) (bodySource bodyTarget bodyFinal : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      bodySource.clock ≤ source.clock → ClosSem.evaluate [body] (values ++ env) bodySource = (bodyResult, bodyFinal) →
      StateRel bodySource bodyTarget → bodyResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [body] (values ++ env) { bodyTarget with clock := extra + bodyTarget.clock } =
        (bodyResult, targetFinal) ∧ StateRel bodyFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.let trace bindings body] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.let trace bindings body] env { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases bindingsRun : ClosSem.evaluate bindings env source with
  | mk bindingResult sourceMid =>
    have bindingNotTypeError : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨bindingsExtra, targetMid, targetBindings, midRel⟩ :=
      bindingsIH target sourceMid bindingResult bindingsRun related bindingNotTypeError
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨bindingsExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBindings]
    | val values =>
      have sourceBound : sourceMid.clock ≤ source.clock := by
        have bound := ClosSem.evaluate_clock_le bindings env source
        simpa [bindingsRun] using bound
      obtain ⟨bodyExtra, targetFinal, targetBody, finalRel⟩ :=
        bodyIH values sourceMid targetMid sourceFinal result sourceBound run midRel notTypeError
      have shiftedBindings := ClosSem.evaluate_addClock.1 bindings env
        { target with clock := bindingsExtra + target.clock } targetMid (.val values) bodyExtra targetBindings (by simp)
      let enlarged := { target with clock := (bindingsExtra + target.clock) + bodyExtra }
      let enlargedMid := { targetMid with clock := targetMid.clock + bodyExtra }
      have bindingsRun' : ClosSem.evaluate bindings env enlarged = (.val values, enlargedMid) := by
        simpa [enlarged, enlargedMid] using shiftedBindings
      have bodyRun' : ClosSem.evaluate [body] (values ++ env) enlargedMid = (result, targetFinal) := by
        simpa [enlargedMid, Nat.add_comm] using targetBody
      refine ⟨bindingsExtra + bodyExtra, targetFinal, ?_, finalRel⟩
      have targetRun : ClosSem.evaluate [.let trace bindings body] env enlarged = (result, targetFinal) := by
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun']
        exact bodyRun'
      simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

/-- Nonempty expression-list simulation from the head and tail hypotheses. -/
theorem evaluate_cons_simulation_step {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (headIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [head] env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (tailIH : ∀ (tailSource tailTarget tailFinal : ClosSem.State C F) (tailResult : Result (List ClosSem.Value) ClosSem.Value),
      tailSource.clock ≤ source.clock → ClosSem.evaluate tail env tailSource = (tailResult, tailFinal) →
      StateRel tailSource tailTarget → tailResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate tail env { tailTarget with clock := extra + tailTarget.clock } =
        (tailResult, targetFinal) ∧ StateRel tailFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate (head :: tail) env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate (head :: tail) env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases headRun : ClosSem.evaluate [head] env source with
  | mk headResult sourceMid =>
    cases headResult with
    | err error =>
      have sourceError := ClosProps.evaluate_cons_error head tail env source sourceMid error headRun
      rw [sourceError] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
        headIH target sourceMid (.err error) headRun related notTypeError
      refine ⟨extra, targetFinal, ?_, finalRel⟩
      exact ClosProps.evaluate_cons_error head tail env _ targetFinal error targetRun
    | val headValues =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head env source sourceMid headValues headRun
      cases tailRun : ClosSem.evaluate tail env sourceMid with
      | mk tailResult last =>
        have sourceSequence := ClosProps.evaluate_cons_value head tail env source sourceMid value headRun
        rw [tailRun] at sourceSequence
        have tailNotTypeError : tailResult ≠ .err (.abort .typeError) := by
          intro bad
          subst tailResult
          simp at sourceSequence
          rw [sourceSequence] at run
          simp at run
          exact notTypeError run.1.symm
        obtain ⟨headExtra, targetMid, targetHead, midRel⟩ :=
          headIH target sourceMid (.val [value]) headRun related (by simp)
        have sourceBound : sourceMid.clock ≤ source.clock := by
          have bound := ClosSem.evaluate_clock_le [head] env source
          simpa [headRun] using bound
        obtain ⟨tailExtra, targetFinal, targetTail, finalRel⟩ :=
          tailIH sourceMid targetMid last tailResult sourceBound tailRun midRel tailNotTypeError
        have shiftedHead := ClosSem.evaluate_addClock.1 [head] env
          { target with clock := headExtra + target.clock } targetMid (.val [value]) tailExtra targetHead (by simp)
        let enlarged := { target with clock := (headExtra + target.clock) + tailExtra }
        let enlargedMid := { targetMid with clock := targetMid.clock + tailExtra }
        have headRun' : ClosSem.evaluate [head] env enlarged = (.val [value], enlargedMid) := by
          simpa [enlarged, enlargedMid] using shiftedHead
        have tailRun' : ClosSem.evaluate tail env enlargedMid = (tailResult, targetFinal) := by
          simpa [enlargedMid, Nat.add_comm] using targetTail
        have targetSequence := ClosProps.evaluate_cons_value head tail env enlarged enlargedMid value headRun'
        rw [tailRun'] at targetSequence
        rw [sourceSequence] at run
        cases tailResult with
        | err error =>
          simp at run targetSequence
          rcases run with ⟨rfl, rfl⟩
          refine ⟨headExtra + tailExtra, targetFinal, ?_, finalRel⟩
          simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetSequence
        | val values =>
          simp at run targetSequence
          rcases run with ⟨rfl, rfl⟩
          refine ⟨headExtra + tailExtra, targetFinal, ?_, finalRel⟩
          simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetSequence

/-- Raising an evaluated value preserves simulation of the child expression. -/
theorem evaluate_raise_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [body] env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate [.raise trace body] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.raise trace body] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases bodyRun : ClosSem.evaluate [body] env source with
  | mk bodyResult sourceMid =>
    rw [ClosSem.evaluate, bodyRun] at run
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨extra, targetFinal, targetBody, finalRel⟩ := bodyIH target sourceMid bodyResult bodyRun related bodyNotTypeError
    cases bodyResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨extra, targetFinal, ?_, finalRel⟩
      rw [ClosSem.evaluate, targetBody]
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨extra, targetFinal, ?_, finalRel⟩
      rw [ClosSem.evaluate, targetBody]

/-- Conditional evaluation preserves simulation of its test and chosen branch. -/
theorem evaluate_if_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (conditionIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [condition] env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [condition] env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (branchIH : ∀ (choice : Bool) (branchSource branchTarget branchFinal : ClosSem.State C F)
      (branchResult : Result (List ClosSem.Value) ClosSem.Value),
      branchSource.clock ≤ source.clock → ClosSem.evaluate [if choice then yes else no] env branchSource = (branchResult, branchFinal) →
      StateRel branchSource branchTarget → branchResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [if choice then yes else no] env { branchTarget with clock := extra + branchTarget.clock } =
        (branchResult, targetFinal) ∧ StateRel branchFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate [.ifThenElse trace condition yes no] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.ifThenElse trace condition yes no] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases conditionRun : ClosSem.evaluate [condition] env source with
  | mk conditionResult sourceMid =>
    have conditionNotTypeError : conditionResult ≠ .err (.abort .typeError) := by
      intro bad
      subst conditionResult
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, conditionRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨conditionExtra, targetMid, targetCondition, midRel⟩ :=
      conditionIH target sourceMid conditionResult conditionRun related conditionNotTypeError
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, conditionRun] at run
    cases conditionResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨conditionExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetCondition]
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value condition env source sourceMid values conditionRun
      change (match ClosSem.asBool value with
        | none => (.err (.abort .typeError), sourceMid)
        | some true => ClosSem.evaluate [yes] env sourceMid
        | some false => ClosSem.evaluate [no] env sourceMid) = (result, sourceFinal) at run
      cases decoded : ClosSem.asBool value with
      | none =>
        rw [decoded] at run
        simp at run
        exact (notTypeError run.1.symm).elim
      | some choice =>
        rw [decoded] at run
        have sourceBound : sourceMid.clock ≤ source.clock := by
          have bound := ClosSem.evaluate_clock_le [condition] env source
          simpa [conditionRun] using bound
        have branchRun : ClosSem.evaluate [if choice then yes else no] env sourceMid = (result, sourceFinal) := by
          cases choice <;> exact run
        obtain ⟨branchExtra, targetFinal, targetBranch, finalRel⟩ :=
          branchIH choice sourceMid targetMid sourceFinal result sourceBound branchRun midRel notTypeError
        have shiftedCondition := ClosSem.evaluate_addClock.1 [condition] env
          { target with clock := conditionExtra + target.clock } targetMid (.val [value]) branchExtra targetCondition (by simp)
        let enlarged := { target with clock := (conditionExtra + target.clock) + branchExtra }
        let enlargedMid := { targetMid with clock := targetMid.clock + branchExtra }
        have conditionRun' : ClosSem.evaluate [condition] env enlarged = (.val [value], enlargedMid) := by
          simpa [enlarged, enlargedMid] using shiftedCondition
        have branchRun' : ClosSem.evaluate [if choice then yes else no] env enlargedMid = (result, targetFinal) := by
          simpa [enlargedMid, Nat.add_comm] using targetBranch
        refine ⟨conditionExtra + branchExtra, targetFinal, ?_, finalRel⟩
        have targetRun : ClosSem.evaluate [.ifThenElse trace condition yes no] env enlarged = (result, targetFinal) := by
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, conditionRun']
          change (match ClosSem.asBool value with
            | none => (.err (.abort .typeError), enlargedMid)
            | some true => ClosSem.evaluate [yes] env enlargedMid
            | some false => ClosSem.evaluate [no] env enlargedMid) = (result, targetFinal)
          rw [decoded]
          cases choice <;> exact branchRun'
        simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

/-- Handler evaluation preserves simulation of its body and handler. -/
theorem evaluate_handle_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [body] env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (handlerIH : ∀ (value : ClosSem.Value) (handlerSource handlerTarget handlerFinal : ClosSem.State C F)
      (handlerResult : Result (List ClosSem.Value) ClosSem.Value),
      handlerSource.clock ≤ source.clock → ClosSem.evaluate [handler] (value :: env) handlerSource = (handlerResult, handlerFinal) →
      StateRel handlerSource handlerTarget → handlerResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [handler] (value :: env) { handlerTarget with clock := extra + handlerTarget.clock } =
        (handlerResult, targetFinal) ∧ StateRel handlerFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate [.handle trace body handler] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.handle trace body handler] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases bodyRun : ClosSem.evaluate [body] env source with
  | mk bodyResult sourceMid =>
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨bodyExtra, targetMid, targetBody, midRel⟩ := bodyIH target sourceMid bodyResult bodyRun related bodyNotTypeError
    by_cases raises : ∃ value, bodyResult = .err (.raise value)
    · obtain ⟨value, rfl⟩ := raises
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun] at run
      have sourceBound : sourceMid.clock ≤ source.clock := by
        have bound := ClosSem.evaluate_clock_le [body] env source
        simpa [bodyRun] using bound
      obtain ⟨handlerExtra, targetFinal, targetHandler, finalRel⟩ :=
        handlerIH value sourceMid targetMid sourceFinal result sourceBound run midRel notTypeError
      have shiftedBody := ClosSem.evaluate_addClock.1 [body] env
        { target with clock := bodyExtra + target.clock } targetMid (.err (.raise value)) handlerExtra targetBody (by simp)
      let enlarged := { target with clock := (bodyExtra + target.clock) + handlerExtra }
      let enlargedMid := { targetMid with clock := targetMid.clock + handlerExtra }
      have bodyRun' : ClosSem.evaluate [body] env enlarged = (.err (.raise value), enlargedMid) := by
        simpa [enlarged, enlargedMid] using shiftedBody
      have handlerRun' : ClosSem.evaluate [handler] (value :: env) enlargedMid = (result, targetFinal) := by
        simpa [enlargedMid, Nat.add_comm] using targetHandler
      refine ⟨bodyExtra + handlerExtra, targetFinal, ?_, finalRel⟩
      have targetRun : ClosSem.evaluate [.handle trace body handler] env enlarged = (result, targetFinal) := by
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun']
        exact handlerRun'
      simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun
    · have notRaise : ∀ value, bodyResult ≠ .err (.raise value) := by
        intro value equal
        exact raises ⟨value, equal⟩
      have sourcePass : ClosSem.evaluate [.handle trace body handler] env source = (bodyResult, sourceMid) := by
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun]
        cases bodyResult with
        | val values => rfl
        | err error =>
          cases error with
          | abort reason => rfl
          | raise value => exact (notRaise value rfl).elim
      rw [sourcePass] at run
      cases run
      refine ⟨bodyExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBody]
      cases result with
      | val values => rfl
      | err error =>
        cases error with
        | abort reason => rfl
        | raise value => exact (notRaise value rfl).elim

/-- Tick evaluation preserves the state relation, using the body simulation
at the decremented clock. -/
theorem evaluate_tick_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (bodySource bodyTarget bodyFinal : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      bodySource.clock < source.clock → ClosSem.evaluate [body] env bodySource = (bodyResult, bodyFinal) →
      StateRel bodySource bodyTarget → bodyResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [body] env { bodyTarget with clock := extra + bodyTarget.clock } =
        (bodyResult, targetFinal) ∧ StateRel bodyFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate [.tick trace body] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.tick trace body] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
  by_cases zero : source.clock = 0
  · simp [ClosSem.evaluate, zero] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨0, target, ?_, related⟩
    have targetZero : target.clock = 0 := clockEq.trans zero
    simp [ClosSem.evaluate, targetZero]
    cases target
    simp_all
  · have bodyRun : ClosSem.evaluate [body] env (ClosSem.decClock 1 source) = (result, sourceFinal) := by
      simpa [ClosSem.evaluate, zero] using run
    have smaller : (ClosSem.decClock 1 source).clock < source.clock := by simp [ClosSem.decClock]; omega
    obtain ⟨extra, targetFinal, targetBody, finalRel⟩ :=
      bodyIH (ClosSem.decClock 1 source) (ClosSem.decClock 1 target) sourceFinal result smaller bodyRun
        (stateRel_decClock source target related 1) notTypeError
    have clocks : ClosSem.decClock 1 { target with clock := extra + target.clock } =
        { ClosSem.decClock 1 target with clock := extra + (ClosSem.decClock 1 target).clock } := by
      simp only [ClosSem.decClock]
      congr 1
      omega
    refine ⟨extra, targetFinal, ?_, finalRel⟩
    rw [ClosSem.evaluate]
    rw [if_neg (show ¬ ({ target with clock := extra + target.clock } : ClosSem.State C F).clock = 0 by simp only; omega)]
    rw [clocks]
    exact targetBody

/-- Variable lookup agrees in related states. -/
theorem evaluate_var_simulation {C F : Type} (trace : BackendCommon.Tra)
    (index : Nat) (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (related : StateRel source target) (run : ClosSem.evaluate [.var trace index] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.var trace index] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases found : env[index]? with
  | none =>
    simp [ClosSem.evaluate, found] at run
    exact (notTypeError run.1.symm).elim
  | some value =>
    simp [ClosSem.evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨0, target, ?_, related⟩
    simp [ClosSem.evaluate, found]

/-- Closure creation agrees in related states. -/
theorem evaluate_fn_simulation {C F : Type} (name : Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (related : StateRel source target) (run : ClosSem.evaluate [.fn name location selected arity body] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.fn name location selected arity body] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simp [ClosSem.evaluate.eq_def, arityOk] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨0, target, ?_, related⟩
      simp [ClosSem.evaluate.eq_def, maxEq, arityOk]
      cases target
      simp_all
    | some names =>
      cases captured : ClosSem.lookupVars names env with
      | none =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        exact (notTypeError run.1.symm).elim
      | some values =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨0, target, ?_, related⟩
        simp [ClosSem.evaluate.eq_def, maxEq, arityOk, captured]
        cases target
        simp_all
  · simp [ClosSem.evaluate.eq_def, arityOk] at run
    exact (notTypeError run.1.symm).elim

/-- Recursive-binding evaluation preserves simulation of the body. -/
theorem evaluate_letrec_simulation_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (newEnv : List ClosSem.Value) (target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] newEnv source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [body] newEnv { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.letrec names location selected functions body] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.letrec names location selected functions body] env
      { target with clock := extra + target.clock } = (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  by_cases good : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      rw [ClosSem.evaluate.eq_def] at run
      dsimp only at run
      rw [if_pos good] at run
      let recursive := (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] env functions i)
      obtain ⟨extra, targetFinal, targetBody, finalRel⟩ := bodyIH (recursive ++ env) target sourceFinal result run related notTypeError
      refine ⟨extra, targetFinal, ?_, finalRel⟩
      rw [ClosSem.evaluate.eq_def]
      dsimp only
      rw [if_pos (by simpa [maxEq] using good)]
      exact targetBody
    | some selected =>
      cases captured : ClosSem.lookupVars selected env with
      | none =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        simp at run
        exact (notTypeError run.1.symm).elim
      | some values =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        dsimp only at run
        let recursive := (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] values functions i)
        obtain ⟨extra, targetFinal, targetBody, finalRel⟩ := bodyIH (recursive ++ env) target sourceFinal result run related notTypeError
        refine ⟨extra, targetFinal, ?_, finalRel⟩
        rw [ClosSem.evaluate.eq_def]
        dsimp only
        rw [if_pos (by simpa [maxEq] using good), captured]
        exact targetBody
  · rw [ClosSem.evaluate.eq_def] at run
    dsimp only at run
    rw [if_neg good] at run
    simp at run
    exact (notTypeError run.1.symm).elim

/-- Direct calls in related states either propagate an argument error or
encounter the excluded type error, because related code maps are empty. -/
theorem evaluate_call_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate args env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (related : StateRel source target) (run : ClosSem.evaluate [.call trace ticks location args] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal, ClosSem.evaluate [.call trace ticks location args] env { target with clock := extra + target.clock } =
      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases argsRun : ClosSem.evaluate args env source with
  | mk argsResult sourceMid =>
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
    have argsNotTypeError : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨extra, targetMid, targetArgs, midRel⟩ := argsIH target sourceMid argsResult argsRun related argsNotTypeError
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨extra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
    | val values =>
      have emptyCode := midRel.1.2.1
      simp [ClosSem.findCode, emptyCode] at run
      exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.ClosInterp
