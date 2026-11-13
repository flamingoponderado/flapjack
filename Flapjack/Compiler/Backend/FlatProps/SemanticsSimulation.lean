module

public import Flapjack.Compiler.Backend.FlatProps.InitialClock
public import Flapjack.Compiler.Backend.FlatProps.EvalSim

@[expose] public section
/-! Observational semantics preservation from flat evaluation simulation.
Private helper lemmas structure the original proof and have no separate HOL declarations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (ErrorResult Abort)
private def traceFamily {C F : Type} (ec : InstallConfig C) (ffi : HolFfiState F)
    (ds : List FlatLang.Exp) : HolLList HolIoEvent → Prop :=
  fun trace => ∃ clock, trace = HolLList.fromList (evaluateDecs (initialState ffi clock ec) ds).1.ffi.ioEvents
private theorem traceFamily_chain {C F : Type} (ec : InstallConfig C) (ffi : HolFfiState F)
    (ds : List FlatLang.Exp) : HolLList.lprefixChain (traceFamily ec ffi ds) := by
  intro a b ha hb
  obtain ⟨k, hk⟩ := ha
  obtain ⟨j, hj⟩ := hb
  subst a
  subst b
  cases Nat.le_total k j with
  | inl le =>
    left
    apply (HolLList.lprefix_fromList _ _).mpr
    have ev := evaluateDecs_addToClock_ioEventsMono ds (initialState ffi k ec) (j-k)
    simpa [initialState, Nat.add_sub_of_le le] using ev
  | inr le =>
    right
    apply (HolLList.lprefix_fromList _ _).mpr
    have ev := evaluateDecs_addToClock_ioEventsMono ds (initialState ffi j ec) (k-j)
    simpa [initialState, Nat.add_sub_of_le le] using ev

private theorem traceFamily_sim {C₁ C₂ F : Type} (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (ec : InstallConfig C₁) (ec2 : InstallConfig C₂)
    (rel : List FlatLang.Exp → List FlatLang.Exp → Prop)
    (sim : evalSim ffi source target ec ec2 rel false) (related : rel source target)
    (safe : ∀ k, (evaluateDecs (initialState ffi k ec) source).2 ≠ some (.abort .typeError)) :
    HolLList.lprefixRel (traceFamily ec ffi source) (traceFamily ec2 ffi target) ∧
    HolLList.lprefixRel (traceFamily ec2 ffi target) (traceFamily ec ffi source) := by
  constructor
  · intro ll ⟨k, equal⟩
    subst ll
    let run := evaluateDecs (initialState ffi k ec) source
    obtain ⟨extra, result, next, targetRun, ffiEq, _, _, _⟩ :=
      sim k run.2 run.1 ⟨rfl, Or.inr (safe k), related⟩
    refine ⟨HolLList.fromList (evaluateDecs (initialState ffi (k + extra) ec2) target).1.ffi.ioEvents,
      ⟨k + extra, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).mpr
    simp only [targetRun]
    simpa only [← ffiEq] using (List.prefix_refl run.1.ffi.ioEvents)
  · intro ll ⟨k, equal⟩
    subst ll
    let run := evaluateDecs (initialState ffi k ec) source
    obtain ⟨extra, result, next, targetRun, ffiEq, _, _, _⟩ :=
      sim k run.2 run.1 ⟨rfl, Or.inr (safe k), related⟩
    refine ⟨HolLList.fromList (evaluateDecs (initialState ffi k ec) source).1.ffi.ioEvents,
      ⟨k, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).mpr
    have ev := evaluateDecs_addToClock_initialState_ioEventsMono ffi k ec2 target
      (evaluateDecs (initialState ffi k ec2) target).1
      (evaluateDecs (initialState ffi k ec2) target).2 extra rfl
    rw [targetRun] at ev
    simpa [← ffiEq] using ev

private theorem simulation_target_safe {C₁ C₂ F : Type} (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (ec : InstallConfig C₁) (ec2 : InstallConfig C₂)
    (rel : List FlatLang.Exp → List FlatLang.Exp → Prop)
    (sim : evalSim ffi source target ec ec2 rel false) (related : rel source target)
    (safe : ∀ k, (evaluateDecs (initialState ffi k ec) source).2 ≠ some (.abort .typeError)) :
    ∀ k, (evaluateDecs (initialState ffi k ec2) target).2 ≠ some (.abort .typeError) := by
  intro k bad
  cases sourceRun : evaluateDecs (initialState ffi k ec) source with
  | mk sourceState sourceResult =>
    have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa [sourceRun] using safe k
    obtain ⟨extra, result, next, targetRun, ffiEq, noneCase, raiseCase, abortCase⟩ :=
      sim k sourceResult sourceState ⟨sourceRun, Or.inr sourceSafe, related⟩
    cases initialTarget : evaluateDecs (initialState ffi k ec2) target with
    | mk targetState targetResult =>
      have targetResultEq : targetResult = some (.abort .typeError) := by simpa [initialTarget] using bad
      subst targetResult
      have shifted := evaluateDecs_addToClock_initialState (some (.abort .typeError)) ffi k ec2 target targetState extra
        ⟨by simp, initialTarget⟩
      have eqResult : result = some (.abort .typeError) := by
        have same := targetRun.symm.trans (by simpa [Nat.add_comm] using shifted)
        exact congrArg Prod.snd same
      cases sourceResult with
      | none => simp_all
      | some error =>
        cases error with
        | raise value =>
          obtain ⟨targetValue, raised⟩ := raiseCase value rfl
          simp_all
        | abort reason =>
          have matched := abortCase reason rfl
          cases reason <;> simp_all

private def resultOutcome (r : Option (ErrorResult Value)) (outcome : HolOutcome) : Prop :=
  match r, outcome with
  | some (.abort (.ffiError event)), outcome => outcome = .ffiOutcome event
  | some (.abort _), _ => False
  | _, outcome => outcome = .success

private theorem resultOutcome_sim (source target : Option (ErrorResult Value))
    (noneCase : source = none → target = none)
    (raiseCase : ∀ v, source = some (.raise v) → ∃ v', target = some (.raise v'))
    (abortCase : ∀ a, source = some (.abort a) → target = some (.abort a))
    (outcome : HolOutcome) : resultOutcome source outcome ↔ resultOutcome target outcome := by
  cases source with
  | none =>
    have targetNone := noneCase rfl
    simp [resultOutcome, targetNone]
  | some error =>
    cases error with
    | raise value =>
      obtain ⟨value', eq⟩ := raiseCase value rfl
      simp [resultOutcome, eq]
    | abort reason =>
      have eq := abortCase reason rfl
      simp [resultOutcome, eq]

private theorem simulation_terminating {C₁ C₂ F : Type} (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (ec : InstallConfig C₁) (ec2 : InstallConfig C₂)
    (rel : List FlatLang.Exp → List FlatLang.Exp → Prop)
    (sim : evalSim ffi source target ec ec2 rel false) (related : rel source target)
    (safe : ∀ k, (evaluateDecs (initialState ffi k ec) source).2 ≠ some (.abort .typeError)) :
    ∀ behavior, terminatingObservation ec ffi source behavior ↔ terminatingObservation ec2 ffi target behavior := by
  intro behavior
  constructor
  · rintro ⟨k, sourceState, sourceResult, outcome, sourceRun, out, shape⟩
    have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa [sourceRun] using safe k
    obtain ⟨extra, targetResult, targetState, targetRun, ffiEq, noneCase, raiseCase, abortCase⟩ :=
      sim k sourceResult sourceState ⟨sourceRun, Or.inr sourceSafe, related⟩
    refine ⟨k + extra, targetState, targetResult, outcome, targetRun, ?_, ?_⟩
    · exact (resultOutcome_sim sourceResult targetResult noneCase raiseCase abortCase outcome).mp out
    · simpa [ffiEq] using shape
  · rintro ⟨k, targetState, targetResult, outcome, targetRun, out, shape⟩
    have notTimeout : targetResult ≠ some (.abort .timeoutError) := by
      intro equal
      subst targetResult
      simp at out
    cases sourceRun : evaluateDecs (initialState ffi k ec) source with
    | mk sourceState sourceResult =>
      have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa [sourceRun] using safe k
      obtain ⟨extra, result, next, targetRun', ffiEq, noneCase, raiseCase, abortCase⟩ :=
        sim k sourceResult sourceState ⟨sourceRun, Or.inr sourceSafe, related⟩
      have shifted := evaluateDecs_addToClock_initialState targetResult ffi k ec2 target targetState extra
        ⟨notTimeout, targetRun⟩
      have same := targetRun'.symm.trans (by simpa [Nat.add_comm] using shifted)
      have resultEq : result = targetResult := congrArg Prod.snd same
      have ffiEq' : sourceState.ffi = targetState.ffi := by
        have stateEq := congrArg Prod.fst same
        simp only at stateEq
        rw [stateEq] at ffiEq
        exact ffiEq
      refine ⟨k, sourceState, sourceResult, outcome, sourceRun, ?_, ?_⟩
      · apply (resultOutcome_sim sourceResult result noneCase raiseCase abortCase outcome).mpr
        have out' : resultOutcome targetResult outcome := by
          cases targetResult with
          | none => exact out
          | some error =>
            cases error with
            | raise value => exact out
            | abort reason => cases reason <;> exact out
        simpa [resultEq] using out'
      · simpa [ffiEq'] using shape

/-- A non-failing source and its evaluation simulation have identical observations. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "IMP_semantics_eq"]
theorem imp_semanticsEq {C₁ C₂ F : Type} (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (ec : InstallConfig C₁) (ec2 : InstallConfig C₂)
    (rel : List FlatLang.Exp → List FlatLang.Exp → Prop)
    (h : evalSim ffi source target ec ec2 rel false ∧ semantics ec ffi source ≠ .fail)
    (related : rel source target) : semantics ec ffi source = semantics ec2 ffi target := by
  obtain ⟨sim, notFail⟩ := h
  have sourceSafe : ∀ k, (evaluateDecs (initialState ffi k ec) source).2 ≠ some (.abort .typeError) := by
    intro k bad
    apply notFail
    unfold semantics
    simp only [show ∃ clock, (evaluateDecs (initialState ffi clock ec) source).2 = some (.abort .typeError) from ⟨k, bad⟩, ite_true]
  have targetSafe := simulation_target_safe ffi source target ec ec2 rel sim related sourceSafe
  have observations : terminatingObservation ec ffi source = terminatingObservation ec2 ffi target := by
    funext behavior
    exact propext (simulation_terminating ffi source target ec ec2 rel sim related sourceSafe behavior)
  have relations := traceFamily_sim ffi source target ec ec2 rel sim related sourceSafe
  have lubs := HolLList.IMP_build_lprefix_lub_EQ (traceFamily_chain ec ffi source)
    (traceFamily_chain ec2 ffi target) relations.1 relations.2
  unfold traceFamily at lubs
  unfold semantics
  simp only [show ¬ ∃ k, (evaluateDecs (initialState ffi k ec) source).2 = some (.abort .typeError) from
      fun ⟨k, bad⟩ => sourceSafe k bad,
    show ¬ ∃ k, (evaluateDecs (initialState ffi k ec2) target).2 = some (.abort .typeError) from
      fun ⟨k, bad⟩ => targetSafe k bad, ite_false]
  rw [observations]
  cases holOptionSome (terminatingObservation ec2 ffi target) with
  | some behavior => rfl
  | none => exact congrArg HolBehaviour.diverge lubs
end Flapjack.Compiler.Backend.FlatProps
