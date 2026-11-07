import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Declaration sequencing for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Declaration evaluation either succeeds with any target value list, or
returns related exceptions and identical aborts. -/
inductive DecResultRel : Option (ErrorResult FlatSem.Value) →
    Result (List ClosSem.Value) ClosSem.Value → Prop where
  | success (values : List ClosSem.Value) : DecResultRel none (.val values)
  | raise {source target} (related : ValueRel source target) :
      DecResultRel (some (.raise source)) (.err (.raise target))
  | abort (error : Abort) : DecResultRel (some (.abort error)) (.err (.abort error))

/-- Simulation of a list of top-level declarations. -/
def DecSim {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (declarations : List FlatLang.Exp) : Prop :=
  let flat := FlatSem.evaluateDecs source declarations
  let clos := ClosSem.evaluate (compileDecs declarations) [] target
  StateRel flat.1 clos.2 ∧ DecResultRel flat.2 clos.1

/-- Empty declarations return no error and an empty closure result. -/
theorem evaluate_decs_nil {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (states : StateRel source target) : DecSim source target [] := by
  simpa [DecSim, FlatSem.evaluateDecs, compileDecs, compile, compileExps, ClosSem.evaluate] using
    And.intro states (DecResultRel.success [])

/-- The only closure value related to flat unit is closure unit. -/
theorem unitValue_target (target : ClosSem.Value) (related : ValueRel FlatSem.unitValue target) :
    target = ClosSem.unitValue := by
  cases related with
  | tuple fields => cases fields; rfl

/-- Compose the simulation of the first declaration with the induction
hypothesis for the remaining declarations. -/
theorem evaluate_decs_cons {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp)
    (firstSim : (FlatSem.evaluate ⟨[]⟩ source [declaration]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[]⟩ [] [] source target [declaration])
    (restSim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluateDecs next rest).2 ≠ some (.abort .typeError) → DecSim next nextTarget rest)
    (notTypeError : (FlatSem.evaluateDecs source (declaration :: rest)).2 ≠ some (.abort .typeError)) :
    DecSim source target (declaration :: rest) := by
  have firstNotTypeError : (FlatSem.evaluate ⟨[]⟩ source [declaration]).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluateDecs_cons]
    unfold FlatSem.evaluateDec
    simp only [failure]
  have firstSim := firstSim firstNotTypeError
  unfold EvalSim at firstSim
  unfold DecSim
  simp only [compileDecs, compile, compileExps] at firstSim ⊢
  rw [FlatSem.evaluateDecs_cons] at notTypeError ⊢
  unfold FlatSem.evaluateDec at notTypeError ⊢
  cases flatRun : FlatSem.evaluate ⟨[]⟩ source [declaration] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp [] declaration] [] target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at firstSim notTypeError ⊢
      rcases firstSim with ⟨states, results⟩
      cases results with
      | abort error =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closRun]
        exact ⟨states, .abort error⟩
      | raise related =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closRun]
        exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length ⟨[]⟩ source next declaration _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            have sourceUnit : sourceValue = FlatSem.unitValue := by
              cases sourceValue <;> simp [FlatSem.unitValue] at notTypeError ⊢
              case conv stamp fields => cases stamp <;> cases fields <;> simp_all
            subst sourceValue
            have targetUnit := unitValue_target targetValue head
            subst targetValue
            rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ closRun]
            simp [FlatSem.unitValue] at notTypeError ⊢
            have bound := FlatSem.evaluate_clock_spec.1 ⟨[]⟩ source next [declaration] _ flatRun
            have restRelated := restSim next nextTarget states bound notTypeError
            simp only [DecSim, compileDecs, compile] at restRelated
            cases closTail : ClosSem.evaluate (compileExps [] rest) [] nextTarget with
            | mk tailResult lastTarget =>
              cases flatTail : FlatSem.evaluateDecs next rest with
              | mk last tailError =>
                simp only [closTail, flatTail] at restRelated ⊢
                rcases restRelated with ⟨lastStates, tailRel⟩
                cases tailRel with
                | success values => exact ⟨lastStates, .success (ClosSem.unitValue :: values)⟩
                | raise valueRel => exact ⟨lastStates, .raise valueRel⟩
                | abort error => exact ⟨lastStates, .abort error⟩

/-- An installed declaration sequence ends with an explicit unit result on
success, and propagates related exceptions and identical aborts. -/
inductive DecUnitResultRel : Option (ErrorResult FlatSem.Value) →
    Result (List ClosSem.Value) ClosSem.Value → Prop where
  | success (prior : List ClosSem.Value) :
      DecUnitResultRel none (.val (prior ++ [ClosSem.unitValue]))
  | raise {source target} (related : ValueRel source target) :
      DecUnitResultRel (some (.raise source)) (.err (.raise target))
  | abort (error : Abort) : DecUnitResultRel (some (.abort error)) (.err (.abort error))

/-- Simulation of declarations followed by the unit expression appended by
dynamic installation. -/
def DecUnitSim {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (declarations : List FlatLang.Exp) : Prop :=
  let flat := FlatSem.evaluateDecs source declarations
  let clos := ClosSem.evaluate (compileDecs declarations ++ compileDecs [.con .none none []]) [] target
  StateRel flat.1 clos.2 ∧ DecUnitResultRel flat.2 clos.1

/-- The appended unit expression handles the empty declaration list. -/
theorem evaluate_decs_unit_nil {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (states : StateRel source target) : DecUnitSim source target [] := by
  simpa [DecUnitSim, FlatSem.evaluateDecs, compileDecs, compile, compileExps, compileExp, smartCons,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.unitValue] using
    And.intro states (DecUnitResultRel.success [])

/-- Compose one declaration with the remaining unit-terminated sequence. -/
theorem evaluate_decs_unit_cons {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp)
    (firstSim : (FlatSem.evaluate ⟨[]⟩ source [declaration]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[]⟩ [] [] source target [declaration])
    (restSim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluateDecs next rest).2 ≠ some (.abort .typeError) → DecUnitSim next nextTarget rest)
    (notTypeError : (FlatSem.evaluateDecs source (declaration :: rest)).2 ≠ some (.abort .typeError)) :
    DecUnitSim source target (declaration :: rest) := by
  have firstNotTypeError : (FlatSem.evaluate ⟨[]⟩ source [declaration]).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluateDecs_cons]
    unfold FlatSem.evaluateDec
    simp only [failure]
  have firstSim := firstSim firstNotTypeError
  unfold EvalSim at firstSim
  unfold DecUnitSim
  simp only [compileDecs, compile, compileExps, List.cons_append] at firstSim ⊢
  rw [FlatSem.evaluateDecs_cons] at notTypeError ⊢
  unfold FlatSem.evaluateDec at notTypeError ⊢
  cases flatRun : FlatSem.evaluate ⟨[]⟩ source [declaration] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp [] declaration] [] target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at firstSim notTypeError ⊢
      rcases firstSim with ⟨states, results⟩
      cases results with
      | abort error =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closRun]
        exact ⟨states, .abort error⟩
      | raise related =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closRun]
        exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length ⟨[]⟩ source next declaration _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            have sourceUnit : sourceValue = FlatSem.unitValue := by
              cases sourceValue <;> simp [FlatSem.unitValue] at notTypeError ⊢
              case conv stamp fields => cases stamp <;> cases fields <;> simp_all
            subst sourceValue
            have targetUnit := unitValue_target targetValue head
            subst targetValue
            rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ closRun]
            simp [FlatSem.unitValue] at notTypeError ⊢
            have bound := FlatSem.evaluate_clock_spec.1 ⟨[]⟩ source next [declaration] _ flatRun
            have restRelated := restSim next nextTarget states bound notTypeError
            simp only [DecUnitSim, compileDecs, compile] at restRelated
            cases closTail : ClosSem.evaluate (compileExps [] rest ++ compileExps [] [.con .none none []]) [] nextTarget with
            | mk tailResult lastTarget =>
              cases flatTail : FlatSem.evaluateDecs next rest with
              | mk last tailError =>
                simp only [compileExps] at closTail restRelated
                simp only [closTail, flatTail] at restRelated ⊢
                rcases restRelated with ⟨lastStates, tailRel⟩
                cases tailRel with
                | success prior => exact ⟨lastStates, .success (ClosSem.unitValue :: prior)⟩
                | raise valueRel => exact ⟨lastStates, .raise valueRel⟩
                | abort error => exact ⟨lastStates, .abort error⟩

end Flapjack.Compiler.Backend.FlatToClos
