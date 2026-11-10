module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Observational consequence of the proof-side numbering simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

private def resultHasOutcome (result : Result (List Value) Value) (outcome : HolOutcome) : Prop :=
  match result with
  | .err (.abort .timeoutError) => False
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | _ => outcome = .success

private theorem resultHasOutcome_iff (result : Result (List Value) Value) (outcome : HolOutcome) :
    resultHasOutcome result outcome ↔
      (match result, outcome with
       | .err (.abort .timeoutError), _ => False
       | .err (.abort (.ffiError event)), outcome => outcome = .ffiOutcome event
       | _, outcome => outcome = .success) := by
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | raise value => rfl
    | abort reason => cases reason <;> rfl

/-- Numbering-related results agree on type errors and on every terminating
observable outcome, without requiring their returned values to be equal. -/
theorem resultRel_observations (maxApp : Nat) (left right : Result (List Value) Value)
    (related : ResultRel maxApp left right) :
    (left = .err (.abort .typeError) ↔ right = .err (.abort .typeError)) ∧
    ∀ outcome : HolOutcome, resultHasOutcome left outcome ↔ resultHasOutcome right outcome := by
  cases left with
  | val values =>
    cases right with
    | val nextValues => simp [resultHasOutcome]
    | err error => cases error <;> simp [ResultRel] at related
  | err error =>
    cases error with
    | raise value =>
      cases right with
      | val values => simp [ResultRel] at related
      | err nextError =>
        cases nextError with
        | raise nextValue => simp [resultHasOutcome]
        | abort reason => cases related
    | abort reason =>
      cases right with
      | val values => simp [ResultRel] at related
      | err nextError =>
        cases nextError with
        | raise value => simp [ResultRel] at related
        | abort nextReason =>
          have same : reason = nextReason := related
          subst nextReason
          cases reason <;> simp [resultHasOutcome]

/-- Initial source and numbered target states satisfy the proof-side state
relation when every oracle program is safe for numbering. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C)
    (safe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome maxApp (oracle index).2.1) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (stateCc (ignoreTable compileInc) compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock) := by
  simp [StateRel, initialState, optionRel, HolFiniteMapExact.empty, safe]

/-- Factored numbering-semantics helper; its separate safety premises are
assembled into the source theorem below. It has no separate HOL declaration. -/
theorem semantics_number {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ignoreTable compileInc) compiler) program ≠ .fail)
    (safe : ¬ ClosProps.containsAppSome maxApp program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome maxApp (oracle index).2.1) :
    semantics ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler
      (renumberList number program).2 =
    semantics ffi maxApp HolFiniteMapExact.empty oracle (stateCc (ignoreTable compileInc) compiler) program := by
  classical
  have sourceSafe := (semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle
    (stateCc (ignoreTable compileInc) compiler) program).mp notFail
  have simulations : ∀ clock,
      ResultRel maxApp
        (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (stateCc (ignoreTable compileInc) compiler) clock)).1
        (evaluate (renumberList number program).2 []
          (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock)).1 ∧
      (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (stateCc (ignoreTable compileInc) compiler) clock)).2.ffi =
        (evaluate (renumberList number program).2 []
          (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock)).2.ffi := by
    intro clock
    cases sourceRun : evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (stateCc (ignoreTable compileInc) compiler) clock) with
    | mk result final =>
      have noType : result ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
      obtain ⟨targetResult, targetFinal, targetRun, resultRel, stateRel⟩ :=
        evaluate_simulation.1 program [] [] _ _ result final number sourceRun noType safe .nil
          (initialState_related ffi maxApp clock oracle compiler oracleSafe)
      rw [targetRun]
      exact ⟨resultRel, stateRel.2.1⟩
  have targetSafe : ∀ clock,
      (evaluate (renumberList number program).2 []
        (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock)).1 ≠
          .err (.abort .typeError) := by
    intro clock bad
    exact sourceSafe clock ((resultRel_observations _ _ _ (simulations clock).1).1.mpr bad)
  have terminatingEq :
      terminatingObservation ffi maxApp HolFiniteMapExact.empty oracle (stateCc (ignoreTable compileInc) compiler) program =
      terminatingObservation ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler
        (renumberList number program).2 := by
    funext behavior
    apply propext
    constructor <;> intro observed
    · obtain ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩ := observed
      have sim := simulations clock
      rw [run] at sim
      refine ⟨clock, _, _, outcome, rfl, ?_, ?_⟩
      · apply (resultHasOutcome_iff _ outcome).mp
        apply ((resultRel_observations _ _ _ sim.1).2 outcome).mp
        exact (resultHasOutcome_iff result outcome).mpr outcomeEq
      · simpa [← sim.2] using behaviorEq
    · obtain ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩ := observed
      have sim := simulations clock
      rw [run] at sim
      refine ⟨clock, _, _, outcome, rfl, ?_, ?_⟩
      · apply (resultHasOutcome_iff _ outcome).mp
        apply ((resultRel_observations _ _ _ sim.1).2 outcome).mpr
        exact (resultHasOutcome_iff result outcome).mpr outcomeEq
      · simpa [sim.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (stateCc (ignoreTable compileInc) compiler) clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate (renumberList number program).2 []
          (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(simulations clock).2] using h
    · simpa [← (simulations clock).2] using h
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
      (stateCc (ignoreTable compileInc) compiler) clock)).1 = .err (.abort .typeError) from
        fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate (renumberList number program).2 []
      (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (ignoreTable compileInc) oracle) compiler clock)).1 =
        .err (.abort .typeError) from fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [← terminatingEq, ← tracesEq]

/-- Closure numbering preserves whole-program observations for a safe,
non-failing source program and safe oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "semantics_number"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semanticsNumberHOL {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle
      (stateCc (ignoreTable compileInc) compiler) program ≠ .fail)
    (safe : ¬ ClosProps.containsAppSome maxApp program ∧
      ∀ index, (oracle index).2.2 = [] ∧
        ¬ ClosProps.containsAppSome maxApp (oracle index).2.1) :
    semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty (stateCo (ignoreTable compileInc) oracle) compiler
      (renumberList number program).2 =
    semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle
      (stateCc (ignoreTable compileInc) compiler) program :=
  semantics_number ffi maxApp number oracle compiler program notFail safe.1 safe.2

end Flapjack.Compiler.Backend.ClosNumber
