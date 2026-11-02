import Flapjack.Compiler.Backend.ClosNumber.Proofs.Evaluate
import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
import Flapjack.Compiler.Backend.ClosMti.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic

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
  simp [StateRel, initialState, OptionRel, HolFiniteMapExact.empty, safe]

/-- Observational semantics are preserved by closure numbering for a
non-failing source program. The proof uses the current proof-side evaluator
and carriers and remains untagged pending HOL correspondence review. -/
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

/-- Multi-argument introduction followed by closure numbering preserves the
current Lean observations. The intermediate numbering invariants follow from
the unary source and oracle invariants. This is not a reviewed HOL port. -/
theorem semantics_mti_then_number {C F : Type} (ffi : HolFfiState F) (maxApp number : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : 1 ≤ maxApp)
    (unary : ∀ e ∈ program, ClosProps.noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧
      ∀ e ∈ (oracle index).2.1, ClosProps.noMti e)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp) (stateCc (ignoreTable compileInc) compiler)) program ≠ .fail) :
    semantics ffi maxApp HolFiniteMapExact.empty
      (stateCo (ignoreTable compileInc) (pureCo (ClosMti.compileInc maxApp) ∘ oracle)) compiler
      (renumberList number (ClosMti.introList maxApp program)).2 =
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp) (stateCc (ignoreTable compileInc) compiler)) program := by
  let transformedOracle : CompileOracle (Nat × C) := pureCo (ClosMti.compileInc maxApp) ∘ oracle
  have mtiSem := ClosMti.semantics_introMulti_candidate ffi maxApp oracle
    (stateCc (ignoreTable compileInc) compiler) program positive oracleUnary unary
  have transformedSafe : ¬ ClosProps.containsAppSome maxApp (ClosMti.introList maxApp program) :=
    ClosMti.introList_numberingSafe maxApp program positive unary
  have oracleSafe : ∀ index, (transformedOracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome maxApp (transformedOracle index).2.1 := by
    intro index
    change (ClosMti.compileInc maxApp (oracle index).2).2 = [] ∧
      ¬ ClosProps.containsAppSome maxApp (ClosMti.compileInc maxApp (oracle index).2).1
    exact ⟨rfl, ClosMti.introList_numberingSafe maxApp (oracle index).2.1 positive (oracleUnary index).2⟩
  have transformedNotFail : semantics ffi maxApp HolFiniteMapExact.empty transformedOracle
      (stateCc (ignoreTable compileInc) compiler) (ClosMti.introList maxApp program) ≠ .fail := by
    simpa [transformedOracle, ← mtiSem] using notFail
  have numberSem := semantics_number ffi maxApp number transformedOracle compiler
    (ClosMti.introList maxApp program) transformedNotFail transformedSafe oracleSafe
  exact numberSem.trans mtiSem.symm

/-- The same observation equality for the executed fuelled traversal. This
does not cover the subsequent known-function and call passes. -/
theorem semantics_compileFuel_then_number {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number : Nat) (oracle : CompileOracle (Nat × C))
    (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : 1 ≤ maxApp)
    (unary : ∀ e ∈ program, ClosProps.noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧
      ∀ e ∈ (oracle index).2.1, ClosProps.noMti e)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp) (stateCc (ignoreTable compileInc) compiler)) program ≠ .fail) :
    ∃ transformed, ClosMti.compileFuel fuel true maxApp program = some transformed ∧
      semantics ffi maxApp HolFiniteMapExact.empty
        (stateCo (ignoreTable compileInc) (pureCo (ClosMti.compileInc maxApp) ∘ oracle)) compiler
        (renumberList number transformed).2 =
      semantics ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc (ClosMti.compileInc maxApp) (stateCc (ignoreTable compileInc) compiler)) program := by
  exact ⟨ClosMti.introList maxApp program, ClosMti.compileFuel_introList fuel maxApp program,
    semantics_mti_then_number ffi maxApp number oracle compiler program positive unary oracleUnary notFail⟩

end Flapjack.Compiler.Backend.ClosNumber
