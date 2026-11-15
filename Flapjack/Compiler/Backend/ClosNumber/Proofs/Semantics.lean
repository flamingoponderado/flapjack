module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Observational consequence of the proof-side numbering simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

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
  apply Eq.symm
  apply semantics_eq_of_related_evaluations
  intro clock
  obtain ⟨results, ffiEq⟩ := simulations clock
  have toStandard (left right : Result (List Value) Value) (h : ResultRel maxApp left right) :
      SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel maxApp)) (ValueRel maxApp) left right := by
    cases left <;> cases right <;> simp_all [ResultRel, SemanticPrimitivesProps.resultRel]
    case err.err left right =>
      cases left <;> cases right <;> simp_all [SemanticPrimitivesProps.excRel]
  have observed := resultRelOutcome (List.Forall₂ (ValueRel maxApp)) (ValueRel maxApp) _ _ (toStandard _ _ results)
  exact ⟨observed.1, observed.2, ffiEq⟩

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
