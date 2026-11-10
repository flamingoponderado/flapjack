module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationTotal
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section


/-! Observational correctness of known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Semantics
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The source and optimized initial states satisfy the simulation relation. -/
theorem initialStateRel {C F : Type} (c : Config) (ffi : HolFfiState F) (maxApp clock : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc : Compiler C)
    (aux : ∀ n, (co n).2.2 = []) (free : ∀ n, fvMax 0 (co n).2.1) :
    StateRel c (nextG (initialState ffi maxApp HolFiniteMapExact.empty co (stateCc (compileInc c) cc) clock))
      (initialState ffi maxApp HolFiniteMapExact.empty co (stateCc (compileInc c) cc) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (compileInc c) co) cc clock) := by
  simp [StateRel, initialState, ClosMti.fmapRel, aux, free, HolFiniteMapExact.empty]

/-- Evaluation from the two related initial states preserves result shape and
FFI state at each clock. This is Flapjack infrastructure for the exported
observational theorem. -/
theorem initialEvaluationRelated {C F : Type} (c : Config) (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc : Compiler C)
    (xs : List ClosLang.Exp) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (aux : ∀ n, (co n).2.2 = []) (freeOracle : ∀ n, fvMax 0 (co n).2.1)
    (safeOraclePrograms : ∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e)
    (inputSyntax : everyFnVarsNone xs) (coSyntax : coEveryFnVarsNone co)
    (mono : oracleGapproxSubspt co) (oracleSafe : oracleStateSgcFree co)
    (stateOracle : isStateOracle (compileInc c) co) (unique : uniqueSetGlobals xs co)
    (exprSafe : ∀ e ∈ xs, esgcFree e) (free : fvMax 0 xs)
    (nextEq : (co 0).1.1 = g) (oracleDisjoint : oracleGapproxDisjoint g co)
    (known : knownListTotal c xs [] .ln = (eas, g))
    (sourceSafe : ∀ clock, (evaluate xs [] (initialState ffi maxApp HolFiniteMapExact.empty co
      (stateCc (compileInc c) cc) clock)).1 ≠ .err (.abort .typeError)) :
    ∀ clock,
      resultOutcome (evaluate xs [] (initialState ffi maxApp HolFiniteMapExact.empty co
        (stateCc (compileInc c) cc) clock)).1 =
        resultOutcome (evaluate (eas.map Prod.fst) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (stateCo (compileInc c) co) cc clock)).1 ∧
      ((evaluate xs [] (initialState ffi maxApp HolFiniteMapExact.empty co
        (stateCc (compileInc c) cc) clock)).1 = .err (.abort .typeError) ↔
        (evaluate (eas.map Prod.fst) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (stateCo (compileInc c) co) cc clock)).1 = .err (.abort .typeError)) ∧
      (evaluate xs [] (initialState ffi maxApp HolFiniteMapExact.empty co
        (stateCc (compileInc c) cc) clock)).2.ffi =
        (evaluate (eas.map Prod.fst) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (stateCo (compileInc c) co) cc clock)).2.ffi := by
  intro clock
  let source := initialState ffi maxApp HolFiniteMapExact.empty co (stateCc (compileInc c) cc) clock
  let target := initialState ffi maxApp HolFiniteMapExact.empty (stateCo (compileInc c) co) cc clock
  have sourceRel : StateRel c (nextG source) source target := initialStateRel c ffi maxApp clock co cc aux freeOracle
  have sourceSafeState : ssgcFree source := by
    simp only [ssgcFree, source, initialState, HolFiniteMapExact.empty]
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro n exps extra h
    have safe := safeOraclePrograms n exps extra h
    have extraEmpty : extra = [] := by
      have e := aux n
      rw [h] at e
      exact e
    subst extra
    exact ⟨safe, by simp [elistGlobals]⟩
  have emptyDisjoint : mglobalsDisjoint ([] : List (Option ClosSem.Value)) xs := by
    simp [mglobalsDisjoint, mappedGlobals, getGlobal]
  have emptyOracleDisjoint : stateOracleMglobalsDisjoint source := by
    intro n
    simp [source, initialState, mglobalsDisjoint, mappedGlobals, getGlobal]
  have emptyGlobals : stateGlobalsApprox source (nextG source) := by
    simp [stateGlobalsApprox, source, initialState, getGlobal]
  have emptyApprox : globalsApproxSgcFree (.ln : Spt ValApprox) := by
    simp [globalsApproxSgcFree, sptLookup]
  have emptySub : sptSubspt (.ln : Spt ValApprox) g := by
    simp [sptSubspt, sptMem, sptDomain, sptLookup]
  have finalSub : sptSubspt g (nextG source) := by
    simp [source, initialState, nextG, nextEq, sptSubspt]
  cases sourceRun : evaluate xs [] source with
  | mk result final =>
    have noType : result ≠ .err (.abort .typeError) := by
      intro bad
      apply sourceSafe clock
      simpa [source, sourceRun] using bad
    obtain ⟨targetResult, targetFinal, targetRun, related, finalState, _, _, _⟩ :=
      (Simulation.Total.knownCorrect0 (C := C) (F := F)).1 xs [] source result final
        [] [] [] [] target c .ln g [] eas
        ⟨sourceRun, known, sourceRel, inputSyntax, by simpa [source, initialState] using coSyntax,
          by simpa [source, initialState] using emptyDisjoint,
          by simpa [source, initialState, nextG, nextEq] using oracleDisjoint,
          emptyOracleDisjoint, exprSafe, sourceSafeState, by simp, .nil,
          by simpa [source, initialState] using oracleSafe, emptyApprox, by simp, emptyGlobals,
          emptySub, finalSub, by simpa [source, initialState] using mono, by simpa using free,
          .nil, by simpa [source, initialState] using unique,
          by simpa [source, initialState] using stateOracle, rfl, noType⟩
    have observation := resultRelOutcome _ _ result targetResult related
    have ffiEq : final.ffi = targetFinal.ffi := finalState.2.2.2.2.2.1
    have observationAll := And.intro observation.1 (And.intro observation.2 ffiEq)
    have targetRun' : evaluate (eas.map Prod.fst) []
        (initialState ffi maxApp HolFiniteMapExact.empty (stateCo (compileInc c) co) cc clock) =
        (targetResult, targetFinal) := by simpa [target] using targetRun
    simpa [source, sourceRun, targetRun'] using observationAll

/-- Factored observational helper using the canonical empty map. Its
source-shaped counterpart is stated below. -/
theorem semanticsKnown {C F : Type} (c : Config) (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc : Compiler C)
    (xs : List ClosLang.Exp) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (nonFail : semantics ffi maxApp HolFiniteMapExact.empty co (stateCc (compileInc c) cc) xs ≠ .fail)
    (h : (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (compileInc c) co ∧ uniqueSetGlobals xs co ∧
      (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧ (co 0).1.1 = g ∧
      oracleGapproxDisjoint g co ∧ knownListTotal c xs [] .ln = (eas, g)) :
    semantics ffi maxApp HolFiniteMapExact.empty (stateCo (compileInc c) co) cc (eas.map Prod.fst) =
      semantics ffi maxApp HolFiniteMapExact.empty co (stateCc (compileInc c) cc) xs := by
  obtain ⟨aux, freeOracle, safeOraclePrograms, inputSyntax, coSyntax, mono, oracleSafe,
    stateOracle, unique, exprSafe, free, nextEq, oracleDisjoint, known⟩ := h
  have sourceSafe := (semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty co
    (stateCc (compileInc c) cc) xs).mp nonFail
  have same := initialEvaluationRelated c ffi maxApp co cc xs eas g aux freeOracle safeOraclePrograms
    inputSyntax coSyntax mono oracleSafe stateOracle unique exprSafe free nextEq oracleDisjoint known sourceSafe
  exact (semantics_eq_of_related_evaluations ffi maxApp HolFiniteMapExact.empty HolFiniteMapExact.empty
    co (stateCo (compileInc c) co) (stateCc (compileInc c) cc) cc xs (eas.map Prod.fst) same).symm

/-- Known-function optimization preserves whole-program observations under
the source oracle, syntax and global-approximation conditions. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "semantics_known"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semanticsKnownHOL {C F : Type} (c : Config) (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc : Compiler C)
    (xs : List ClosLang.Exp) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (nonFail : semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty co (stateCc (compileInc c) cc) xs ≠ .fail)
    (h : (∀ n, (co n).2.2 = []) ∧ (∀ n, fvMax 0 (co n).2.1) ∧
      (∀ n exps extra, (co n).2 = (exps, extra) → ∀ e ∈ exps, esgcFree e) ∧
      everyFnVarsNone xs ∧ coEveryFnVarsNone co ∧ oracleGapproxSubspt co ∧
      oracleStateSgcFree co ∧ isStateOracle (compileInc c) co ∧ uniqueSetGlobals xs co ∧
      (∀ e ∈ xs, esgcFree e) ∧ fvMax 0 xs ∧ (co 0).1.1 = g ∧
      oracleGapproxDisjoint g co ∧ knownListTotal c xs [] .ln = (eas, g)) :
    semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty (stateCo (compileInc c) co) cc (eas.map Prod.fst) =
      semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty co (stateCc (compileInc c) cc) xs :=
  semanticsKnown c ffi maxApp co cc xs eas g nonFail h

end Flapjack.Compiler.Backend.ClosKnown.Semantics
