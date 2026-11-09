module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.HandleBranch

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
@[expose] public section

/-! Composition of the match-expression cases. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An error in a match scrutinee propagates through the source match. -/
theorem evaluate_mat_error {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .err error)) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- An error in the generated let initializer propagates without dispatch. -/
theorem evaluate_let_error {C F : Type} (trace : BackendCommon.Tra) (name : VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state [.let_ trace (some name) first body] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- A type-failing source row makes the match expression type-fail. -/
theorem evaluate_mat_rowTypeError {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value = .typeError) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- Duplicate variables in a selected match row make the expression type-fail. -/
theorem evaluate_mat_duplicate {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value =
      .match (bindings, pattern, body)) (duplicate : ¬(FlatLang.patBindings pattern).Nodup) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- Compilation's generated-name bound for a match expression. -/
theorem compileExp_mat_bound (cfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileExp cfg (.mat trace scrutinee rows)).1 =
      max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 := by
  cases first : compileExp cfg scrutinee with
  | mk bound rest =>
    cases rest with
    | mk flag expression =>
      cases matchResult : compileMatch cfg rows with
      | mk rowBound rest =>
        cases rest with
        | mk rowFlag compiledRows => simp [compileExp, first, matchResult]

end Flapjack.Compiler.Backend.FlatPattern
