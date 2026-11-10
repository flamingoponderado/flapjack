module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.FlatToClos.Op


@[expose] public section

/-! Error propagation through closure expressions used by flat-to-closure compilation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

namespace ClosureErrorPort
/-- Roundtrip for the closure state's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end ClosureErrorPort

/-- A failed binding evaluation propagates through a closure let. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_Let_error"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_error {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (state last : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (run : ClosSem.evaluate expressions env state = (.err error, last)) :
    ClosSem.evaluate [.let trace expressions body] env state = (.err error, last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]

/-- A failed argument evaluation propagates through a closure operation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_Op_error"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_op_error {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (state last : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (run : ClosSem.evaluate expressions env state = (.err error, last)) :
    ClosSem.evaluate [.op trace op expressions] env state = (.err error, last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]

/-- Compilation preserves argument-evaluation errors for the ordinary operators. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_op_evaluates_args"
  (fmap_as_finite_support := [refs, code])]
theorem compileOp_evaluates_args {C F : Type} (xs : List ClosLang.Exp) (db : List ClosSem.Value)
    (t : ClosSem.State C F) (err : ErrorResult ClosSem.Value) (t1 : ClosSem.State C F)
    (op : FlatLang.Op) (tra : BackendCommon.Tra) :
    ClosSem.evaluate xs db t = (.err err, t1) ∧
      op ≠ .src .opapp ∧ op ≠ .src .eval ∧ op ≠ .src (.thunkOp .forceThunk) →
    ClosSem.evaluate [compileOp tra op xs] db t = (.err err, t1) := by
  intro ⟨run, notApp, notEval, notForce⟩
  cases op <;> try (rename_i a; cases a)
  all_goals simp only [compileOp]
  all_goals try exact evaluate_op_error xs db t t1 err tra _ run
  all_goals try exact evaluate_let_error xs db t t1 err _ _ run
  all_goals try contradiction
  case src.arith action ty =>
    cases ty <;> cases action <;> simp only [compileArith] <;>
      first | exact evaluate_op_error xs db t t1 err tra _ run
            | exact evaluate_let_error xs db t t1 err _ _ run
  all_goals try (repeat' first
    | exact evaluate_op_error xs db t t1 err tra _ run
    | exact evaluate_let_error xs db t t1 err _ _ run
    | split)
  all_goals try simp_all
  all_goals cases xs with
    | nil => simp [ClosSem.evaluate] at run
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [arg1, arg2]
        first | exact run | exact evaluate_let_error [x] db t t1 err _ _ run | skip
        all_goals apply evaluate_op_error
        all_goals simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
          ClosSem.applyNumeric, ClosSem.doIntApp, run]
      | cons y rest =>
        cases rest with
        | nil =>
          simp only [arg1, arg2]
          first | exact evaluate_let_error [x,y] db t t1 err _ _ run | skip
          all_goals apply evaluate_op_error
          all_goals rw [ClosSem.evaluate] at run ⊢
          all_goals rw [ClosSem.fixClock_evaluate] at run ⊢
          all_goals cases h : ClosSem.evaluate [x] db t with
          | mk r next =>
            cases r <;> simp_all [ClosSem.evaluate, ClosSem.fixClock,
              ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
            all_goals cases h2 : ClosSem.evaluate [y] db next with
            | mk r2 last => cases r2 <;> simp_all
        | cons z zs =>
          simp only [arg1, arg2]
          exact evaluate_let_error (x :: y :: z :: zs) db t t1 err _ _ run

end Flapjack.Compiler.Backend.FlatToClos
