module

public meta import Lean.Elab.Tactic.Generalize
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CorrSupport

@[expose] public section

/-! Flapjack-only proof automation for the generated `*_corr_thm` ports: the
symbolic-execution tactics, and `generalize_app`, which replaces the first
application of a given function in the goal (and every equal occurrence) by a
fresh variable. No HOL counterpart. -/

namespace Flapjack.Compiler.Backend.WordBignum.CorrSupport

open Lean Elab Tactic Meta in
/-- Generalize the first application of the named constant in the goal. -/
elab "generalize_app " c:ident " as " x:ident : tactic => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some e := t.find? (fun e => e.isAppOf name)
    | throwError "no application of {name} in the goal"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| generalize $stx = $x at *))

/-- Normalise state projections, register reads and expression evaluation. -/
macro "corr_simp" : tactic => `(tactic| ((try simp only [Compiler.Encoders.Asm.wordCmpHOL,
  holAsmSignedLess_eq_slt, decide_true_any, decide_false_any, Bool.not_eq_true',
  Bool.not_eq_false', Bool.not_eq_true,
  Bool.not_eq_false, Bool.not_true, Bool.not_false, beq_iff_eq, beq_eq_false_iff_ne,
  bne_iff_ne] at *) <;> simp only [regWrite_arrays, regWrite_clock,
  arrayWrite_regs, arrayWrite_clock, arrayWrite_arrays, clockWrite_regs, clockWrite_arrays,
  clockWrite_clock, decClock_regs, decClock_arrays, decClock_clock, incClock_regs,
  incClock_arrays, incClock_clock, deleteVars_arrays, deleteVars_clock, deleteVars_lookup,
  lookup_regWrite, lookup_regDelete, holFapply_regWrite, evalExp, evalRi, evalExpPre,
  evalRiPre, Compiler.Encoders.Asm.wordCmpHOL, mem_dom_iff, beq_iff_eq, decide_eq_true_eq, decide_true_any, decide_false_any,
  beq_eq_false_iff_ne, Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne,
  ne_eq, reduceCtorEq, if_true, if_false, ite_true, ite_false, Nat.reduceEqDiff,
  List.mem_cons, List.mem_nil_iff, or_false, not_false_eq_true, Option.some_ne_none,
  true_and, and_true, not_true_eq_false, false_or, or_self] at *))

/-- Discharge a side condition of a symbolic execution step. -/
macro "corr_side" : tactic => `(tactic| (corr_simp <;> first | done | (simp_all; done) | omega))

/-- Close an equality of mini-language states extensionally. -/
macro "corr_state_eq" : tactic => `(tactic|
  ((try (repeat' split)) <;> refine MiniState.ext' (fun k => ?_) (funext fun a => ?_) ?_ <;>
    corr_simp <;> (try split_ifs) <;> simp_all <;> omega))

/-- Symbolically execute a mini program, with `t` as an extra first step (for
generated sub-programs). -/
syntax "corr_exec_with " "(" tacticSeq ")" : tactic
/-- One symbolic execution step. -/
syntax "corr_step" : tactic
macro_rules
  | `(tactic| corr_step) => `(tactic| first
    | refine ev_seq_seq ?_
    | (refine ev_seq_assign ?_ ?_ <;> try corr_side)
    | refine ev_seq_delete ?_
    | refine ev_seq_swap ?_
    | (refine ev_seq_load ?_ ?_ ?_ <;> try corr_side)
    | (refine ev_seq_store ?_ ?_ ?_ ?_ <;> try corr_side)
    | (refine ev_seq_add ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side)
    | (refine ev_seq_sub ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side)
    | (refine ev_seq_mul ?_ ?_ ?_ ?_ <;> try corr_side)
    | (refine ev_seq_div ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side)
    | ((refine ev_ite2 ?_ ?_ ?_ ?_ <;> try corr_side) <;> intro hcmp <;>
        (try corr_simp) <;> (try (exfalso; simp_all; done))))

/-- Close a final `Skip` or `Continue`. -/
syntax "corr_leaf" : tactic
macro_rules
  | `(tactic| corr_leaf) => `(tactic|
    ((first | refine ev_skip ?_ | refine ev_continue ?_) <;> corr_state_eq))

macro_rules
  | `(tactic| corr_exec_with ($t)) => `(tactic|
    ((repeat (first | ($t) | corr_step)) <;> corr_leaf))

macro "corr_exec" : tactic => `(tactic| corr_exec_with (fail))

end Flapjack.Compiler.Backend.WordBignum.CorrSupport
