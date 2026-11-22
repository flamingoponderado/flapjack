module

public meta import Lean.Elab.Tactic.Generalize
public import Mathlib.Tactic.IntervalCases
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
  let some e := t.find? (fun e => e.isAppOf name && !e.hasLooseBVars)
    | throwError "no application of {name} in the goal"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| generalize $stx = $x at *))

open Lean Elab Tactic Meta in
/-- Generalize the first application of the named constant in the goal,
recording the equation as `h`. -/
elab "generalize_app_eq " c:ident " as " x:ident " with " h:ident : tactic => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some e := t.find? (fun e => e.isAppOf name && !e.hasLooseBVars)
    | throwError "no application of {name} in the goal"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| generalize $h:ident : $stx = $x at *))

open Lean Elab Tactic Meta in
/-- Split a goal that is syntactically a conjunction (without unfolding
definitions) into its conjuncts, recursively. -/
elab "corr_split_ands" : tactic => do
  let rec go (fuel : Nat) (g : MVarId) : MetaM (List MVarId) := do
    let fuel + 1 := fuel | return [g]
    g.withContext do
    let t ← instantiateMVars (← g.getType)
    match t.and? with
    | some (a, b) =>
      let ga ← mkFreshExprSyntheticOpaqueMVar a
      let gb ← mkFreshExprSyntheticOpaqueMVar b
      g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
      return (← go fuel ga.mvarId!) ++ (← go fuel gb.mvarId!)
    | none => return [g]
  let g ← getMainGoal
  replaceMainGoal (← go 64 g)

/-- Normalise state projections, register reads and expression evaluation. -/
macro "corr_simp" : tactic => `(tactic| ((try simp only [Compiler.Encoders.Asm.wordCmpHOL,
  holAsmSignedLess_eq_slt, decide_true_any, decide_false_any, Bool.not_eq_true',
  Bool.not_eq_false', Bool.not_eq_true,
  Bool.not_eq_false, Bool.not_true, Bool.not_false, beq_iff_eq, beq_eq_false_iff_ne,
  bne_iff_ne] at *) <;> simp only [regWrite_arrays, regWrite_clock,
  arrayWrite_regs, arrayWrite_clock, arrayWrite_arrays, clockWrite_regs, clockWrite_arrays,
  clockWrite_clock, decClock_regs, decClock_arrays, decClock_clock, incClock_regs,
  incClock_arrays, incClock_clock, deleteVars_arrays, deleteVars_clock, deleteVars_lookup, holFapply_deleteVars, xor_zero_sub_one, toNat_one_eq,
  andOp_and_eq, mcSingleMulPre_eq_true,
  mcMulBySingle2Pre_eq_true, mcCmp3Pre_eq_true, mcCmpMul2Pre_eq_true, mcCmp2Pre_eq_true,
  mcAdjCmpPre_eq_true, mcIdivModHeaderPre_eq_true, mcIadd1Pre_eq_true, mcIadd2Pre_eq_true,
  mcIadd3Pre_eq_true, mcIsubFlipPre_eq_true, mcImul1Pre_eq_true, mcSub1Pre_eq_true, holFapply_regDelete,
  lookup_regWrite, lookup_regDelete, holFapply_regWrite, evalExp, evalRi, evalExpPre,
  evalRiPre, Compiler.Encoders.Asm.wordCmpHOL, mem_dom_iff, beq_iff_eq, decide_eq_true_eq, decide_true_any, decide_false_any,
  beq_eq_false_iff_ne, Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne,
  ne_eq, reduceCtorEq, ite_self, if_true, if_false, ite_true, ite_false, Nat.reduceEqDiff,
  List.mem_cons, List.mem_nil_iff, or_false, not_false_eq_true, Option.some_ne_none,
  true_and, and_true, not_true_eq_false, false_or, or_self] at *))

/-- Discharge a side condition of a symbolic execution step. -/
macro "corr_side" : tactic => `(tactic| (first | assumption | ((try corr_simp) <;> corr_split_ands <;>
  first | done | trivial | assumption | (simp_all; done) | (intro; simp_all; done) | omega |
  (apply ofNat_toNat_lt_32; decide))))

/-- Close an equality of mini-language states extensionally. -/
macro "corr_state_eq" : tactic => `(tactic|
  ((try (repeat' split)) <;> refine MiniState.ext' (fun k => ?_) (funext fun a => ?_) ?_ <;>
    (try corr_simp) <;>
    first
    | rfl
    | (cases a <;> simp_all [BitVec.neg_one_eq_allOnes] <;> omega)
    | (rcases Nat.lt_or_ge k 32 with hk | hk <;>
        first
        | (interval_cases k <;> simp_all [BitVec.neg_one_eq_allOnes] <;> omega)
        | (simp (disch := omega) only [if_neg]; done))
    | (simp_all [BitVec.neg_one_eq_allOnes] <;> omega)))

/-- After a two-result primitive step, normalise the state and name the two
components of the primitive's result (shared with the shallow side). -/
macro "corr_gen " f:ident : tactic => `(tactic|
  ((try corr_simp); (try (generalize_app $f as res; obtain ⟨_, _⟩ := res));
    (try dsimp only at *)))

/-- `corr_gen` for an addition or subtraction, keeping the fact that its
carry word is `0` or `1`. -/
macro "corr_gen_carry " f:ident lem:ident : tactic => `(tactic|
  ((try corr_simp); (try (generalize_app_eq $f as res with hres; (have hcarry := $lem hres); clear hres; obtain ⟨_, _⟩ := res));
    (try dsimp only at *)))

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
    | ((refine ev_seq_add ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side); corr_gen_carry Flapjack.Misc.Multiword.singleAddWord singleAddWord_carry_of_eq)
    | ((refine ev_seq_sub ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side); corr_gen_carry Flapjack.Misc.Multiword.singleSubWord singleSubWord_carry_of_eq)
    | ((refine ev_seq_mul ?_ ?_ ?_ ?_ <;> try corr_side); corr_gen Flapjack.Misc.Multiword.singleMul)
    | ((refine ev_seq_div ?_ ?_ ?_ ?_ ?_ ?_ <;> try corr_side); corr_gen Flapjack.Misc.Multiword.singleDiv)
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
