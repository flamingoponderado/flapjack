load "bvi_tailrecProofTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then
    (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail ("hypotheses: " ^ label);
val _ = show_thm "input_condition_def_typed=" bvi_tailrecProofTheory.input_condition_def;
val _ = show_thm "compile_prog_semantics_typed=" bvi_tailrecProofTheory.compile_prog_semantics;
val _ = show_thm "compile_each_semantics_typed=" bvi_tailrecProofTheory.compile_each_semantics;
val _ = show_thm "evaluate_compile_each_typed=" bvi_tailrecProofTheory.evaluate_compile_each;
val _ = show_thm "state_rel_def_typed=" bvi_tailrecProofTheory.state_rel_def;
val _ = show_thm "state_rel_const_typed=" bvi_tailrecProofTheory.state_rel_const;
val _ = show_thm "state_rel_with_clock_typed=" bvi_tailrecProofTheory.state_rel_with_clock;
val _ = show_thm "state_rel_code_rel_typed=" bvi_tailrecProofTheory.state_rel_code_rel;
val _ = show_thm "code_rel_def_typed=" bvi_tailrecProofTheory.code_rel_def;
val _ = show_thm "code_rel_domain_typed=" bvi_tailrecProofTheory.code_rel_domain;
val _ = show_thm "evaluate_let_wrap_typed=" bvi_tailrecProofTheory.evaluate_let_wrap;
val _ = show_thm "evaluate_complete_ind_typed=" bvi_tailrecProofTheory.evaluate_complete_ind;
val _ = show_thm "EVERY_LAST1_typed=" bvi_tailrecProofTheory.EVERY_LAST1;
val _ = show_thm "scan_expr_LENGTH_typed=" bvi_tailrecProofTheory.scan_expr_LENGTH;
val _ = show_thm "LAST1_thm_typed=" bvi_tailrecProofTheory.LAST1_thm;
val _ = show_thm "try_update_LENGTH_typed=" bvi_tailrecProofTheory.try_update_LENGTH;
val _ = show_thm "update_context_LENGTH_typed=" bvi_tailrecProofTheory.update_context_LENGTH;
val _ = show_thm "try_update_EL_typed=" bvi_tailrecProofTheory.try_update_EL;
val _ = show_thm "try_update_twice_typed=" bvi_tailrecProofTheory.try_update_twice;
val _ = show_thm "index_of_simp_typed=" bvi_tailrecProofTheory.index_of_simp;
val _ = show_thm "scan_expr_ty_rel_typed=" bvi_tailrecProofTheory.scan_expr_ty_rel;
val _ = show_thm "check_op_thm_typed=" bvi_tailrecProofTheory.check_op_thm;
val _ = show_thm "optimized_code_def_typed=" bvi_tailrecProofTheory.optimized_code_def;
val _ = show_thm "code_rel_subspt_typed=" bvi_tailrecProofTheory.code_rel_subspt;
val _ = show_thm "compile_each_LENGTH_typed=" bvi_tailrecProofTheory.compile_each_LENGTH;
val _ = show_thm "rewrite_scan_expr_typed=" bvi_tailrecProofTheory.rewrite_scan_expr;
val _ = show_thm "scan_expr_op_type_typed=" bvi_tailrecProofTheory.scan_expr_op_type;
val _ = show_thm "compile_each_next_mono_typed=" bvi_tailrecProofTheory.compile_each_next_mono;
val _ = show_thm "compile_prog_next_mono_typed=" bvi_tailrecProofTheory.compile_prog_next_mono;
val _ = show_thm "compile_each_MEM_typed=" bvi_tailrecProofTheory.compile_each_MEM;
val _ = show_thm "compile_prog_MEM_typed=" bvi_tailrecProofTheory.compile_prog_MEM;
(* The two find-code theorems are local in the original script. Replay their
   original statements and proofs so their inferred types are captured. *)
open preamble bvi_tailrecProofTheory bvi_tailrecTheory bviPropsTheory bviSemTheory;
val find_code_def = bvlSemTheory.find_code_def;
val code_rel_find_code_some_replay = Q.prove
  (`∀c1 c2 (args: v list) a exp.
      code_rel c1 c2 ∧ find_code (SOME n) args c1 = SOME (a, exp) ⇒
        find_code (SOME n) args c2 ≠ NONE`,
   rw [find_code_def, code_rel_def]
   \\ pop_assum mp_tac
   \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
   \\ first_x_assum drule
   \\ fs [compile_exp_def]
   \\ CASE_TAC \\ fs [] \\ rw []
   \\ pairarg_tac \\ fs []);
val _ = show_thm "code_rel_find_code_SOME_replay_typed=" code_rel_find_code_some_replay;
val code_rel_find_code_none_replay = Q.prove
  (`∀c1 c2 (args: v list) a exp.
      code_rel c1 c2 ∧ find_code NONE args c1 = SOME (a, exp) ⇒
        find_code NONE args c2 ≠ NONE`,
   rw [find_code_def, code_rel_def]
   \\ pop_assum mp_tac
   \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
   >- (first_x_assum drule
       \\ fs [compile_exp_def]
       \\ CASE_TAC \\ fs [] \\ rw []
       \\ pairarg_tac \\ fs [])
   \\ first_x_assum drule
   \\ fs [compile_exp_def]
   \\ CASE_TAC \\ fs [] \\ rw []
   \\ pairarg_tac \\ fs []);
val _ = show_thm "code_rel_find_code_NONE_replay_typed=" code_rel_find_code_none_replay;
