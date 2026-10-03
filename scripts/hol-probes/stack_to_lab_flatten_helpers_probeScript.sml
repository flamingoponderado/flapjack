load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_to_labTheory
 stack_allocTheory stack_allocProofTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:890-1206. *)
val _ = checked "flatten_leq_statement" flatten_leq;
val _ = checked "no_ret_correct_statement" no_ret_correct;
val _ = checked "compile_jump_correct_statement" (GEN_ALL compile_jump_correct);
val _ = checked "result_view_nchotomy_statement" (DB.fetch "stack_to_labProof" "result_view_nchotomy");
val _ = checked "result_view_def_statement" result_view_def;
val _ = checked "halt_word_view_def_statement" halt_word_view_def;
val _ = checked "halt_view_def_statement" halt_view_def;
val _ = checked "stack_to_lab_lab_pres_statement" stack_to_lab_lab_pres;
val _ = checked "stack_to_lab_lab_pres_T_statement" stack_to_lab_lab_pres_T;
val _ = checked "flatten_T_F_statement" (GEN_ALL flatten_T_F);
val _ = checked "prog_to_section_labels_ok_statement" (GEN_ALL prog_to_section_labels_ok);
val _ = checked "NOT_MEM_find_lab_IMP_statement" NOT_MEM_find_lab_IMP;
val _ = checked "is_some_loc_to_pc_prefix_statement" (GEN_ALL is_some_loc_to_pc_prefix);
val _ = checked "every_is_some_loc_to_pc_prefix_statement" (GEN_ALL every_is_some_loc_to_pc_prefix);

(* Local original, replayed with its source proof. *)
val NOT_bad_fun_return_IMP_SOME = Q.prove(
  `¬bad_fun_return q ⇒ ∃n. q = SOME n`,
  Cases_on ‘q’ \\ simp []);
val _ = checked "NOT_bad_fun_return_IMP_SOME_statement" (GEN_ALL NOT_bad_fun_return_IMP_SOME);

(* Line-1022 original, rebound at line 3211; replayed with its source proof. *)
val next_lab_non_zero_1022 = Q.prove(
  `∀p. 2 ≤ next_lab p 2`,
  once_rewrite_tac [next_lab_EQ_MAX] \\ fs [MAX_DEF]);
val _ = checked "next_lab_non_zero_1022_statement" next_lab_non_zero_1022;
