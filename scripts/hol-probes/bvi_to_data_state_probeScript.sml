load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "compile_sing=" bvi_to_dataTheory.compile_sing_def;
val _ = show "compile=" bvi_to_dataTheory.compile_def;
val _ = show "compile_sing_eq=" bvi_to_dataTheory.compile_sing_eq;
val _ = show "compile_LENGTH=" bvi_to_dataTheory.compile_LENGTH;
val _ = show "compile_LESS_EQ=" bvi_to_dataTheory.compile_LESS_EQ;
(* The original theorems are local; capture their literal typed statements. *)
val _ = (print "compile_RANGE_lemma_statement="; print_term
  ``!n env tail live xs.
      EVERY (\v. v < (SND (SND (bvi_to_data$compile n env tail live xs))))
        (FST (SND (bvi_to_data$compile n env tail live xs)))``; print "\n");
val _ = (print "compile_RANGE_statement="; print_term
  ``!n env tail live xs ys vs k.
    (bvi_to_data$compile n env tail live xs = (ys,vs,k)) ==>
      EVERY (\v. v < k) vs``; print "\n");
val _ = show "compile_exp_eq=" bvi_to_dataTheory.compile_exp_eq;
val _ = show "compile_part=" bvi_to_dataTheory.compile_part_def;
val _ = show "compile_prog=" bvi_to_dataTheory.compile_prog_def;
val _ = show "code_rel=" bvi_to_dataProofTheory.code_rel_def;
val _ = show "state_rel=" bvi_to_dataProofTheory.state_rel_def;
val _ = show "compile_correct=" bvi_to_dataProofTheory.compile_correct;
val _ = show "data_to_bvi_do_eq=" bvi_to_dataProofTheory.data_to_bvi_do_eq;
val _ = show "data_to_bvi_do_app=" bvi_to_dataProofTheory.data_to_bvi_do_app;
val _ = show "data_to_bvi_v_list_to_v_APPEND=" bvi_to_dataProofTheory.data_to_bvi_v_list_to_v_APPEND;
val _ = show "var_corr=" dataPropsTheory.var_corr_def;
val _ = show "get_vars_thm=" dataPropsTheory.get_vars_thm;
val _ = show "get_vars_append=" dataPropsTheory.get_vars_append;
val _ = show "get_vars_reverse=" dataPropsTheory.get_vars_reverse;
val _ = show "EVERY_get_vars=" dataPropsTheory.EVERY_get_vars;
val _ = show "get_vars_IMP_domain=" dataPropsTheory.get_vars_IMP_domain;
val _ = show "do_app_aux_err=" dataPropsTheory.do_app_aux_err;
val _ = show "do_app_err=" dataPropsTheory.do_app_err;
val _ = show "do_app_aux_const=" dataPropsTheory.do_app_aux_const;
val _ = show "do_app_const=" dataPropsTheory.do_app_const;
val _ = show "var_corr_map=" bvi_to_dataProofTheory.var_corr_map;
val _ = show "get_vars_lift_thm=" bvi_to_dataProofTheory.get_vars_lift_thm;
val _ = show "var_corr_inter=" bvi_to_dataProofTheory.var_corr_inter;
val _ = show "get_vars_mk_wf=" bvi_to_dataProofTheory.get_vars_mk_wf;
val _ = show "get_vars_inter=" bvi_to_dataProofTheory.get_vars_inter;
val _ = show "lookup_mk_wf=" sptreeTheory.lookup_mk_wf;
val _ = show "data_to_bvi_result=" bvi_to_dataProofTheory.data_to_bvi_result_def;
val _ = show "data_to_bvi_result_eq=" bvi_to_dataProofTheory.data_to_bvi_result_eq;
val _ = show "missing_var=" (EVAL ``bvi_to_data$compile_sing 4 [] F [] (bvi$Var 5)``);
val _ = show "tail_var=" (EVAL ``bvi_to_data$compile_sing 4 [7] T [] (bvi$Var 0)``);
val _ = show "tail_letcall=" (EVAL ``bvi_to_data$compile_sing 2 [] F []
  (bvi$LetCall 1 0 3 [] (bvi$Return [bvi$Var 0]))``);
