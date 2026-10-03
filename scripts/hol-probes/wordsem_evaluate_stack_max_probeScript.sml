load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory backendPropsTheory;
val _ = Globals.linewidth := 1000000;
fun closed name th =
  if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail ("open " ^ name);
fun same name th original =
  if aconv (concl th) (concl(GEN_ALL original)) then () else raise Fail ("statement drift " ^ name);
(* The two recursive laws are exported theorems; their source proofs use
   [local] helpers that are not exported, so their closed statements are
   captured. The four derived laws are replayed with their literal proofs. *)
val _ = closed "evaluate_stack_max_le" ((GEN_ALL evaluate_stack_max_le));
val _ = (print "evaluate_stack_max_le_statement="; print_term(concl((GEN_ALL evaluate_stack_max_le))); print "\n");
val _ = print("evaluate_stack_max_le_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL evaluate_stack_max_le)))) ^ "\n");
val _ = closed "evaluate_stack_limit" ((GEN_ALL evaluate_stack_limit));
val _ = (print "evaluate_stack_limit_statement="; print_term(concl((GEN_ALL evaluate_stack_limit))); print "\n");
val _ = print("evaluate_stack_limit_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL evaluate_stack_limit)))) ^ "\n");
val stack_max_replay = GEN_ALL(prove(concl evaluate_stack_max,
  rpt gen_tac >>
  disch_then (mp_tac o HO_MATCH_MP evaluate_stack_max_le) >>
  gvs[oneline miscTheory.the_def,oneline option_le_def] >>
  every_case_tac >> fs[]));
val _ = same "evaluate_stack_max" stack_max_replay evaluate_stack_max;
val _ = closed "evaluate_stack_max" (stack_max_replay);
val _ = (print "evaluate_stack_max_statement="; print_term(concl(stack_max_replay)); print "\n");
val _ = print("evaluate_stack_max_hypotheses=" ^ Int.toString(length(hyp(stack_max_replay))) ^ "\n");
val is_some_replay = GEN_ALL(prove(concl evaluate_stack_max_IS_SOME,
  rw[] >> dxrule_then assume_tac evaluate_stack_max >>
  PURE_FULL_CASE_TAC >> fs[]));
val _ = same "evaluate_stack_max_IS_SOME" is_some_replay evaluate_stack_max_IS_SOME;
val _ = closed "evaluate_stack_max_IS_SOME" (is_some_replay);
val _ = (print "evaluate_stack_max_IS_SOME_statement="; print_term(concl(is_some_replay)); print "\n");
val _ = print("evaluate_stack_max_IS_SOME_hypotheses=" ^ Int.toString(length(hyp(is_some_replay))) ^ "\n");
val eq_replay = GEN_ALL(prove(concl evaluate_stack_limit_stack_max_eq,
  rpt strip_tac >>
  imp_res_tac evaluate_stack_max >>
  imp_res_tac evaluate_stack_limit >>
  fs[the_eqn] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)));
val _ = same "evaluate_stack_limit_stack_max_eq" eq_replay evaluate_stack_limit_stack_max_eq;
val _ = closed "evaluate_stack_limit_stack_max_eq" (eq_replay);
val _ = (print "evaluate_stack_limit_stack_max_eq_statement="; print_term(concl(eq_replay)); print "\n");
val _ = print("evaluate_stack_limit_stack_max_eq_hypotheses=" ^ Int.toString(length(hyp(eq_replay))) ^ "\n");
val lt_replay = GEN_ALL(prove(concl evaluate_stack_limit_stack_max,
  rpt strip_tac >>
  imp_res_tac evaluate_stack_max >>
  imp_res_tac evaluate_stack_limit >>
  fs[the_eqn] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)));
val _ = same "evaluate_stack_limit_stack_max" lt_replay evaluate_stack_limit_stack_max;
val _ = closed "evaluate_stack_limit_stack_max" (lt_replay);
val _ = (print "evaluate_stack_limit_stack_max_statement="; print_term(concl(lt_replay)); print "\n");
val _ = print("evaluate_stack_limit_stack_max_hypotheses=" ^ Int.toString(length(hyp(lt_replay))) ^ "\n");
val _ = closed "share_inst_const" ((GEN_ALL share_inst_const));
val _ = (print "share_inst_const_statement="; print_term(concl((GEN_ALL share_inst_const))); print "\n");
val _ = print("share_inst_const_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL share_inst_const)))) ^ "\n");
val _ = closed "cut_state_const" ((GEN_ALL cut_state_const));
val _ = (print "cut_state_const_statement="; print_term(concl((GEN_ALL cut_state_const))); print "\n");
val _ = print("cut_state_const_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL cut_state_const)))) ^ "\n");
val _ = closed "option_le_trans" ((GEN_ALL option_le_trans));
val _ = (print "option_le_trans_statement="; print_term(concl((GEN_ALL option_le_trans))); print "\n");
val _ = print("option_le_trans_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL option_le_trans)))) ^ "\n");
val _ = closed "option_le_max_right" ((GEN_ALL option_le_max_right));
val _ = (print "option_le_max_right_statement="; print_term(concl((GEN_ALL option_le_max_right))); print "\n");
val _ = print("option_le_max_right_hypotheses=" ^ Int.toString(length(hyp((GEN_ALL option_le_max_right)))) ^ "\n");
val _ = (print "option_le_def="; print_term (concl option_le_def); print "\n");
