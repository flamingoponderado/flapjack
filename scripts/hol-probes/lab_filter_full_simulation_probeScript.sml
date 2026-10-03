load "bossLib";
load "preamble";
load "lab_filterProofTheory";
open bossLib HolKernel Parse preamble labSemTheory lab_filterTheory lab_filterProofTheory;
(* Exact temporary simplifier setup from original script lines10/12. *)
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = temp_delsimps ["NORMEQ_CONV"];
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
fun types label th = (print(label ^ "=");app(fn v=>print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))(fst(strip_forall(concl th)) @ free_vars(concl th));print "\n");
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO (prove(concl th,ACCEPT_TAC th)))));print "\n");
val th = DB.fetch "lab_filterProof" "filter_correct";
val _ = show_types := true;
val _ = capture "filter_correct" th;
val _ = types "filter_correct_types" th;
val _ = print("filter_correct_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "filter_correct_proved" th;
