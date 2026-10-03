load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
fun closed name th =
  if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail ("open " ^ name);
fun same name th original =
  if aconv (concl th) (concl(GEN_ALL original)) then () else raise Fail ("statement drift " ^ name);
(* evaluate_consts uses the [local] inst_code_gc_fun_const, which is not
   exported, so its closed statement is captured; the two exported helpers
   are replayed with their literal proofs. *)
val _ = closed "evaluate_consts" (GEN_ALL evaluate_consts);
val _ = (print "evaluate_consts_statement="; print_term(concl(GEN_ALL evaluate_consts)); print "\n");
val _ = print("evaluate_consts_hypotheses=" ^ Int.toString(length(hyp(GEN_ALL evaluate_consts))) ^ "\n");
val pop_replay = GEN_ALL(prove(concl pop_env_code_gc_fun_clock,
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[state_component_equality]));
val _ = same "pop_env_code_gc_fun_clock" pop_replay pop_env_code_gc_fun_clock;
val _ = closed "pop_env_code_gc_fun_clock" pop_replay;
val _ = (print "pop_env_code_gc_fun_clock_statement="; print_term(concl pop_replay); print "\n");
val _ = print("pop_env_code_gc_fun_clock_hypotheses=" ^ Int.toString(length(hyp pop_replay)) ^ "\n");
val alloc_replay = GEN_ALL(prove(concl alloc_code_gc_fun_const,
  fs[alloc_def,gc_def,LET_THM]>>EVERY_CASE_TAC>>
  fs[call_env_def,push_env_def,LET_THM,env_to_list_def
    ,set_store_def,state_component_equality,flush_state_def]>>
  imp_res_tac pop_env_code_gc_fun_clock>>fs[]));
val _ = same "alloc_code_gc_fun_const" alloc_replay alloc_code_gc_fun_const;
val _ = closed "alloc_code_gc_fun_const" alloc_replay;
val _ = (print "alloc_code_gc_fun_const_statement="; print_term(concl alloc_replay); print "\n");
val _ = print("alloc_code_gc_fun_const_hypotheses=" ^ Int.toString(length(hyp alloc_replay)) ^ "\n");
