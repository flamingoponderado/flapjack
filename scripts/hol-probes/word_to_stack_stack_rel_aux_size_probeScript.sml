load "preamble"; load "word_to_stackProofTheory"; load "wordPropsTheory"; load "backendPropsTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordPropsTheory
 wordSemTheory optionTheory miscTheory;
val _ = Globals.linewidth := 1000000;
(* Original fetch "-" resolves the current word_to_stackProof theory. *)
val fetch = fn thy => fn name => DB.fetch (if thy = "-" then "word_to_stackProof" else thy) name;
val the_eqn = backendPropsTheory.the_eqn;
val original = word_to_stackProofTheory.stack_rel_aux_stack_size;
val replay = GEN_ALL(prove(concl original,
ho_match_mp_tac (fetch "-" "stack_rel_aux_ind") >>
  rw[stack_rel_aux_def,stack_size_eq,handler_val_def,the_eqn,OPTION_MAP2_DEF,
     IS_SOME_EXISTS,CaseEq "option"] >>
  res_tac >> fs[]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open stack size invariant";
val _ = if aconv (concl replay) (concl(GEN_ALL original)) then () else raise Fail "statement drift";
val _ = (print "stack_rel_aux_stack_size_statement="; print_term(concl replay); print "\n");
val _ = print("stack_rel_aux_stack_size_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("stack_rel_aux_stack_size_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
val _ = (print "stack_rel_aux_type="; print_type(type_of ``word_to_stackProof$stack_rel_aux``); print "\n");
