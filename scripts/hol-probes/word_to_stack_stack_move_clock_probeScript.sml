load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory wordSemTheory stackSemTheory wordLangTheory stackLangTheory
 wordsTheory arithmeticTheory listTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
(* Original local Q.prove proof unchanged; GEN_ALL closes original free clk. *)
val original = GEN_ALL (Q.prove(`
  ∀a b c d (t:('a,'c,'ffi)stackSem$state).
  let prog = stack_move a b c d Skip in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))`,
  Induct>>fs[LET_THM,stack_move_def,stackSemTheory.evaluate_def]>>rw[]>>
  TRY(pairarg_tac>>fs[])>>
  simp[]>>
  (*get_var_set_var?*)
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE])|>SIMP_RULE arith_ss [LET_THM]);
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "evaluate_stack_move_clock_statement="; print_term(concl original); print "\n");
val _ = print("evaluate_stack_move_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("evaluate_stack_move_clock_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
