load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory;
val _ = Globals.linewidth := 1000000;
(* The script-local overload of stack_removeProofScript.sml:17. *)
val _ = overload_on ("num_stubs", ``stack_num_stubs``);

(* Local original 3988-4005, replayed unchanged. *)
val IMP_code_rel = prove(
  ``EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code1 /\
   code2 = fromAList (compile jump off gen_gc max_heap k start code1) ==>
   code_rel jump off k (fromAList code1) code2``,
  rw[]>>
  fs[code_rel_def,lookup_fromAList]>>
  CONJ_TAC>- (
    fs[ALOOKUP_def,compile_def,init_stubs_def] \\ rw []
    \\ rpt var_eq_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac EVERY_MEM \\ full_simp_tac(srw_ss())[]
    \\ simp[prog_comp_eta,ALOOKUP_MAP_2]
    \\ pop_assum mp_tac \\ EVAL_TAC)>>
  simp[domain_fromAList,compile_def,init_stubs_def,prog_comp_eta,MAP_MAP_o,UNCURRY,o_DEF,ETA_AX]>>
  simp[EXTENSION]>>
  metis_tac[]);
val _ = (print "IMP_code_rel_statement="; print_term (concl (GEN_ALL IMP_code_rel)); print "\n");
val _ = print ("IMP_code_rel_hypotheses=" ^ Int.toString (length (hyp IMP_code_rel)) ^ "\n");

(* Exported originals 3856-3986 and 4069-4086. *)
val _ = (print "evaluate_init_code_statement="; print_term (concl (GEN_ALL evaluate_init_code)); print "\n");
val _ = print ("evaluate_init_code_hypotheses=" ^ Int.toString (length (hyp evaluate_init_code)) ^ "\n");
val _ = (print "init_semantics_statement="; print_term (concl (GEN_ALL init_semantics)); print "\n");
val _ = print ("init_semantics_hypotheses=" ^ Int.toString (length (hyp init_semantics)) ^ "\n");
val _ = (print "make_init_opt_SOME_semantics_statement="; print_term (concl (GEN_ALL make_init_opt_SOME_semantics)); print "\n");
val _ = print ("make_init_opt_SOME_semantics_hypotheses=" ^ Int.toString (length (hyp make_init_opt_SOME_semantics)) ^ "\n");
val _ = (print "make_init_semantics_statement="; print_term (concl (GEN_ALL make_init_semantics)); print "\n");
val _ = print ("make_init_semantics_hypotheses=" ^ Int.toString (length (hyp make_init_semantics)) ^ "\n");
