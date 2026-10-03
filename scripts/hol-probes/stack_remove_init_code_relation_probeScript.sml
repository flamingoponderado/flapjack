load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory stackPropsTheory stackSemTheory stackLangTheory sptreeTheory;
val _ = Globals.linewidth := 20000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = overload_on ("num_stubs", ``stack_num_stubs``);
val full_code_relation = GEN_ALL(prove(``EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code1 /\
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
  metis_tac[]));
val _ = print ("init_code_relation_statement=" ^ term_to_string(concl full_code_relation) ^ "\n");
val _ = print ("init_code_relation_hypotheses=" ^ Int.toString(length(hyp full_code_relation)) ^ "\n");
val _ = print ("init_code_relation_proved=T\n");
