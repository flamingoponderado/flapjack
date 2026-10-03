load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 1000000;
val state_rel_get_var = GEN_ALL (prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
full_simp_tac(srw_ss())[state_rel_def,get_var_def]));
val state_rel_IMP = GEN_ALL (prove(``state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)``,
srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]));
val cc_shmem = prove(``!op register base offset s1 r s2 t1 k off jump.
 evaluate (ShMemOp op register (Addr base offset),s1) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k s1 t1 /\ reg_bound (ShMemOp op register (Addr base offset)) k ==>
 ?ck t2. evaluate (comp jump off k (ShMemOp op register (Addr base offset)),t1 with clock := ck + t1.clock) = (r,t2) /\
 (case r of SOME (Halt _) => t2.ffi = s2.ffi
 | SOME TimeOut => t2.ffi = s2.ffi
 | SOME (FinalFFI _) => t2.ffi = s2.ffi
 | _ => state_rel jump off k s2 t2)``,
 rpt strip_tac >>
rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def,word_exp_def,IS_SOME_EXISTS,
         wordLangTheory.word_op_def]>>
    ntac 2 (FULL_CASE_TAC>>fs[])
    \\ fs[CaseEq"bool"]
    >- (imp_res_tac state_rel_IMP>>
        gvs[empty_env_def,state_rel_def]>>
        TRY (qexists_tac`0`)>>gvs[])>>
    qexists_tac ‘0’>>gs[]>>
    imp_res_tac state_rel_IMP
    \\ Cases_on ‘op’
    \\ fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
          sh_mem_load32_def,sh_mem_store32_def,
          sh_mem_load16_def,sh_mem_store16_def,
          sh_mem_load_byte_def,sh_mem_store_byte_def,get_var_def]
    \\ imp_res_tac state_rel_get_var >> fs[get_var_def]
    \\ ntac 2 (TOP_CASE_TAC>>fs[]) >>TRY (ntac 2 (CASE_TAC>>fs[]))>>
    rveq>>simp[]>>
    fs[state_rel_def,state_component_equality,FLOOKUP_UPDATE,dec_clock_def]>>rfs[]>>
    metis_tac[]);
val _ = if null(hyp cc_shmem) andalso null(free_vars(concl cc_shmem)) then () else raise Fail "open theorem";
val _ = print("cc_shmem_statement=" ^ term_to_string(concl cc_shmem) ^ "\n");
val _ = print("cc_shmem_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_shmem))) ^ "\n");
