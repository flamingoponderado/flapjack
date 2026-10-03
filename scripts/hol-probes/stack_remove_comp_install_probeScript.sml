load "preamble";
load "helperLib";
open helperLib;
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory byteTheory miscTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val state_rel_get_var = GEN_ALL (prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]));
val cc_install = prove(``!ptr len dptr dlen ret s1 r s2 t1 k off jump.
 evaluate (Install ptr len dptr dlen ret,s1) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k s1 t1 /\ reg_bound (Install ptr len dptr dlen ret) k ==>
 ?ck t2. evaluate (comp jump off k (Install ptr len dptr dlen ret),t1 with clock := ck + t1.clock) = (r,t2) /\
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
    \\ fs[get_var_def]
    \\ ntac 8 (TOP_CASE_TAC \\ fs[])
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rveq
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rewrite_tac[GSYM MAP]
    \\ qmatch_goalsub_abbrev_tac`fromAList code`
    \\ simp[prog_comp_eta]
    \\ TOP_CASE_TAC \\ fs[]
    \\ simp[shift_seq_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ conj_tac >- (
      simp[FUN_EQ_THM,prog_comp_eta] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      simp[FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] )
    \\ conj_tac >- (
      qhdtm_x_assum`code_rel`mp_tac \\
      simp[code_rel_def,lookup_union,lookup_fromAList] \\
      strip_tac >>
      conj_tac>-(
        ntac 2 strip_tac \\
        reverse TOP_CASE_TAC >- (
          strip_tac  \\ rveq \\
          res_tac \\ simp[] ) \\
        strip_tac \\ imp_res_tac ALOOKUP_MEM \\
        simp[ALOOKUP_MAP_2] \\
        last_x_assum(qspec_then`0` mp_tac)>>simp[]>>
        disch_then old_drule>>strip_tac>>simp[]>>
        CASE_TAC>>fs[EXTENSION,domain_lookup,PULL_EXISTS]>>
        first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
        fs[backend_commonTheory.stack_num_stubs_def])>>
     simp[domain_union,domain_fromAList,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]>>
     metis_tac[UNION_COMM,UNION_ASSOC])
    \\ conj_tac >- simp[lookup_union]
    \\ conj_tac >- (
      simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] \\
      rfs[] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      fs[wordSemTheory.buffer_flush_def]
      \\ rveq \\ fs[GSYM bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w] )
    \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ conj_tac >- metis_tac[]
    \\ fs[wordSemTheory.buffer_flush_def]
    \\ rveq \\ fs[]);
val _ = if null(hyp cc_install) andalso null(free_vars(concl cc_install)) then () else raise Fail "open theorem";
val _ = print("cc_install_statement=" ^ term_to_string(concl cc_install) ^ "\n");
val _ = print("cc_install_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_install))) ^ "\n");
