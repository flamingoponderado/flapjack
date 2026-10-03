load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val state_rel_get_var=prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]);
val cc_code_buffer = prove(``!r1 r2 s r s2 t1 k off jump. evaluate ((CodeBufferWrite r1 r2),s) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s t1 /\ reg_bound (CodeBufferWrite r1 r2) k ==>
     ?ck t2. evaluate (comp jump off k (CodeBufferWrite r1 r2),t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2))``,
 rpt strip_tac >>

    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def]
    \\ ntac 5 (TOP_CASE_TAC \\ fs[])
    \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ metis_tac[]);
val _ = print("cc_code_buffer_statement=" ^ term_to_string(concl cc_code_buffer) ^ "\n");
val _ = print("cc_code_buffer_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_code_buffer))) ^ "\n");
