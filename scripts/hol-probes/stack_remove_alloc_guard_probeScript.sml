(* Fresh literal original full single-allocation proof includes the local
   unsigned guard argument440-506. This is oracle evidence for the arithmetic
   prerequisite only; the full Lean simulation is a separate open bead. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory addressTheory stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val ag = GEN_ALL (prove(``state_rel jump off k s t1 ∧
   ((r,s2) = if s.stack_space < n
    then (SOME (Halt (Word 2w)),empty_env s)
    else (NONE, s with stack_space := s.stack_space - n)) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_alloc jump k n,t1 with clock := t1.clock + ck) = (r,t2) ∧
     if s.stack_space < n then t2.ffi = s2.ffi else state_rel jump off k s2 t2``,
  simp[single_stack_alloc_def] \\
  Cases_on`jump` \\
  simp [evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[get_var_imm_def,get_var_def]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[wordSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ qpat_abbrev_tac`cc = c + _ + _`
  \\ `cc <+ c ⇔ s.stack_space < n`
  by (
    simp[Abbr`cc`,word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ Cases_on`c` \\ full_simp_tac(srw_ss())[]
    \\ qpat_abbrev_tac`d = _ DIV 8`
    \\ REWRITE_TAC[
         wordsLib.WORD_DECIDE ``w + -1w * v + t = w + t - v``,
         word_add_n2w]
    \\ REWRITE_TAC[addressTheory.word_arith_lemma2]
    \\ qmatch_assum_rename_tac`m < dimword _`
    \\ IF_CASES_TAC \\ simp_tac bool_ss []
    >- (
      `m < (n - s.stack_space) * d` by decide_tac
      \\ reverse (Cases_on `s.stack_space < n`)
      >- (
        `n - s.stack_space = 0` by decide_tac
        \\ `m < 0 * d` by metis_tac[] \\ full_simp_tac(srw_ss())[] )
      \\ simp[]
      \\ `m + d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [n2w_sub]
      \\ REWRITE_TAC[WORD_NEG_SUB]
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM word_add_n2w]
      \\ REWRITE_TAC[GSYM WORD_SUB_SUB]
      \\ `d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
      \\ ONCE_REWRITE_TAC[MULT_COMM]
      \\ qmatch_abbrev_tac`n2w m - n2w a <+ _`
      \\ `d ≠ 0` by ( strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,Abbr`a`] )
      \\ `0 < m` by (full_simp_tac(srw_ss())[max_stack_alloc_def,Abbr`d`] \\ decide_tac)
      \\ `d * max_stack_alloc < d * (n - s.stack_space)` by decide_tac
      \\ `max_stack_alloc < n - s.stack_space` by metis_tac[LT_MULT_LCANCEL]
      \\ decide_tac)
    \\ `(n - s.stack_space) * d ≤ m` by decide_tac
    \\ qmatch_assum_abbrev_tac`a * d ≤ m`
    \\ simp[WORD_LO]
    \\ Cases_on`s.stack_space < n`
    >- (
      `s.stack_space ≤ n` by decide_tac
      \\ `s.stack_space * d ≤ n * d` by metis_tac[LESS_MONO_MULT]
      \\ asm_simp_tac std_ss [GSYM SUB_SUB]
      \\ REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB]
      \\ simp[]
      \\ `d ≠ 0` by (strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,state_rel_def,good_dimindex_def] \\ rev_full_simp_tac(srw_ss())[])
      \\ conj_asm1_tac >- simp[]
      \\ full_simp_tac(srw_ss())[max_stack_alloc_def]
      \\ simp[] )
    \\ simp[]
    \\ simp[NOT_LESS]
    \\ `n ≤ s.stack_space` by decide_tac
    \\ simp[]
    \\ `d * n ≤ d * s.stack_space` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ asm_simp_tac std_ss [LESS_EQ_ADD_SUB]
    \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
    \\ `m + d * (s.stack_space - n) < dimword (:'a)` suffices_by (simp [])
    \\ full_simp_tac(srw_ss())[LEFT_SUB_DISTRIB]
    \\ full_simp_tac(srw_ss())[state_rel_def,bytes_in_word_def]
    \\ `d < dimword (:α)` by (UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `s.stack_space <= LENGTH s.stack` assume_tac
    \\ old_drule LESS_EQUAL_ADD \\ strip_tac \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[LEFT_ADD_DISTRIB] \\ decide_tac)
  \\ simp[]
  >- (* jump = true *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      srw_tac[][find_code_def]
      \\ qhdtm_x_assum`state_rel`mp_tac
      \\ simp[Once state_rel_def]
      \\ strip_tac
      \\ simp[halt_inst_def,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,dec_clock_def,get_var_def,FLOOKUP_UPDATE]
      \\ qexists_tac`1`
      \\ simp[] )
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ fs[bytes_in_word_def,word_mul_n2w]
    \\ metis_tac[])
  >> (* jump = false *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (simp[evaluate_def,halt_inst_def,inst_def,assign_def,word_exp_def]>>
      fs[state_rel_def])
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ fs[bytes_in_word_def,word_mul_n2w]
    \\ metis_tac[])));
val _ = print("ag_statement=" ^ term_to_string(concl ag) ^ "\n");
val _ = print("ag_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ag))) ^ "\n");
fun print_eval label q = let val th = EVAL q in print(label ^ "=" ^ term_to_string(rhs(concl th)) ^ "\n") end;
val _ = print_eval "ag_32_0" ``(((1020w:32 word) + n2w (4 * 0) - n2w (4 * 1)) <+ 1020w, (0:num) < 1)``;
val _ = print_eval "ag_32_1" ``(((1020w:32 word) + n2w (4 * 1) - n2w (4 * 1)) <+ 1020w, (1:num) < 1)``;
val _ = print_eval "ag_32_2" ``(((1020w:32 word) + n2w (4 * 254) - n2w (4 * 255)) <+ 1020w, (254:num) < 255)``;
val _ = print_eval "ag_32_3" ``(((1020w:32 word) + n2w (4 * 255) - n2w (4 * 255)) <+ 1020w, (255:num) < 255)``;
val _ = print_eval "ag_32_4" ``(((1020w:32 word) + n2w (4 * 256) - n2w (4 * 255)) <+ 1020w, (256:num) < 255)``;
val _ = print_eval "ag_64_0" ``(((2040w:64 word) + n2w (8 * 0) - n2w (8 * 1)) <+ 2040w, (0:num) < 1)``;
val _ = print_eval "ag_64_1" ``(((2040w:64 word) + n2w (8 * 1) - n2w (8 * 1)) <+ 2040w, (1:num) < 1)``;
val _ = print_eval "ag_64_2" ``(((2040w:64 word) + n2w (8 * 254) - n2w (8 * 255)) <+ 2040w, (254:num) < 255)``;
val _ = print_eval "ag_64_3" ``(((2040w:64 word) + n2w (8 * 255) - n2w (8 * 255)) <+ 2040w, (255:num) < 255)``;
val _ = print_eval "ag_64_4" ``(((2040w:64 word) + n2w (8 * 256) - n2w (8 * 255)) <+ 2040w, (256:num) < 255)``;
