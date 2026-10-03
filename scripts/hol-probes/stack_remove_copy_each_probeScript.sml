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
val copy_each_replay = prove(``∀pattern i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c) stackSem$state).
    copy_words_for_pattern pattern i a off bs d m = SOME (i1,a1,m1) ∧
    ALL_DISTINCT [1;2;3;t1;t2] ∧ dm = t.mdomain ∧ good_dimindex (:'a) ∧
    get_var 1 t = SOME (Word pattern) ∧ d SUBSET dm ∧
    get_var 2 t = SOME (Word (a:'a word)) ∧
    get_var 3 t = SOME (Word off) ∧
    get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) ∧
    (word_list x (MAP Word bs) * rest * memory m d) (fun2set (t.memory,dm)) ⇒
    ∃ck y m2.
      evaluate (copy_each t1 t2, t with clock := t.clock + ck) =
        (NONE, t with <| memory := m2 ;
                         regs := ((if pattern = 1w then t.regs else t.regs |+ (t1,Word y))
                           |+ (2,Word a1) |+ (1,Word 1w)
                           |+ (t2, Word (x + bytes_in_word * n2w i1))) |>) ∧
      (word_list x (MAP Word bs) * rest * memory m1 d) (fun2set (m2,dm))``,
  ho_match_mp_tac copy_words_for_pattern_ind
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [copy_words_for_pattern_def]
  \\ Cases_on ‘pattern = 1w’ \\ fs []
  THEN1
   (fs [copy_each_def,evaluate_def]
    \\ fs [get_var_def,get_var_imm_def,wordSemTheory.word_cmp_def]
    \\ fs [state_component_equality]
    \\ rw [] \\ gvs []
    \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
    \\ rw [] \\ eq_tac \\ rw []\\ fs [])
  \\ rpt strip_tac \\ gvs []
  \\ simp [copy_each_def]
  \\ once_rewrite_tac [evaluate_def]
  \\ fs [get_var_def,get_var_imm_def,asmTheory.word_cmp_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def]
  \\ old_drule miscTheory.LESS_LENGTH
  \\ strip_tac \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_R_TAC \\ gvs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,wordSemTheory.word_cmp_def]
  \\ qspec_then ‘pattern’ assume_tac (word_bit_test |> Q.INST [‘n’|->‘0’] |> GEN_ALL)
  \\ fs [word_bit_def]
  \\ Cases_on ‘1w && pattern = 0w’ \\ fs []
  \\ ‘32 ≤ dimindex (:'a)’ by fs [good_dimindex_def]
  \\ fs [SUBSET_DEF] \\ res_tac \\ fs []
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,wordSemTheory.word_cmp_def,list_Seq_def,
         wordLangTheory.word_sh_def,mem_store_def,dec_clock_def]
  \\ rewrite_tac [STOP_def]
  \\ fs [copy_each_def,list_Seq_def]
  \\ (fn x =>
        qexists_tac ‘1’ x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ fs [EL_LENGTH_APPEND]
  \\ last_x_assum (qspecl_then [‘x’,‘t8’] mp_tac)
  \\ (impl_tac
      THEN1
       (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
        \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ once_rewrite_tac [STAR_COMM]
        \\ irule memory_write \\ fs []
        \\ fs [AC STAR_ASSOC STAR_COMM])
      \\ strip_tac
      \\ unabbrev_all_tac \\ fs []
      \\ qexists_tac ‘ck + 1’
      \\ fs [state_component_equality]
      \\ rw []
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []
      \\ TRY (qexists_tac ‘y’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC)
      \\ TRY (qexists_tac ‘y+off’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC)
      \\ TRY (qexists_tac ‘y'’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC)));
val _ = print("copy_each_statement=" ^ term_to_string(concl copy_each_replay) ^ "\n");
val _ = print("copy_each_proved=" ^ term_to_string(rhs(concl(EQT_INTRO copy_each_replay))) ^ "\n");
