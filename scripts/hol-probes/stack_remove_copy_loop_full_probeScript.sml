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
val copy_loop_replay = prove(``  ∀i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c) stackSem$state).
    copy_words i a off bs d m = SOME (a1,m1) ∧
    ALL_DISTINCT [1;2;3;t1;t2] ∧ dm = t.mdomain ∧ good_dimindex (:'a) ∧
    d SUBSET dm ∧
    get_var 2 t = SOME (Word (a:'a word)) ∧
    get_var 3 t = SOME (Word off) ∧
    get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) ∧
    (word_list x (MAP Word bs) * rest * memory m d) (fun2set (t.memory,dm)) ⇒
    ∃ck b y y2 m2.
      evaluate (copy_loop t1 t2, t with clock := t.clock + ck) =
        (NONE, t with <| memory := m2 ;
                         regs := ((if b then t.regs else t.regs |+ (t1,Word y))
                           |+ (2,Word a1) |+ (1,Word 1w) |+ (t2,Word y2)) |>) ∧
      (word_list x (MAP Word bs) * rest * memory m1 d) (fun2set (m2,dm))``,
  ho_match_mp_tac copy_words_ind
  \\ rpt gen_tac \\ strip_tac
  \\ simp [Once copy_words_def]
  \\ Cases_on ‘copy_words_for_pattern (EL i bs) (i + 1) a off bs d m’
  \\ fs [] \\ PairCases_on ‘x’ \\ fs []
  \\ rpt strip_tac \\ gvs [wordsTheory.word_msb_neg]
  \\ simp [copy_loop_def]
  \\ simp [Once list_Seq_def]
  \\ simp [Once list_Seq_def]
  \\ ‘x' + bytes_in_word * n2w i ∈ t.mdomain ∧
      t.memory (x' + bytes_in_word * n2w i) = Word (EL i bs)’ by
   (fs [GSYM NOT_LESS] \\ old_drule LESS_LENGTH
    \\ strip_tac \\ gvs []
    \\ fs [word_list_def,word_list_APPEND] \\ SEP_R_TAC
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND])
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ reverse (Cases_on ‘EL i bs < 0w’) \\ gvs []
  THEN1
   (simp [EVAL “list_Seq [_;_]”]
    \\ fs [evaluate_def,get_var_def,get_var_imm_def,wordSemTheory.word_cmp_def,inst_def,
           word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
           set_var_def,FLOOKUP_UPDATE]
    \\ (fn x =>
        qexists_tac ‘0’ x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
    \\ old_drule copy_each_thm \\ fs []
    \\ disch_then (qspecl_then [‘x'’,‘t8’] mp_tac)
    \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def]
    \\ impl_tac
    THEN1 (gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
    \\ strip_tac
    \\ qexists_tac ‘ck’
    \\ fs [] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [state_component_equality]
    \\ qexists_tac ‘EL i bs = 1w’ \\ fs []
    \\ rw [] \\ fs []
    THEN1
     (qexists_tac ‘(x' + bytes_in_word * n2w x0)’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
    THEN1
     (qexists_tac ‘y’
      \\ qexists_tac ‘x' + bytes_in_word * n2w x0’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []))
  \\ simp [EVAL “list_Seq [_;_]”]
  \\ (fn x =>
        (qexists_tac ‘0’ \\ qexists_tac ‘ARB’ \\ qexists_tac ‘ARB’ \\ qexists_tac ‘ARB’) x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,wordSemTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac ‘ttt = STOP _’
  \\ simp [Once list_Seq_def]
  \\ old_drule copy_each_thm \\ fs []
  \\ disch_then (qspecl_then [‘x'’,‘t8’] mp_tac)
  \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def]
  \\ impl_tac
  THEN1 (gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ (fn x =>
        x |> snd |> dest_imp |> fst |> rand |> rand
          |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ rw []
  \\ last_x_assum (qspecl_then [‘x'’,‘t8’] mp_tac)
  \\ impl_tac
  THEN1
   (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
    \\ rw [] \\ fs [FLOOKUP_UPDATE])
  \\ rw []
  \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
  \\ qpat_x_assum ‘evaluate (copy_each t1 t2,_) = _’ assume_tac
  \\ old_drule (evaluate_add_clock |> GEN_ALL) \\ fs []
  \\ disch_then (qspec_then ‘ck'+1’ assume_tac)
  \\ qexists_tac ‘ck+ck'+1’
  \\ fs [evaluate_def]
  \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ ntac 2 (pop_assum kall_tac)
  \\ fs [list_Seq_def]
  \\ qpat_x_assum ‘evaluate (copy_loop t1 t2,_) = _’ mp_tac
  \\ rewrite_tac [copy_loop_def,list_Seq_def,STOP_def]
  \\ qpat_abbrev_tac ‘ttt = While _ _ _ _’
  \\ simp [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ simp [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,dec_clock_def]
  \\ disch_then kall_tac
  \\ fs [state_component_equality]
  THEN1
   (qexists_tac ‘b’ \\ rw []
    THEN1
     (qexists_tac ‘y2’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
    THEN1
     (qexists_tac ‘y'’
      \\ qexists_tac ‘y2’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []))
  \\ Cases_on ‘b’ \\ fs []
  THEN1
   (qexists_tac ‘F’
    \\ qexists_tac ‘y’
    \\ qexists_tac ‘y2’
    \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
    \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
  \\ qexists_tac ‘F’
  \\ qexists_tac ‘y'’
  \\ qexists_tac ‘y2’
  \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
  \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []);
val _ = print("copy_loop_statement=" ^ term_to_string(concl copy_loop_replay) ^ "\n");
val _ = print("copy_loop_proved=" ^ term_to_string(rhs(concl(EQT_INTRO copy_loop_replay))) ^ "\n");
