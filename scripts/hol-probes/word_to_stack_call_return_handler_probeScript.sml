load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble helperLib;
open semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory
  wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_insert",
  "domain_inter", "domain_map", "domain_difference", "sptree.map_def",
  "sptree.lookup_rwts", "sptree.insert_notEmpty", "misc.max3_def"];
val _ = numLib.temp_prefer_num();
val _ = Parse.hide "B";
val LASTN_LENGTH_ID2 = prove (``  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack``,
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID]);
val abs_stack_IMP_LENGTH = prove (``  ∀bs wstack sstack lens stack.
    abs_stack bs wstack sstack lens = SOME stack ⇒ LENGTH stack = LENGTH wstack ∧ LENGTH lens = LENGTH wstack``,
  recInduct abs_stack_ind
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []);
val abs_stack_to_stack_LENGTH = prove (``  ∀bs wstack sstack lens stack.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val stack = LENGTH sstack``,
  ho_match_mp_tac abs_stack_ind>>rw[]>>
  fs[abs_stack_def,LET_THM]>>TRY(Cases_on`w`)>>
  fs[full_read_bitmap_def]
  >-
    (pop_assum sym_sub_tac>>fs[handler_val_def])
  >-
    (pop_assum mp_tac>>
    ntac 4 TOP_CASE_TAC>>fs[]>>rw[]>>
    simp[handler_val_def])
  >>
    (pop_assum mp_tac>>
    ntac 7 TOP_CASE_TAC>>fs[]>>
    rw[]>>
    simp[handler_val_def]));
val DROP_SUB = prove (``  a ≤ LENGTH ls ∧ b ≤ a ⇒
  DROP (a-b) ls = (DROP(a-b) (TAKE a ls))++ DROP a ls``,
  rw[]>>
  Q.ISPECL_THEN[`a`,`ls`] mp_tac(GSYM TAKE_DROP)>>
  disch_then SUBST_ALL_TAC>>
  simp[GSYM DROP_APPEND1]);
val DROP_SUB2 = prove (``  ∀a ls b.
  b ≤ a ∧
  a = LENGTH ls ⇒
  ∃rest.
  DROP (a-b) ls = rest ∧ LENGTH rest = b``,
  Induct>>
  fs[]>>rw[]>>
  simp[]);
val stack_rel_DROP_SOME = prove (``  stack_rel k whandler (StackFrame n l0 l (SOME (whandler',b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  stack_rel k whandler' wstack (SOME(EL 2 sstack)) (DROP (f'+4) sstack) len bs lens``,
  simp[stack_rel_def]>>rw[]>>
  Cases_on`sstack`>>fs[abs_stack_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
  rpt (TOP_CASE_TAC>>simp[])>>
  rw[]>>fs[stack_rel_aux_def]>>
  qpat_x_assum`P ⇒A=B` mp_tac>>
  simp[]>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[]);
val stack_rel_cons_LEN_SOME = prove (``  stack_rel k whandler (StackFrame n l0 l (SOME(a,b,c))::wstack) shandler sstack len bs (f'::lens) ⇒
  f'+4 ≤ LENGTH sstack``,
  simp[stack_rel_def]>>Cases_on`sstack`>>simp[abs_stack_def]>>
  rpt TOP_CASE_TAC>>simp[]);
val evaluate_PushHandler = prove (``  3 ≤ t.stack_space ∧
  state_rel ac k 0 0 (push_env x' NONE s with <|locals:=LN; locals_size:=SOME 0|>) t (f'::lens) 0 ∧
  loc_check t.code (x''2,x''3) ⇒
  ∃t':('a,'c,'ffi)stackSem$state.
  evaluate(PushHandler F (x''2:num) (x''3:num) (k,f:num,f'),t) = (NONE,t') ∧
  t' = t with <|stack_space:=t'.stack_space; regs:=t'.regs;stack:=t'.stack;store:=t'.store|> ∧
  (∀n.
    n < LENGTH t.stack - t.stack_space ⇒
    EL n (DROP t.stack_space t.stack) = EL (n+3) (DROP t'.stack_space t'.stack)) ∧
  (∀i. i ≠ k ⇒ get_var i t' = get_var i t) ∧
  t'.stack_space +3 = t.stack_space ∧
  LENGTH t'.stack = LENGTH t.stack ∧
  state_rel ac k 0 0 (push_env x' (SOME (x''0,x''1:'a wordLang$prog,x''2,x''3)) s with <|locals:=LN; locals_size:=SOME 0|>) t' (f'::lens) 0``,
  rw[]>>
  `t.use_stack ∧ t.use_store ∧ t.stack_space -3 < LENGTH t.stack ∧ ∃h. FLOOKUP t.store Handler = SOME h` by
    (fs[state_rel_def,flookup_thm]>>
    simp[])>>
  simp[PushHandler_F,stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
       stackSemTheory.word_exp_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,stackSemTheory.set_store_def]>>
  fs[state_rel_def]>>
  simp[FLOOKUP_UPDATE]>>
  fs[push_env_def,env_to_list_def,LET_THM,lookup_def]>>
  CONJ_TAC>-
    simp[DROP_LUPDATE,EL_LUPDATE,EL_DROP]>>
  CONJ_TAC>-
    metis_tac[]>>
  CONJ_TAC>- (
    fs[stack_size_rel_def,stack_size_eq] >>
    rpt strip_tac >> fs[] >> rveq >>
    simp[MAX_DEF]) >>
  fs[stack_rel_def]>>
  CONJ_TAC>-
    fs[sorted_env_def]>>
  simp[DROP_LUPDATE]>>
  `∃a b c ts. DROP (t.stack_space-3) t.stack = a::b::c::DROP t.stack_space t.stack` by
    (simp[DROP_SUB]>>
    simp[TAKE_TAKE_MIN,LENGTH_TAKE,DROP_LENGTH_NIL_rwt]>>
    imp_res_tac (DROP_SUB2|>INST_TYPE[alpha|->``:'a word_loc``])>>
    first_x_assum(qspec_then`TAKE t.stack_space t.stack` mp_tac)>>
    impl_tac>- simp[]>>
    strip_tac>>
    qpat_x_assum`A=rest` SUBST_ALL_TAC>>
    Cases_on`rest`>>fs[]>>
    Cases_on`t'`>>fs[]>>
    Cases_on`t''`>>fs[ADD1]>>
    Cases_on`t'`>>fs[ADD1]>>
    DECIDE_TAC)>>
  fs[LUPDATE_compute]>>
  qpat_x_assum`abs_stack A B C D = SOME stack` mp_tac>>
  Cases_on`DROP t.stack_space t.stack`>>simp[abs_stack_def]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  imp_res_tac abs_stack_IMP_LENGTH>>
  simp[ADD1]>>rw[]
  >- (
    (*stackLang handler needs to be updated*)
    simp[handler_val_def,LASTN_LENGTH_ID2,LASTN_CONS]>>
    qpat_x_assum`LENGTH x'' =LENGTH s.stack` sym_sub_tac>>
    simp[LASTN_LENGTH_ID]>>
    imp_res_tac abs_stack_to_stack_LENGTH>>
    simp[]>>
    qpat_x_assum `A=h'::t'` (mp_tac o Q.AP_TERM `LENGTH`)>>
    simp[]) >>
  fs[stack_rel_aux_def]>>
  rw[]>>
  qpat_x_assum`A ∧ B ⇒ C` mp_tac>>
  simp[]>>
  `SUC (LENGTH s.stack) - (s.handler+1) = SUC(LENGTH s.stack - (s.handler+1))` by DECIDE_TAC>>
  fs[handler_val_def,GSYM ADD1]>>
  rw[]>>
  simp[LASTN_CONS]);
val evaluate_PushHandler_clock = prove (``  ∀(t:('a,'c,'ffi)stackSem$state).
  evaluate (PushHandler F a b (k,f:num,f':num),t with clock:=clk) =
  (FST (evaluate(PushHandler F a b (k,f:num,f':num),t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(PushHandler F a b (k,f:num,f':num),t)) with clock:=clk))``,
  simp[PushHandler_def,stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
       stackSemTheory.word_exp_def,stackSemTheory.get_var_def,stackSemTheory.set_var_def,stackSemTheory.set_store_def]>>rw[]>>
  TOP_CASE_TAC>>fs[empty_env_def,FLOOKUP_UPDATE]>>
  rpt(TOP_CASE_TAC>>fs[]));
fun row label theorem = (print(label ^ "="); print_term(concl theorem));
val _ = row "handler_StackHandlerArgs_F" StackHandlerArgs_F;
val _ = print("handler_StackHandlerArgs_F_hypotheses=" ^ Int.toString(length(hyp StackHandlerArgs_F)) ^ "\n");
val _ = row "handler_PushHandler_F" PushHandler_F;
val _ = print("handler_PushHandler_F_hypotheses=" ^ Int.toString(length(hyp PushHandler_F)) ^ "\n");
val _ = row "handler_PopHandler_F" PopHandler_F;
val _ = print("handler_PopHandler_F_hypotheses=" ^ Int.toString(length(hyp PopHandler_F)) ^ "\n");
val _ = row "handler_stack_rel_DROP_SOME" stack_rel_DROP_SOME;
val _ = print("handler_stack_rel_DROP_SOME_hypotheses=" ^ Int.toString(length(hyp stack_rel_DROP_SOME)) ^ "\n");
val _ = row "handler_stack_rel_cons_LEN_SOME" stack_rel_cons_LEN_SOME;
val _ = print("handler_stack_rel_cons_LEN_SOME_hypotheses=" ^ Int.toString(length(hyp stack_rel_cons_LEN_SOME)) ^ "\n");
val _ = row "handler_evaluate_PushHandler" evaluate_PushHandler;
val _ = print("handler_evaluate_PushHandler_hypotheses=" ^ Int.toString(length(hyp evaluate_PushHandler)) ^ "\n");
val _ = row "handler_evaluate_PushHandler_clock" evaluate_PushHandler_clock;
val _ = print("handler_evaluate_PushHandler_clock_hypotheses=" ^ Int.toString(length(hyp evaluate_PushHandler_clock)) ^ "\n");
val _ = row "handler_full_width64" (INST_TYPE [alpha |-> ``:64``] evaluate_PushHandler);
val _ = row "handler_full_width80" (INST_TYPE [alpha |-> ``:80``] evaluate_PushHandler);
