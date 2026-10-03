load "preamble"; load "word_to_stackProofTheory"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordPropsTheory wordSemTheory stackSemTheory listTheory rich_listTheory optionTheory miscTheory sortingTheory sptreeTheory arithmeticTheory alistTheory mllistTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordSemTheory
 stackSemTheory arithmeticTheory listTheory rich_listTheory optionTheory miscTheory;
val theorem = fn name => DB.fetch "word_to_stackProof" name;

val LASTN_MORE = prove(``
  ∀ls n.
  ¬(n < LENGTH ls) ⇒ LASTN n ls = ls``,
  fs[LASTN_LENGTH_LESS_EQ]);
val LASTN_LENGTH_BOUNDS = prove(``
  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls``,
  fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]);
val LASTN_CONS_ID = prove(``
  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)``,
  rw[]>>EVAL_TAC>>fs[]);
val LASTN_DROP2 = prove(``
  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l``,
  Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]>>
  Cases_on`n > LENGTH l`>>fs[ADD1]>>
  `LENGTH l - n = 0` by fs[]>>
  simp[DROP_def]);
val abs_stack_IMP_LENGTH = prove(``
  ∀bs wstack sstack lens stack.
    abs_stack bs wstack sstack lens = SOME stack ⇒ LENGTH stack = LENGTH wstack ∧ LENGTH lens = LENGTH wstack``,
  recInduct (theorem "abs_stack_ind")
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []);
val abs_stack_to_stack_LENGTH = prove(``
  ∀bs wstack sstack lens stack.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val stack = LENGTH sstack``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
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

(* Local theorem is not persisted; quote its full literal original statement. *)
val prefixStatement = ``  ∀bs wstack sstack lens stack h wrest k len.
  h ≤ LENGTH wstack ∧
  LASTN h wstack = wrest ∧
  abs_stack bs wstack sstack lens = SOME stack ∧
  stack_rel_aux k len wstack stack ⇒
  let rest = LASTN h stack in
  let lrest = LASTN h lens in
  let srest = LASTN (handler_val rest) sstack in
  abs_stack bs wrest srest lrest = SOME rest ∧
  stack_rel_aux k len wrest rest``;
val abs_stack_prefix_drop = GEN_ALL(prove(prefixStatement,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  rpt strip_tac>>fs[LET_THM,abs_stack_def]
  >-
    (fs[LASTN_def,handler_val_def]>>
    rveq>>
    fs[abs_stack_def,handler_val_def])
  >-
    (qpat_x_assum`A=SOME stack'`mp_tac>>
    Cases_on`w`>>fs[full_read_bitmap_def]>>
    ntac 4 TOP_CASE_TAC>>fs[]>>
    strip_tac>>rveq>>
    imp_res_tac abs_stack_IMP_LENGTH>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]
    >-
      (fs[LASTN_CONS,stack_rel_aux_def]>>
      first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
      res_tac>>
      fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_x_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>>AP_TERM_TAC>>
      qpat_abbrev_tac`lengt = handler_val A`>>
      Q.ISPECL_THEN [`lengt`,`DROP(LENGTH x)stack`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      simp[LASTN_DROP2,DROP_DROP]>>
      AP_THM_TAC>>
      AP_TERM_TAC>>DECIDE_TAC)
    >>
      qpat_abbrev_tac`frame = (a,x,TAKE A B)`>>
      `h = LENGTH (frame::x')` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      `LASTN (handler_val (frame::x')) (Word c::stack) = Word c::stack` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`frame`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      fs[Abbr`frame`,abs_stack_def,LET_THM,full_read_bitmap_def])
  >>
    qpat_x_assum`A=SOME stack'` mp_tac>>
    ntac 7 TOP_CASE_TAC>>
    PairCases_on`v0`>>
    fs[stack_rel_aux_def]>>
    strip_tac>>rveq>>
    imp_res_tac abs_stack_IMP_LENGTH>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]
    >-
      (fs[LASTN_CONS,stack_rel_aux_def]>>
      res_tac>>
      fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_x_assum`A=SOME(LASTN h x')` sym_sub_tac>>
      AP_THM_TAC>> AP_TERM_TAC>>
      qpat_abbrev_tac`lengt = handler_val A`>>
      Q.ISPECL_THEN [`lengt`,`DROP(LENGTH x)t`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      simp[LASTN_DROP2,DROP_DROP]>>
      AP_THM_TAC>>
      AP_TERM_TAC>>DECIDE_TAC)
    >>
      qpat_abbrev_tac`frame = (a,x,TAKE A B)`>>
      `h = LENGTH (frame::x')` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      qpat_abbrev_tac`ls=Word 1w::A`>>
      `LASTN (handler_val (frame::x')) ls = ls` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`ls`,Abbr`frame`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      fs[Abbr`frame`,Abbr`ls`,abs_stack_def,LET_THM,full_read_bitmap_def]));

load "preamble"; load "word_to_stackProofTheory"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordPropsTheory
 wordSemTheory listTheory rich_listTheory sortingTheory sptreeTheory mllistTheory;
val SORTS_SORT_key_val_compare = prove(``SORTS sort key_val_compare``,
  match_mp_tac sort_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare));
val list_rearrange_I = prove(``
  (list_rearrange I = I)``,
  fs [list_rearrange_def,FUN_EQ_THM]
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF,GENLIST_ID]);
val envStatement = ``
  !env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l``;
val env_to_list_K_I_IMP = GEN_ALL(prove(envStatement,
  fs [env_to_list_def,LET_DEF,FUN_EQ_THM,list_rearrange_I] \\ rw []
  \\ pop_assum kall_tac
  \\ qspec_then `toAList env` mp_tac (SORTS_SORT_key_val_compare
        |> REWRITE_RULE [SORTS_DEF])
  \\ Q.SPEC_TAC (`sort key_val_compare (toAList env)`,`l`) \\ rw []
  \\ `PERM (MAP FST (toAList env)) (MAP FST l)` by (match_mp_tac PERM_MAP \\ fs [])
  \\ `ALL_DISTINCT (MAP FST l)` by metis_tac [ALL_DISTINCT_MAP_FST_toAList,
         sortingTheory.ALL_DISTINCT_PERM]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ Induct_on `l` \\ fs []
  \\ Cases_on `l` \\ fs [SORTED_DEF] \\ rw []
  \\ res_tac \\ fs [key_val_compare_def,LET_DEF]
  \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs []));
load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory sortingTheory alistTheory sptreeTheory listTheory rich_listTheory arithmeticTheory;
val ALOOKUP_IFF_MEM = prove(``  ALL_DISTINCT (MAP FST l) ==>
    (ALOOKUP l q = SOME r <=> MEM (q,r) l)``,   Induct_on `l` \\ fs [FORALL_PROD,MEM_MAP] \\ rw [] \\ metis_tac []);
val SORTED_CONS_IMP = prove(``  SORTED (\x y. FST x > (FST y):num) (h::t) ==>
    ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
    !x. MEM x t ==> FST h > FST x``,   Induct_on `t` \\ fs [SORTED_DEF] \\ rw []
  \\ `SORTED (\x y. FST x > FST y) (h::t)` by
    (Cases_on `t` \\ fs [SORTED_DEF] \\ decide_tac)
  \\ fs [] \\ Cases_on `h` \\ Cases_on `h'` \\ fs []);
val SORTED_IMP_ALL_DISTINCT_LEMMA = prove(``  !l. SORTED (\x y. FST x > (FST y):num) l ==> ALL_DISTINCT (MAP FST l)``,   Induct \\ fs [] \\ rw [MEM_MAP]
  \\ metis_tac [DECIDE ``m>n ==> m<>n:num``,SORTED_CONS_IMP]);
val MEM_toAList_fromAList = prove(``  SORTED (\x y. FST x > (FST y):num) l ==>
    MEM a (toAList (fromAList l)) = MEM a l``,   Cases_on `a` \\ fs [MEM_toAList,lookup_fromAList] \\ rw []
  \\ imp_res_tac SORTED_IMP_ALL_DISTINCT_LEMMA \\ fs [ALOOKUP_IFF_MEM]);
val SORTED_FST_PERM_IMP_ALIST_EQ = prove(``  SORTED (\x y. FST x > FST y) l /\
  SORTED (\x y. FST x > FST y) q /\
  PERM (toAList (fromAList l)) q ==>
  q = l``,   rw [] \\ old_drule MEM_PERM \\ fs [MEM_toAList_fromAList]
  \\ pop_assum kall_tac \\ rpt (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Induct_on `q` \\ fs [MEM]
  THEN1 (Cases \\ fs[] \\ metis_tac [])
  \\ Cases_on `l` THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rw []
  \\ imp_res_tac SORTED_CONS_IMP
  \\ `!m n:num. m > n /\ n > m ==> F` by decide_tac
  \\ metis_tac []);
val ALL_DISTINCT_MEM_toAList_fromAList = prove(``  ALL_DISTINCT (MAP FST ls) ⇒
  (MEM x (toAList (fromAList ls)) ⇔
  MEM x ls)``,   Cases_on`x`>>fs[MEM_toAList,lookup_fromAList]>>
  rw[]>>
  metis_tac[ALOOKUP_MEM,ALOOKUP_ALL_DISTINCT_MEM]);
val LASTN_LENGTH_ID2 = prove(``
  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack``,
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID]);
val LASTN_LESS = prove(``
  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs``,
  Induct>>rw[]>>
  Cases_on`n+1 ≤ LENGTH ls`>>fs[]
  >-
    (fs[LASTN_CONS]>>
    res_tac>>fs[]>>
    `n ≤ LENGTH ls` by (fs[]>>decide_tac)>>
    fs[LASTN_CONS])
  >>
  `n = LENGTH ls` by DECIDE_TAC>>
  `n+1 = LENGTH (h::ls)` by (fs[]>>DECIDE_TAC)>>
  imp_res_tac LASTN_LENGTH_ID2>>
  fs[LASTN_CONS]);
(* Rebind after constituent probe opens: the original local theorem lookup
   is resolved against the already-built word_to_stackProof theory. *)
val theorem = fn name => DB.fetch "word_to_stackProof" name;
val abs_stack_len = prove(``
  ∀bs wstack sstack lens stack handler.
  abs_stack bs wstack sstack lens = SOME stack ⇒
  handler_val (LASTN handler stack) ≤ LENGTH sstack``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
  fs[abs_stack_def,LET_THM]
  >-
    (rveq>>fs[LASTN_def,handler_val_def])
  >>
    (pop_assum mp_tac>>rpt TOP_CASE_TAC>>fs[]>>
    rw[]>>
    Cases_on`handler ≤ LENGTH x'`
    >-
      (fs[LASTN_CONS]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      DECIDE_TAC)
    >>
      fs[]>>qpat_abbrev_tac`frame = (a,b,c)`>>
      `¬(handler < LENGTH (frame::x'))` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE,Abbr`frame`,handler_val_def]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      `¬(handler < LENGTH x')` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE]));
val handlerStatement = ``
  n ≤ LENGTH sstack /\
  handler+1 ≤ LENGTH wstack /\ SORTED (\x y. FST x > FST y) l /\
  LASTN (handler + 1) wstack = StackFrame m l0 l (SOME (h1,l3,l4))::rest /\
  abs_stack bs wstack (DROP n sstack) lens = SOME stack /\
  stack_rel_aux k (LENGTH sstack) wstack stack ==>
  ?ex payload.
    LASTN (handler+1) stack = (SOME ex,payload) :: LASTN handler stack /\
    3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler+1) stack) /\
    EL (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 1)
          sstack = Loc l3 l4 /\
    ((h1 < LENGTH rest /\
    is_handler_frame (EL (LENGTH rest - (h1+1)) rest) ⇒
    EL (LENGTH sstack − handler_val (LASTN (handler+1) stack) + 2) sstack =
        Word (n2w
          (LENGTH sstack - handler_val (LASTN (h1+1) (LASTN (handler+1) stack)))))) /\
    stack_rel_aux k (LENGTH sstack)
      (StackFrame m l0
        (FST (env_to_list (fromAList l) (K I))) NONE::rest)
          ((NONE,payload) :: LASTN handler stack) /\
    abs_stack bs
      (StackFrame m l0
        (FST (env_to_list (fromAList l) (K I))) NONE::rest)
      (DROP (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 3)
         sstack) (LASTN (handler+1) lens) = SOME ((NONE,payload) :: LASTN handler stack)``;
val replay = GEN_ALL(prove(handlerStatement,
  rw[]>>
  imp_res_tac abs_stack_prefix_drop>>
  fs[LET_THM]>>
  Cases_on`LASTN (handler+1) stack`>>fs[stack_rel_aux_def]>>
  PairCases_on`h`>>Cases_on`h0`>>fs[stack_rel_aux_def]>>
  PairCases_on`x`>>fs[stack_rel_aux_def]>>
  DEP_REWRITE_TAC[inter_union_left]>>
  simp[wf_fromAList]>>
  `FST (env_to_list (fromAList l) (K I)) = l` by
   (Cases_on `env_to_list (fromAList l) (K I)` \\ fs []
    \\ imp_res_tac env_to_list_K_I_IMP \\ rw []
    \\ metis_tac [SORTED_FST_PERM_IMP_ALIST_EQ]) >>
  imp_res_tac abs_stack_IMP_LENGTH>>fs[]>>
  CONJ_TAC>- fs[LASTN_LESS]>>
  imp_res_tac abs_stack_len>>
  fs[handler_val_def]>>
  CONJ_ASM1_TAC>- (
    qhdtm_x_assum `abs_stack` mp_tac>>
    Cases_on`LASTN (handler+1) lens`>>fs[]>>
    (*The DROP must have length ≥ 3*)
    Cases_on`DROP n sstack`>>simp[abs_stack_def,LASTN_def]>>
    Cases_on`t''`>>simp[abs_stack_def]>>
    Cases_on`t'''`>>simp[abs_stack_def]>>
    `3 ≤ LENGTH (DROP n sstack)` by
      (pop_assum SUBST_ALL_TAC>>
      simp[])>>
    Q.ISPECL_THEN [`n`,`sstack`] assume_tac LENGTH_DROP >>
    `LENGTH (DROP n sstack) ≤ LENGTH sstack` by DECIDE_TAC>>
    simp[])>>
  qhdtm_x_assum `abs_stack` mp_tac>>
  qpat_abbrev_tac`ls = LASTN A B`>>
  qpat_abbrev_tac`lens' = LASTN A lens`>>
  strip_tac>>
  simp[LASTN_CONS]>>
  qpat_abbrev_tac`w = Word A`>>
  qpat_abbrev_tac`preconds = (h1 < LENGTH rest ∧ B)`>>
  `EL 1 ls = Loc l3 l4 ∧ (preconds ⇒ EL 2 ls = w)` by
    (qhdtm_x_assum`abs_stack` mp_tac>>
    Cases_on`lens'`>>fs[]>>
    Cases_on`ls`>-simp[abs_stack_def]>>
    Cases_on`h'`>>simp[abs_stack_def,LET_THM]>>
    ntac 7 TOP_CASE_TAC>>fs[])>>
  fs[Abbr`ls`,LASTN_DROP2]>>
  qpat_abbrev_tac`offset = (LENGTH _ + (_ + 4))`>>
  (*Using DROP_DROP and more assumptions on the lengths*)
  `n + offset ≤ LENGTH sstack` by
    (first_x_assum(qspec_then`handler+1` mp_tac)>>
    simp[handler_val_def,Abbr`offset`])>>
  `DROP (LENGTH sstack - n - offset) (DROP n sstack) =
   DROP (LENGTH sstack - offset) sstack` by
     simp[DROP_DROP]>>
  `EL 1 (DROP (LENGTH sstack - offset) sstack) = Loc l3 l4 ∧
   (preconds ⇒ EL 2 (DROP (LENGTH sstack - offset) sstack) = w)` by fs[]>>
  conj_asm1_tac >- (
    first_x_assum sym_sub_tac >>
    dep_rewrite.DEP_REWRITE_TAC[EL_DROP] >>
    simp[Abbr`offset`] ) >>
  conj_asm1_tac >- (
    rw[] >> fs[] >> rw[] >>
    dep_rewrite.DEP_REWRITE_TAC[EL_DROP] >>
    simp[Abbr`offset`] ) >>
  qpat_x_assum`DROP A stack = C` mp_tac>>
  qpat_x_assum`LENGTH stack =A` sym_sub_tac>>
  simp[GSYM LASTN_DROP2]>>
  strip_tac >> imp_res_tac LASTN_LESS>>
  simp[]>>
  qpat_x_assum`abs_stack A B C D = E` mp_tac>>
  simp[]>>
  qpat_abbrev_tac`ls = DROP A B`>>
  qpat_abbrev_tac`ls' = DROP A B`>>
  `ls' = DROP 3 ls` by
    (unabbrev_all_tac>>
    simp[DROP_DROP])>>
  Cases_on`lens'`>>
  Cases_on`ls`>>simp[abs_stack_def]>>
  Cases_on`t''`>>simp[]>>
  Cases_on`t'''`>>simp[]>>
  ntac 5 TOP_CASE_TAC>>
  rw[]>>
  fs[abs_stack_def,LET_THM]>>
  first_x_assum irule>>
  simp[]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open handler theorem";
val _ = (print "stack_rel_raise_statement="; print_term(concl replay); print "\n");
val _ = print("stack_rel_raise_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("stack_rel_raise_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
