load "bvl_to_bviProofTheory";
load "bviPropsTheory";
load "preamble";
open preamble bvl_to_bviProofTheory bvlSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "adjust_bv_def=" adjust_bv_def;
val _ = show "adjust_bv_Unit=" adjust_bv_Unit;
val _ = show "adjust_bv_Boolv=" adjust_bv_Boolv;
val _ = show "adjust_nested=" (EVAL ``adjust_bv (\n. n + 5)
  (Block 7 [Number ~3; RefPtr T 2; CodePtr 3; Block 8 [RefPtr F 9]])``);
val _ = show "aux_code_installed=" aux_code_installed_def;
val aux_code_installed_APPEND_replay = prove (``!xs ys code.
  aux_code_installed (xs ++ ys) code ==>
  aux_code_installed xs code /\ aux_code_installed ys code``,
  Induct \\ fs[APPEND,aux_code_installed_def,FORALL_PROD] \\ METIS_TAC []);
val _ = show "aux_code_installed_APPEND_replay=" aux_code_installed_APPEND_replay;
val _ = show "aux_code_installed_subspt=" aux_code_installed_subspt;
val _ = show "isVar_def=" bvlPropsTheory.isVar_def;
val _ = show "bVarBound_def=" bvlPropsTheory.bVarBound_def;
val bEval_bVarBound_replay = prove (``!xs vs s env.
  bvlProps$bVarBound (LENGTH vs) xs ==>
  (bvlSem$evaluate (xs,vs ++ env,s) = bvlSem$evaluate (xs,vs,s))``,
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def,bvlPropsTheory.bVarBound_def]
  \\ TRY (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[ADD1] \\ NO_TAC)
  THEN1 (`n < LENGTH env + LENGTH env'` by DECIDE_TAC
         \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM MATCH_MP_TAC
         \\ IMP_RES_TAC bvlPropsTheory.evaluate_IMP_LENGTH
         \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  THEN1 (gvs [] \\ rpt (PURE_CASE_TAC \\ gvs [])
         \\ gvs [oneline bvlSemTheory.dest_thunk_def, AllCaseEqs(), EL_APPEND]));
val _ = show "bEval_bVarBound_replay=" bEval_bVarBound_replay;
val _ = show "EVERY_isVar_evaluate_Rval_MEM=" EVERY_isVar_evaluate_Rval_MEM;
val _ = show "evaluate_Var_list=" bvlPropsTheory.evaluate_Var_list;
val _ = show "let_ok_def=" bvl_handleProofTheory.let_ok_def;
val _ = show "handle_ok_def=" bvl_handleProofTheory.handle_ok_def;
val _ = show "handle_ok_CONS=" bvl_handleProofTheory.handle_ok_CONS;
val _ = show "handle_ok_EVERY=" bvl_handleProofTheory.handle_ok_EVERY;
val _ = show "handle_good=" (prove (``bvl_handleProof$handle_ok
  [bvl$Let [] (bvl$Let [bvl$Var 0] (bvl$Var 0))]``,
  EVAL_TAC \\ simp[bvl_handleProofTheory.handle_ok_def]));
val _ = show "handle_bad=" (EVAL ``bvl_handleProof$handle_ok
  [bvl$Let [] (bvl$Let [bvl$Var 0] (bvl$Var 1))]``);
val _ = show "names_ok_def=" names_ok_def;
val _ = show "state_rel_def=" state_rel_def;
val _ = show "state_rel_FLOOKUP_byteArray=" state_rel_FLOOKUP_byteArray;
val _ = show "state_rel_FLOOKUP_valueArray=" state_rel_FLOOKUP_valueArray;
val _ = show "state_rel_FLOOKUP_MutBlock=" state_rel_FLOOKUP_MutBlock;
val _ = show "state_rel_FLOOKUP_Thunk=" state_rel_FLOOKUP_Thunk;
val _ = show "bv_ok_def=" bv_ok_def;
val _ = show "bv_ok_Unit=" bv_ok_Unit;
val _ = show "bv_ok_Boolv=" bv_ok_Boolv;
val _ = show "state_ok_def=" state_ok_def;
val evaluate_ok_lemma_replay = prove(
  ``(state_ok (bvlSem$dec_clock n s) = state_ok s) /\
    ((bvlSem$dec_clock n s).refs = s.refs)``,
  full_simp_tac (srw_ss()) [state_ok_def, bvlSemTheory.dec_clock_def]);
val _ = show "evaluate_ok_lemma_replay=" evaluate_ok_lemma_replay;
val v_to_list_ok_replay = prove(
  ``∀v x. v_to_list v = SOME x ∧ bv_ok refs v ⇒ EVERY (bv_ok refs) x``,
  ho_match_mp_tac v_to_list_ind >>
  simp [v_to_list_def, bv_ok_def] >> srw_tac [] [] >>
  every_case_tac >> full_simp_tac (srw_ss()) [] >> srw_tac [] []);
val _ = show "v_to_list_ok_replay=" v_to_list_ok_replay;
(* The local source theorem follows from its exported strengthening. *)
val do_app_ok_lemma_derived = prove(
  ``state_ok r ∧ EVERY (bv_ok r.refs) a ∧
    (bvlSem$do_app op a r = Rval (q,t)) ⇒ state_ok t ∧ bv_ok t.refs q``,
  metis_tac [do_app_ok]);
val _ = show "do_app_ok_lemma_derived=" do_app_ok_lemma_derived;
val dec_clock_inc_clock_replay = prove(
  ``c ≠ 0 ⇒ bviSem$dec_clock 1 (bviProps$inc_clock c t) =
    bviProps$inc_clock (c - 1) (t:('c,'ffi) bviSem$state)``,
  EVAL_TAC THEN fs [bviSemTheory.state_component_equality]);
val _ = show "dec_clock_inc_clock_replay=" dec_clock_inc_clock_replay;
val _ = show "evaluate_ListLength_code_typed=" bvl_to_bviProofTheory.evaluate_ListLength_code;
val _ = show "evaluate_FromListByte_code_typed=" bvl_to_bviProofTheory.evaluate_FromListByte_code;
val _ = show "evaluate_ToListByte_code_typed=" bvl_to_bviProofTheory.evaluate_ToListByte_code;
val _ = show "evaluate_SumListLength_code_typed=" bvl_to_bviProofTheory.evaluate_SumListLength_code;
val _ = show "evaluate_ConcatByte_code_typed=" bvl_to_bviProofTheory.evaluate_ConcatByte_code;
val _ = show "bvi_inc_clock_def=" bviPropsTheory.inc_clock_def;
val _ = show "bvi_inc_clock_ZERO=" bviPropsTheory.inc_clock_ZERO;
val _ = show "bvi_dec_clock_inv_clock1=" bviPropsTheory.dec_clock_inv_clock1;
val bv_ok_SUBSET_IMP_replay = prove (``!refs x refs2.
  bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x``,
  HO_MATCH_MP_TAC bv_ok_ind \\ full_simp_tac (srw_ss()) [bv_ok_def]
  \\ full_simp_tac (srw_ss()) [SUBSET_DEF,EVERY_MEM]);
val _ = show "bv_ok_SUBSET_IMP_replay=" bv_ok_SUBSET_IMP_replay;
val _ = show "list_to_v_ok=" list_to_v_ok;
val _ = show "list_to_v_ok_APPEND=" list_to_v_ok_APPEND;
val _ = show "do_app_refs_SUBSET=" bvlPropsTheory.do_app_refs_SUBSET;
val _ = show "evaluate_refs_SUBSET=" bvlPropsTheory.evaluate_refs_SUBSET;
val evaluate_IMP_bv_ok_replay = prove (``!xs env s res t a1 vs.
  bvlSem$evaluate (xs,env,s) = (res,t) ==>
  (bv_ok s.refs a1 ==> bv_ok t.refs a1) /\
  (EVERY (bv_ok s.refs) vs ==> EVERY (bv_ok t.refs) vs)``,
  REPEAT STRIP_TAC \\ full_simp_tac (srw_ss()) [EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC bvlPropsTheory.evaluate_refs_SUBSET \\ IMP_RES_TAC bv_ok_SUBSET_IMP_replay);
val _ = show "evaluate_IMP_bv_ok_replay=" evaluate_IMP_bv_ok_replay;
val _ = show "find_code_bv_ok=" find_code_bv_ok;
val _ = show "do_build_ok=" do_build_ok;
val _ = show "do_app_ok=" do_app_ok;
val _ = show "evaluate_ok=" evaluate_ok;
val _ = show "compile_exps_correct=" compile_exps_correct;
val bv_ok_IMP_adjust_bv_eq_replay = prove (``!b2 a1 b3.
  bv_ok refs a1 /\ (!a. a IN FDOM refs ==> b2 a = b3 a) ==>
  adjust_bv b2 a1 = adjust_bv b3 a1``,
  HO_MATCH_MP_TAC adjust_bv_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bv_ok_def]
  \\ full_simp_tac(srw_ss())[MAP_EQ_f,EVERY_MEM]);
val _ = show "bv_ok_IMP_adjust_bv_eq_replay=" bv_ok_IMP_adjust_bv_eq_replay;

open bvl_to_bviTheory bvlPropsTheory;
val _ = show "destVar_def_typed=" bvlPropsTheory.destVar_def;
val _ = show "destVar_tick_unconstrained=" (EVAL ``destVar (bvl$Tick (bvl$Var 0))``);
val _ = show "compile_exps_sing_typed=" bvl_to_bviTheory.compile_exps_sing;
val compile_exps_Var_list_replay = prove (``!l n. EVERY isVar l ==> (∃aux. compile_exps n l = (MAP (Var o destVar) l ,aux,n) ∧ append aux = [])``,
  Induct \\ fs[compile_exps_def] \\ Cases \\ rw[isVar_def] \\ fs[]
  \\ Cases_on`l` \\ fs[compile_exps_def,destVar_def]
  \\ qmatch_goalsub_rename_tac`compile_exps a`
  \\ first_x_assum(qspec_then`a`strip_assume_tac) \\ fs[]);
val _ = show "compile_exps_Var_list_replay=" compile_exps_Var_list_replay;

val compile_int_thm_replay = prove (``∀i env s. bviSem$evaluate ([compile_int i],env,s) = (Rval [Number i],s)``,
  Cases \\ rw [compile_int_def]
  \\ rw [] \\ EVAL_TAC \\ fs [bviSemTheory.state_component_equality]);
val _ = show "compile_int_thm_replay=" compile_int_thm_replay;

open bviSemTheory bviPropsTheory;
val _ = Parse.hide "str";
val compile_int_thm = compile_int_thm_replay;
val compile_string_thm = Q.prove(
  `∀str s ls vs.
   FLOOKUP s.refs ptr = SOME (ByteArray T ls) ∧ LENGTH vs + LENGTH str = LENGTH ls ⇒
   evaluate (MAPi (λn c. Op (MemOp UpdateByte) [Op (IntOp (Const (&ORD c))) []; compile_int (&(n + LENGTH vs)); Var 0]) str,
    RefPtr b ptr::env, s) = (Rval (REPLICATE (LENGTH str) Unit),
      s with refs := s.refs |+ (ptr, ByteArray T (TAKE (LENGTH vs) ls ++ (MAP (n2w o ORD) str))))`,
  Induct \\ rw[evaluate_def,REPLICATE]
  >- (rw[state_component_equality]
      \\ match_mp_tac (GSYM FUPDATE_ELIM) \\ fs[FLOOKUP_DEF])
  \\ rw[Once evaluate_CONS]
  \\ reverse(rw[evaluate_def,do_app_def,do_app_aux_def,backend_commonTheory.small_enough_int_def])
  >- ( qspec_then`h`strip_assume_tac ORD_BOUND \\ fs[] )
  \\ reverse(rw[bvlSemTheory.do_app_def,compile_int_thm,EL_LENGTH_APPEND])
  >- (
    fs[] \\ first_x_assum(qspec_then`n2w (ORD h)`mp_tac)
    \\ simp[w2n_n2w,ORD_BOUND] )
  \\ simp[o_DEF,ADD1]
  \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ qpat_abbrev_tac`ss = s with refs := _`
  \\ first_x_assum(qspec_then`ss`mp_tac)
  \\ simp[Abbr`ss`,FLOOKUP_UPDATE]
  \\ disch_then(qspec_then`ARB::vs`mp_tac)
  \\ rw[ADD1,state_component_equality]
  \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[]
  \\ rw[LIST_EQ_REWRITE]
  \\ Cases_on`x = LENGTH vs` \\ simp[EL_APPEND1,EL_LUPDATE,EL_APPEND2,EL_TAKE]
  \\ Cases_on`x < LENGTH vs` \\ simp[EL_APPEND1,EL_TAKE,EL_LUPDATE]
  \\ simp[EL_TAKE,EL_APPEND2,o_DEF])
  |> Q.SPECL[`str`,`s`,`ls`,`[]`]
  |> SIMP_RULE(srw_ss())[]
  |> Q.GENL[`str`,`ls`,`ptr`,`s`,`env`]
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];

val _ = show "compile_string_thm_typed=" compile_string_thm;

val _ = show "HD_APPEND3_typed=" bvl_to_bviProofTheory.HD_APPEND3;

val compile_exps_LENGTH_lemma_replay = prove (``!n (xs :bvl$exp list). (LENGTH (FST (compile_exps n xs)) = LENGTH xs)``,
  HO_MATCH_MP_TAC compile_exps_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_exps_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);
val _ = show "compile_exps_LENGTH_lemma_replay=" compile_exps_LENGTH_lemma_replay;

val _ = show "compile_exps_LENGTH_typed=" bvl_to_bviTheory.compile_exps_LENGTH;
val _ = show "compile_exps_SING_typed=" bvl_to_bviTheory.compile_exps_SING;

val evaluate_MAP_Var2 = Q.prove(
  `!args.
      bVarBound (LENGTH vs) args /\ EVERY isVar args ==>
      ?ts.
        bviSem$evaluate (MAP (Var o destVar) args,vs ++ env,s) = (Rval ts,s) /\
        evaluate (MAP (Var o destVar) args,vs,s) = (Rval ts,s)`,
  Induct \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def] \\ Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ Cases_on `args` \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def,destVar_def,bVarBound_def]
  \\ REPEAT STRIP_TAC
  \\ `n < LENGTH vs + LENGTH env` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]) |> SPEC_ALL
  |> INST_TYPE[beta|->``:'ffi``,alpha|->``:'c``];

val _ = show "evaluate_MAP_Var2_typed=" evaluate_MAP_Var2;

open bvl_to_bviProofTheory bvl_to_bviTheory bvlPropsTheory bviSemTheory bviPropsTheory;
val handle_ok_def = bvl_handleProofTheory.handle_ok_def;
val iEval_def = bviSemTheory.evaluate_def;
val iEval_append = bviPropsTheory.evaluate_APPEND;
val iEvalOp_def = bviSemTheory.do_app_def;
val compile_exps_Var_list = compile_exps_Var_list_replay;
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [], [`t`]];

val iEval_bVarBound_replay = prove (``  ∀(n:num) xs n vs (s:('c,'ffi) bviSem$state) env.
    bVarBound (LENGTH vs) xs /\ handle_ok xs ==>
    (evaluate (FST (compile_exps n xs),vs ++ env,s) =
     evaluate (FST (compile_exps n xs),vs,s))``,
  recInduct bVarBound_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[iEval_def,bVarBound_def,compile_exps_def]
  \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bEvery_def,handle_ok_def] \\ SRW_TAC [] []
  THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
         \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[])
  THEN1 (full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (fs [])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ full_simp_tac(srw_ss())[iEval_def])
  THEN1
   (fs [evaluate_def] \\ rveq \\ fs []
    \\ Cases_on `x2` \\ fs [destLet_def,NULL_EQ]
    \\ fs [destLet_def,markerTheory.Abbrev_def,
           bvl_handleProofTheory.let_ok_def] \\ rveq \\ fs[]
    \\ IMP_RES_TAC compile_exps_Var_list
    \\ first_x_assum(qspec_then`n`strip_assume_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bVarBound_def]
    \\ (evaluate_MAP_Var2 |> MP_TAC) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[iEval_def]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`]) \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
         \\ REPEAT STRIP_TAC
         \\ Cases_on `evaluate (c1,vs,s)` \\ full_simp_tac(srw_ss())[]
         \\ Cases_on `q` \\ full_simp_tac(srw_ss())[NULL_EQ,LENGTH_NIL]
         \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a ++ vs`]) \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC bviPropsTheory.evaluate_IMP_LENGTH \\ IMP_RES_TAC compile_exps_LENGTH
         \\ REPEAT STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
         \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  >~ [‘Raise’] >-
   (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def])
  >~ [‘Tick’] >-
   (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def])
  >~ [‘compile_op’] >-
   (Cases_on `op = Install` THEN1
     (fs [compile_op_def] \\ IF_CASES_TAC \\ fs []
      THEN1
       (once_rewrite_tac [evaluate_def]
        \\ `evaluate ([Let c1 (Op (IntOp (Const 0)) []); Op (IntOp (Const 0)) []],vs ⧺ env,s) =
           evaluate ([Let c1 (Op (IntOp (Const 0)) []); Op (IntOp (Const 0)) []],vs,s)` by
          (fs [evaluate_def]
           \\ first_x_assum (qspecl_then [`n`,`vs`] mp_tac) \\ fs [])
        \\ fs [] \\ CASE_TAC \\ simp [case_eq_thms]
        \\ Cases_on `q` \\ fs []
        \\ once_rewrite_tac [evaluate_def]
        \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ simp [evaluate_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ Cases_on `a` \\ fs []
        \\ Cases_on `t` \\ fs [])
      THEN1
       (once_rewrite_tac [evaluate_def]
        \\ imp_res_tac compile_exps_LENGTH \\ rfs []
        \\ FIRST_X_ASSUM (qspecl_then [`n`,`vs`] mp_tac) \\ fs [] \\ rw []
        \\ TOP_CASE_TAC \\ TOP_CASE_TAC
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ Cases_on `a` \\ fs [] \\ rveq \\ fs []
        \\ Cases_on `t` \\ fs [] \\ fs [evaluate_def]))
    \\ Cases_on `(?t. op = BlockOp (FromList t)) ∨
       op = MemOp FromListByte ∨ op = MemOp ToListByte ∨ op = MemOp ConcatByteVec` THEN1
     (fs [] \\ rw[] \\ fs [compile_op_def]
      \\ once_rewrite_tac [bviSemTheory.evaluate_def]
      \\ (IF_CASES_TAC THEN1
           (fs [bviSemTheory.evaluate_def,EVAL ``bviSem$do_app (IntOp (Const 0)) [] s``]))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`])
      \\ full_simp_tac(srw_ss())[]
      \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on `a` \\ fs [LENGTH_NIL]
      \\ fs [bviSemTheory.evaluate_def])
    \\ Cases_on`op = MemOp (CopyByte T)`
    >- (
      fs[compile_op_def]
      \\ first_x_assum old_drule
      \\ disch_then(qspecl_then[`n`,`s`,`env`]mp_tac) \\ simp[]
      \\ IF_CASES_TAC
      >- (
        rw[Once bviSemTheory.evaluate_def]
        \\ rw[evaluate_APPEND]
        \\ rw[Once bviSemTheory.evaluate_def,SimpRHS]
        \\ rw[evaluate_APPEND,REPLICATE_compute]
        \\ CASE_TAC \\  simp[]
        \\ Cases_on`q` \\ simp[]
        \\ rw[bviSemTheory.evaluate_def,REPLICATE_compute,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def,HD_APPEND3]
        \\ CASE_TAC \\ simp[]
        \\ imp_res_tac evaluate_IMP_LENGTH
        \\ rewrite_tac[GSYM APPEND_ASSOC,GSYM EL]
        \\ simp[EL_APPEND1]
        \\ CASE_TAC \\ fs[EL_APPEND1]) \\
      rw[Once bviSemTheory.evaluate_def]
      \\ rw[evaluate_APPEND]
      \\ rw[Once bviSemTheory.evaluate_def,SimpRHS]
      \\ rw[evaluate_APPEND,REPLICATE_compute]
      \\ CASE_TAC \\  simp[]
      \\ Cases_on`q` \\ simp[]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on`a` \\ fs[]
      \\ Cases_on`t` \\ fs[]
      \\ rename1`SUC (LENGTH t)`
      \\ Cases_on`t` \\ fs[]
      \\ rw[bviSemTheory.evaluate_def,iEvalOp_def,do_app_aux_def,backend_commonTheory.small_enough_int_def]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[]
      \\ CASE_TAC \\ simp[])
    \\ Cases_on ‘∃n. op = GlobOp (Global n)’ >-
     (gvs [compile_op_def,iEval_def,compile_int_thm]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
      \\ IF_CASES_TAC \\ fs []
      \\ fs [iEval_def]
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on ‘c1’ \\ fs []
      \\ Cases_on ‘a’ \\ gvs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ cases_on_op `op`
    \\ full_simp_tac(srw_ss())[compile_op_def,iEval_def,compile_int_thm]
    \\ simp[iEval_def]
    \\ simp[iEval_append,iEval_def,compile_int_thm]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[iEval_def,compile_int_thm])
  >>~ [‘dest_thunk’]
  >- gvs [AllCaseEqs()]
  >- (
    rpt (PURE_CASE_TAC \\ gvs [])
    \\ unabbrev_all_tac \\ gvs [EL_APPEND])
  \\ full_simp_tac(srw_ss())[iEval_def]
  \\ TRY (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`]) \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ Cases_on `x1` \\ fs [] \\ rveq
  \\ Cases_on `e` \\ fs [] \\ rveq
  \\ fs [destLet_def,markerTheory.Abbrev_def] \\ rveq
  \\ IMP_RES_TAC compile_exps_Var_list
  \\ first_x_assum(qspec_then`n`strip_assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bVarBound_def]
  \\ (evaluate_MAP_Var2 |> MP_TAC) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [APPEND |> SPEC_ALL |> CONJUNCT2 |> GSYM]
  \\ qpat_x_assum ‘∀vs' s env. bVarBound (LENGTH vs') [x2] ∧ _ ⇒ _’
       (fn th => gvs [th, ADD1]));

val _ = show "iEval_bVarBound_replay=" iEval_bVarBound_replay;

open bvlSemTheory;
val v_to_list_adjust_replay = prove (``∀x. v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f)) (v_to_list x)``,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,adjust_bv_def] >> srw_tac[][] >>
  Cases_on`v_to_list x`>>full_simp_tac(srw_ss())[]);
val _ = show "v_to_list_adjust_replay=" v_to_list_adjust_replay;

val do_eq_adjust_lemma_replay = prove (``  (!refs x1 x2 b.
              refs = r.refs /\
              do_eq refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
              bv_ok r.refs x1 /\ bv_ok r.refs x2 ==>
              do_eq t2.refs (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b) /\
   (!refs x1 x2 b.
              refs = r.refs /\
              do_eq_list refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
              EVERY (bv_ok r.refs) x1 /\ EVERY (bv_ok r.refs) x2 ==>
              do_eq_list t2.refs (MAP (adjust_bv b2) x1) (MAP (adjust_bv b2) x2) = Eq_val b)``,
  ho_match_mp_tac do_eq_ind \\ rw [] \\ fs [adjust_bv_def]
  THEN1 (
    fs[bv_ok_def]
    \\ Cases_on`FLOOKUP r.refs n2` >- fs[FLOOKUP_DEF]
    \\ Cases_on`FLOOKUP r.refs n1` >- fs[FLOOKUP_DEF] \\ fs[]
    \\ fs[state_rel_def]
    \\ last_assum(qspec_then`n2`mp_tac)
    \\ last_x_assum(qspec_then`n1`mp_tac)
    \\ simp[]
    \\ every_case_tac \\ fs[]
    \\ fs[INJ_DEF]
    \\ metis_tac[])
  \\ fs [isClos_def] \\ rfs []
  \\ fs [bv_ok_def] \\ rfs []
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ rw [] \\ every_case_tac \\ fs []);
val _ = show "do_eq_adjust_lemma_replay=" do_eq_adjust_lemma_replay;
val do_eq_adjust_lemma = do_eq_adjust_lemma_replay;
val do_eq_adjust_replay = prove (``  do_eq r.refs x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
   bv_ok r.refs x1 /\ bv_ok r.refs x2 ==>
   do_eq t2.refs (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b``,
  metis_tac [do_eq_adjust_lemma]);
val _ = show "do_eq_adjust_replay=" do_eq_adjust_replay;

val _ = show "list_to_v_adjust_typed=" bvl_to_bviProofTheory.list_to_v_adjust;
val _ = show "list_to_v_adjust_APPEND_typed=" bvl_to_bviProofTheory.list_to_v_adjust_APPEND;

(* This local HOL declaration is parsed with its original inferred types. *)
open bvl_to_bviProofTheory bvlSemTheory bviSemTheory;
val doAppAdjustTerm = ``  state_rel b2 s5 t2 /\
  (!i. op ≠ IntOp (Const i)) /\ (op ≠ MemOp Ref) /\
  (∀flag. op ≠ MemOp (RefByte flag)) ∧ (op ≠ MemOp RefArray) ∧
  (∀n. op ≠ GlobOp (Global n)) ∧ (∀n. op ≠ GlobOp (SetGlobal n)) ∧ (op ≠ GlobOp AllocGlobal) ∧
  op ≠ Install /\
  (∀t. op ≠ ThunkOp t) ∧
  (∀n. op ≠ BlockOp (FromList n)) ∧ (op ≠ MemOp FromListByte) ∧
  (op ≠ MemOp ToListByte) ∧ (∀c. op ≠ BlockOp (Build c)) ∧ op ≠ MemOp XorByte ∧
  (∀b. op ≠ MemOp (CopyByte b)) ∧ (op ≠ MemOp ConcatByteVec) ∧ (∀n. op ≠ Label n) ∧
  (do_app op (REVERSE a) s5 = Rval (q,r)) /\ EVERY (bv_ok s5.refs) (REVERSE a) ==>
  ?t3. (do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 =
        Rval (adjust_bv b2 q,t3)) /\
      state_rel b2 r t3``;
val _ = (print "do_app_adjust_term_typed="; print_term doAppAdjustTerm; print "\n");

(* Generated sizes include numeric and operation payloads; eval_ind_alt uses
   these bounds rather than the evaluator termination weight. *)
val _ = show "bvl_exp_size_generated_typed=" bvlTheory.exp_size_def;
val _ = show "eval_ind_alt_typed=" bvl_to_bviProofTheory.eval_ind_alt;
val _ = show "bvl_size_var=" (EVAL ``bvl$exp_size (bvl$Var 7)``);
val _ = show "bvl_size_force=" (EVAL ``bvl$exp_size (bvl$Force 3 5)``);
val _ = show "bvl_size_call=" (EVAL ``bvl$exp_size (bvl$Call 4 (SOME 8) [bvl$Var 2])``);
val _ = show "bvl_size_op=" (EVAL ``bvl$exp_size (bvl$Op (closLang$Label 9) [bvl$Var 3])``);
val _ = show "bvl_size_let=" (EVAL ``bvl$exp_size (bvl$Let [bvl$Var 4] (bvl$Tick (bvl$Var 2)))``);

(* Replay the complete local source theorem and its proof. *)
val bEvalOp_def = bvlSemTheory.do_app_def;
val iEvalOp_def = bviSemTheory.do_app_def;
val do_app_Ref_replay = prove (``
  do_app (MemOp Ref) vs s =
     Rval
      (RefPtr T (LEAST ptr. ptr ∉ FDOM s.refs),
       bvl_to_bvi
        (bvi_to_bvl s with
         refs :=
           s.refs |+ ((LEAST ptr. ptr ∉ FDOM s.refs),ValueArray vs)) s)``,
  fs [iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_THM]
  \\ every_case_tac \\ fs []);
val _ = show "do_app_Ref_replay=" do_app_Ref_replay;

(* Exported state-relation preservation theorems, with inferred carriers. *)
val _ = show "state_rel_add_bytearray_typed=" bvl_to_bviProofTheory.state_rel_add_bytearray;
val _ = show "state_rel_add_thunk_typed=" bvl_to_bviProofTheory.state_rel_add_thunk;
val _ = show "state_rel_update_thunk_typed=" bvl_to_bviProofTheory.state_rel_update_thunk;

(* Replay the local consequence with both original counter binders. *)
val iEval_bVarBound = iEval_bVarBound_replay;
val iEval_bVarBound_extra_replay = prove (``
    ∀n xs n vs s env d.
     bVarBound (LENGTH vs) xs ∧ handle_ok xs /\ d = FST (compile_exps n xs) ⇒
     evaluate (d,vs ⧺ env,s)  =
     evaluate (d,vs,s)``,
  simp [iEval_bVarBound]);
val _ = show "iEval_bVarBound_extra_replay=" iEval_bVarBound_extra_replay;

(* Replay the original local byte and word encoding injectivity proofs. *)
val MAP_Num_11_replay = prove (``
    !ns:word8 list ns'.
      MAP (λx. Number (&w2n x)) ns = MAP (λx. Number (&w2n x)) ns' <=> ns' = ns``,
  Induct \\ Cases_on `ns'` \\ fs [] \\ rw [] \\ eq_tac \\ rw []);
val _ = show "MAP_Num_11_replay=" MAP_Num_11_replay;
val MAP_Word_11_replay = prove (``
    !ns ns'. MAP Word64 ns = MAP Word64 ns' <=> ns' = ns``,
  Induct \\ Cases_on `ns'` \\ fs [] \\ rw [] \\ eq_tac \\ rw []);
val _ = show "MAP_Word_11_replay=" MAP_Word_11_replay;

val _ = show "IMP_v_to_bytes_typed=" bvl_to_bviProofTheory.IMP_v_to_bytes;
val _ = show "IMP_v_to_words_typed=" bvl_to_bviProofTheory.IMP_v_to_words;

val _ = show "aux_code_installed_sublist_typed=" bvl_to_bviProofTheory.aux_code_installed_sublist;
