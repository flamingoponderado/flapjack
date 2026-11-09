load "flat_to_closProofTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib listTheory pairTheory;
open flat_to_closProofTheory;
open rich_listTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "list_rel_el_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl flat_to_closProofTheory.LIST_REL_EL); print "\n");
(* Replay the local indexed-list relation theorem using its original proof. *)
val list_rel_map_genlist_replay = Q.prove (
  `!funs f1 f2 R.
    (!n. n < LENGTH funs ==> R (f1 (EL n funs)) (f2 n)) ==>
    LIST_REL R (MAP f1 funs) (GENLIST f2 (LENGTH funs))`,
  recInduct SNOC_INDUCT >> fs [] >>
  fs [GENLIST,MAP_SNOC,LIST_REL_SNOC] >> rpt strip_tac
  >- (first_x_assum match_mp_tac >>
      metis_tac [EL_SNOC,DECIDE ``n<m ==> n < SUC m``]) >>
  first_x_assum (qspec_then `LENGTH l` mp_tac) >>
  fs [SNOC_APPEND,EL_LENGTH_APPEND]);
val _ = if null (hyp list_rel_map_genlist_replay) then () else raise Fail "local theorem has hypotheses";
val _ = (print "list_rel_map_genlist_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl list_rel_map_genlist_replay); print "\n");
val _ = (print "findi_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl indexedListsTheory.findi_def); print "\n");
val _ = (print "compile_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_def); print "\n");
val _ = (print "compile_decs_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_decs_def); print "\n");
val _ = (print "compile_op_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_op_def); print "\n");
val _ = (print "compile_arith_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_arith_def); print "\n");
val _ = (print "copy_str_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.CopyByteStr_def); print "\n");
val _ = (print "copy_aw8_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.CopyByteAw8_def); print "\n");
val _ = (print "rules_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_rules); print "\n");
val _ = (print "induction_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_ind); print "\n");
val _ = (print "cases_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_cases); print "\n");
val _ = (print "env_rel_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl env_rel_def); print "\n");
val _ = (print "proof_initial_state_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl initial_state'_def); print "\n");
val _ = (print "state_rel_initial_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl state_rel_initial_state); print "\n");
val _ = (print "v_rel_bool_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_Boolv); print "\n");
val _ = (print "v_rel_unit_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_Unitv); print "\n");
val _ = (print "v_rel_to_list_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_to_list); print "\n");
val _ = (print "imp_v_rel_to_list_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl IMP_v_rel_to_list); print "\n");
val _ = (print "dest_constant_imp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl dest_Constant_IMP); print "\n");
val _ = (print "dest_constants_imp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl dest_Constants_IMP); print "\n");
val _ = (print "dest_constant_evaluate_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl dest_Constant_evaluate); print "\n");
val _ = (print "dest_constants_evaluate_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl dest_Constants_evaluate); print "\n");
val _ = (print "evaluate_smart_cons_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_SmartCons); print "\n");
val _ = (print "do_eval_install_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl do_eval_install); print "\n");
val _ = (print "compile_decs_correct2_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_decs_correct2); print "\n");
(* The singleton declaration theorem has independent state type parameters. *)
val _ = (print "evaluate_decs_sing_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_decs_sing); print "\n");
val _ = (print "evaluate_let_error_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_Let_error); print "\n");
val _ = (print "evaluate_op_error_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_Op_error); print "\n");
val _ = (print "v_rel_to_words_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_to_words); print "\n");
val _ = (print "v_rel_to_bytes_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_to_bytes); print "\n");
(* Typed replay of the local environment extension lemmas. *)
val env_cons_upd_replay = prove
  (``env_rel (env with v updated_by f) m db /\ v_rel v1 v2 ==>
     env_rel (env with v updated_by (\xs. (n,v1) :: f xs)) (SOME n :: m) (v2 :: db)``,
   fs [env_rel_def, indexedListsTheory.findi_def, GSYM arithmeticTheory.ADD1] >>
   rw [] >> fs [] >> rw [] >> fs []);
val env_cons_replay = prove
  (``env_rel (env with <| v := xs |>) m db /\ v_rel v1 v2 ==>
     env_rel (env with <| v := (n,v1) :: xs |>) (SOME n :: m) (v2 :: db)``,
   simp [combinTheory.K_DEF, env_cons_upd_replay]);
val _ = (print "env_rel_cons_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl env_cons_replay); print "\n");
val _ = (print "env_rel_cons_upd_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl env_cons_upd_replay); print "\n");
val env_append_replay = prove
  (``!name_prefix prefix db_prefix env m db.
      env_rel env m db /\ LIST_REL v_rel (MAP SND prefix) db_prefix /\
      name_prefix = MAP (SOME o FST) prefix ==>
      env_rel (env1 with <| v := prefix ++ env.v |>) (name_prefix ++ m) (db_prefix ++ db)``,
   Induct >> fs [] >- (rw [env_rel_def]) >>
   Cases_on `prefix` >> fs [PULL_EXISTS] >> rw [] >>
   PairCases_on `h` >> fs [] >> match_mp_tac env_cons_replay >> fs []);
val _ = (print "env_rel_append_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl env_append_replay); print "\n");
(* Typed replay of find_recfun_EL[local], using its original induction proof. *)
val find_recfun_el_replay = prove
  (``!(l0 : (mlstring # 'a # 'b) list) n.
      n < LENGTH l0 /\ ALL_DISTINCT (MAP FST l0) ==>
      semanticPrimitives$find_recfun (FST (EL n l0)) l0 = SOME (SND (EL n l0))``,
   Induct >> fs [] >> simp [Once semanticPrimitivesTheory.find_recfun_def, FORALL_PROD] >>
   rpt strip_tac >> Cases_on `n` >> fs [] >> rw [] >> fs [MEM_MAP] >>
   fs [FORALL_PROD] >> fs [MEM_EL] >> metis_tac [PAIR,PAIR_EQ,FST]);
val _ = (print "find_recfun_el_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl find_recfun_el_replay); print "\n");
(* Typed replay of state_rel_dec_clock[local], which is not exported. *)
val state_clock_replay = prove
  (``!(s : ('a, 'b) flatSem$state) (t : ('a, 'b) closSem$state).
      state_rel s t ==> s.clock = t.clock /\
        state_rel (flatSem$dec_clock s) (closSem$dec_clock 1 t)``,
   simp [state_rel_def, flatSemTheory.dec_clock_def, closSemTheory.dec_clock_def]);
val _ = (print "state_rel_dec_clock_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl state_clock_replay); print "\n");
val _ = (print "state_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl state_rel_def); print "\n");
val _ = (print "lookup_refv_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_refv); print "\n");
val _ = (print "lookup_byte_array_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_byte_array); print "\n");
val _ = (print "lookup_array_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_array); print "\n");
val _ = (print "lookup_thunk_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_thunk); print "\n");
val _ = (print "store_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl store_rel_def); print "\n");
val _ = (print "inc_compile_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl inc_compile_decs'_def); print "\n");
val _ = (print "install_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl install_config_rel'_def); print "\n");
val _ = (print "exc_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.exc_rel_def); print "\n");
val _ = (print "result_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.result_rel_def); print "\n");
val _ = (print "clos_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl closSemTheory.semantics_def); print "\n");
val _ = (print "compile_semantics_prime_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_semantics'); print "\n");
val _ = (print "install_rel_unprimed_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl install_config_rel_def); print "\n");
val _ = (print "compile_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_semantics); print "\n");
val _ = (print "compile_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_correct); print "\n");
val _ = (print "compile_decs_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_decs_correct); print "\n");

(* Replay the local initializer syntax theorem with the original case split. *)
val no_mti_compile_init_replay = Q.prove (
  `closProps$no_mti (clos_interp$compile_init b)`,
  Cases_on `b` >> fs [] >> EVAL_TAC);
val _ = (print "no_mti_compile_init_replay="; Lib.with_flag (Globals.show_types,true) print_term (concl no_mti_compile_init_replay); print "\n");

(* Replay the second local declaration of this duplicated HOL name. *)
val contains_App_SOME_compile_init_2549_replay = Q.prove (
  `1 <= max_app ==> closProps$contains_App_SOME max_app [clos_interp$compile_init b] = F`,
  Cases_on `b` >> fs [] >> EVAL_TAC >> fs []);
val _ = (print "contains_App_SOME_compile_init_2549_replay="; Lib.with_flag (Globals.show_types,true) print_term (concl contains_App_SOME_compile_init_2549_replay); print "\n");

(* Replay the complete local callback-composition theorem. *)
val inc_compile_decs_intro_replay = Q.prove (
  `backendProps$pure_co (clos_interp$insert_interp ## I) o
     backendProps$pure_co flat_to_closProof$inc_compile_decs' o f =
   backendProps$pure_co flat_to_clos$inc_compile_decs o f /\
   backendProps$pure_cc flat_to_closProof$inc_compile_decs'
     (backendProps$pure_cc (clos_interp$insert_interp ## I) cc) =
   backendProps$pure_cc flat_to_clos$inc_compile_decs cc`,
  fs [backendPropsTheory.pure_co_def, FUN_EQ_THM, backendPropsTheory.pure_cc_def,
      flat_to_closTheory.inc_compile_decs_def, FORALL_PROD, inc_compile_decs'_def] >> rw [] >>
  Cases_on `f x` >> fs [] >>
  fs [flat_to_closTheory.inc_compile_decs_def, inc_compile_decs'_def]);
val _ = (print "inc_compile_decs_intro_replay="; Lib.with_flag (Globals.show_types,true) print_term (concl inc_compile_decs_intro_replay); print "\n");

val _ = if null (hyp v_rel_v_to_char_list) then () else raise Fail "hypotheses: v_rel_v_to_char_list";
val _ = (print "v_rel_v_to_char_list_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_v_to_char_list); print "\n");

val _ = if null (hyp imp_cmp_eq_num_cmp) then () else raise Fail "hypotheses: imp_cmp_eq_num_cmp";
val _ = (print "imp_cmp_eq_num_cmp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl imp_cmp_eq_num_cmp); print "\n");

(* Replay the local primitive-type prerequisite used in the operator proofs. *)
val check_type_IntT_flat_to_v_replay = prove (
  ``semanticPrimitives$check_type ast$IntT (flatSem$flat_to_v (v:flatSem$v)) ==>
    ?i. v = flatSem$Litv (ast$IntLit i)``,
  Cases_on `v` >>
  simp [flatSemTheory.flat_to_v_def, semanticPrimitivesTheory.check_type_def,
        flatSemTheory.Boolv_def, semanticPrimitivesTheory.Boolv_def] >> rw []);
val _ = if null (hyp check_type_IntT_flat_to_v_replay) then () else raise Fail "hypotheses: check_type_IntT_flat_to_v";
val _ = (print "check_type_IntT_flat_to_v_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl check_type_IntT_flat_to_v_replay); print "\n");
val _ = if null (hyp op_from_to) then () else raise Fail "hypotheses: op_from_to";
val _ = (print "op_from_to_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_from_to); print "\n");
val _ = if null (hyp compile_op_correct) then () else raise Fail "hypotheses: compile_op_correct";
val _ = (print "compile_op_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_op_correct); print "\n");

(* Replay the remaining literal cases used by op_from_to and op_arith. *)
fun replay_flat_literal_check label tm =
  let val th = prove (tm,
    Cases_on `v` >>
    simp [flatSemTheory.flat_to_v_def, semanticPrimitivesTheory.check_type_def,
          flatSemTheory.Boolv_def, semanticPrimitivesTheory.Boolv_def] >> rw [])
  in if null (hyp th) then
       (print (label ^ "="); Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
     else raise Fail ("hypotheses: " ^ label)
  end;
val _ = replay_flat_literal_check "check_type_Float64T_flat_to_v_typed"
  ``semanticPrimitives$check_type ast$Float64T (flatSem$flat_to_v (v:flatSem$v)) ==>
    ?w. v = flatSem$Litv (ast$Float64 w)``;
val _ = replay_flat_literal_check "check_type_WordT_W8_flat_to_v_typed"
  ``semanticPrimitives$check_type (ast$WordT ast$W8) (flatSem$flat_to_v (v:flatSem$v)) ==>
    ?w. v = flatSem$Litv (ast$Word8 w)``;
val _ = replay_flat_literal_check "check_type_WordT_W64_flat_to_v_typed"
  ``semanticPrimitives$check_type (ast$WordT ast$W64) (flatSem$flat_to_v (v:flatSem$v)) ==>
    ?w. v = flatSem$Litv (ast$Word64 w)``;
val _ = replay_flat_literal_check "check_type_CharT_flat_to_v_typed"
  ``semanticPrimitives$check_type ast$CharT (flatSem$flat_to_v (v:flatSem$v)) ==>
    ?c. v = flatSem$Litv (ast$Char c)``;
val check_type_BoolT_flat_to_v_replay = prove (
  ``semanticPrimitives$check_type ast$BoolT (flatSem$flat_to_v (v:flatSem$v)) ==>
    v = flatSem$Boolv F \/ v = flatSem$Boolv T``,
  Cases_on `v` >>
  simp [flatSemTheory.flat_to_v_def, semanticPrimitivesTheory.check_type_def,
        flatSemTheory.Boolv_def, semanticPrimitivesTheory.Boolv_def] >> rw []);
val _ = if null (hyp check_type_BoolT_flat_to_v_replay) then () else raise Fail "hypotheses: check_type_BoolT_flat_to_v";
val _ = (print "check_type_BoolT_flat_to_v_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl check_type_BoolT_flat_to_v_replay); print "\n");

(* These two local declarations have the same statement; replay each source
   proof with its original binder names and type annotations. *)
val MAP_n2w_o_ORD_11_replay = prove (
  ``!l1 l2. MAP ((n2w :num -> word8) o ORD) l1 = MAP (n2w o ORD) l2 <=> l1 = l2``,
  Induct >> Cases_on `l2` >> fs [wordsTheory.n2w_11, EVAL ``dimword (:8)``,
    arithmeticTheory.MOD_LESS, stringTheory.ORD_BOUND, stringTheory.ORD_11]);
val _ = if null (hyp MAP_n2w_o_ORD_11_replay) then () else raise Fail "hypotheses: MAP_n2w_o_ORD_11";
val _ = (print "MAP_n2w_o_ORD_11_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl MAP_n2w_o_ORD_11_replay); print "\n");
val MAP_n2w_ORD_eq_replay = prove (
  ``!s s'. (MAP (n2w o ORD) s = MAP (n2w o ORD) s' :word8 list) <=> s = s'``,
  Induct >> Cases_on `s'` >> gvs [wordsTheory.n2w_11, EVAL ``dimword (:8)``,
    arithmeticTheory.MOD_LESS, stringTheory.ORD_BOUND, stringTheory.ORD_11]);
val _ = if null (hyp MAP_n2w_ORD_eq_replay) then () else raise Fail "hypotheses: MAP_n2w_ORD_eq";
val _ = (print "MAP_n2w_ORD_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl MAP_n2w_ORD_eq_replay); print "\n");
val _ = if null (hyp op_eval) then () else raise Fail "hypotheses: op_eval";
val _ = (print "op_eval_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_eval); print "\n");
val _ = if null (hyp op_id) then () else raise Fail "hypotheses: op_id";
val _ = (print "op_id_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_id); print "\n");
val _ = if null (hyp op_shifts) then () else raise Fail "hypotheses: op_shifts";
val _ = (print "op_shifts_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_shifts); print "\n");
val _ = if null (hyp op_eq_gc) then () else raise Fail "hypotheses: op_eq_gc";
val _ = (print "op_eq_gc_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_eq_gc); print "\n");
val _ = if null (hyp op_ffi) then () else raise Fail "hypotheses: op_ffi";
val _ = (print "op_ffi_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_ffi); print "\n");
val _ = if null (hyp compile_op_evaluates_args) then () else raise Fail "hypotheses: compile_op_evaluates_args";
val _ = (print "compile_op_evaluates_args_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_op_evaluates_args); print "\n");
val _ = if null (hyp op_globals) then () else raise Fail "hypotheses: op_globals";
val _ = (print "op_globals_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_globals); print "\n");
val _ = if null (hyp op_blocks) then () else raise Fail "hypotheses: op_blocks";
val _ = (print "op_blocks_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_blocks); print "\n");
val _ = if null (hyp op_refs) then () else raise Fail "hypotheses: op_refs";
val _ = (print "op_refs_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_refs); print "\n");
val _ = if null (hyp op_vectors) then () else raise Fail "hypotheses: op_vectors";
val _ = (print "op_vectors_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_vectors); print "\n");
val _ = if null (hyp op_str) then () else raise Fail "hypotheses: op_str";
val _ = (print "op_str_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_str); print "\n");

val _ = if null (hyp op_thunk) then () else raise Fail "hypotheses: op_thunk";
val _ = (print "op_thunk_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_thunk); print "\n");

val _ = if null (hyp op_byte_copy) then () else raise Fail "hypotheses: op_byte_copy";
val _ = (print "op_byte_copy_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_byte_copy); print "\n");

val _ = if null (hyp op_byte_arrays) then () else raise Fail "hypotheses: op_byte_arrays";
val _ = (print "op_byte_arrays_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_byte_arrays); print "\n");

val _ = if null (hyp op_arrays) then () else raise Fail "hypotheses: op_arrays";
val _ = (print "op_arrays_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_arrays); print "\n");

val _ = if null (hyp op_test) then () else raise Fail "hypotheses: op_test";
val _ = (print "op_test_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_test); print "\n");

val _ = if null (hyp op_arith) then () else raise Fail "hypotheses: op_arith";
val _ = (print "op_arith_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl op_arith); print "\n");

val _ = if null (hyp compile_single_DEEP_INTRO) then () else raise Fail "hypotheses: compile_single_DEEP_INTRO";
val _ = (print "compile_single_DEEP_INTRO_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_single_DEEP_INTRO); print "\n");

(* Replay the original local rel_update_thunk proof with explicit state types. *)
val rel_update_thunk_replay = Q.prove (
  `state_rel (s1 : ('a,'b) flatSem$state) (s2 : ('a,'b) closSem$state) /\
   LIST_REL v_rel vs ys ==>
   (flatSem$update_thunk [flatSem$Loc v ptr] s1.refs vs = SOME refs1 ==>
    ?refs2. closSem$update_thunk [closSem$RefPtr v ptr] s2.refs ys = SOME refs2 /\
      state_rel (s1 with refs := refs1) (s2 with refs := refs2))`,
  rw [] >>
  gvs [oneline flatSemTheory.update_thunk_def, oneline closSemTheory.update_thunk_def,
       AllCaseEqs()] >> rw [] >>
  gvs [semanticPrimitivesTheory.store_assign_def, semanticPrimitivesTheory.store_v_same_type_def] >>
  Cases_on `EL ptr s1.refs` >> gvs [] >>
  Cases_on `t` >> gvs [] >>
  `?b. FLOOKUP s2.refs ptr = SOME (closSem$Thunk NotEvaluated b)` by (
    gvs [state_rel_def, store_rel_def] >>
    last_x_assum $ qspec_then `ptr` assume_tac >> gvs []) >>
  gvs [oneline flatSemTheory.dest_thunk_def, oneline closSemTheory.dest_thunk_def,
       AllCaseEqs()] >>
  gvs [Once v_rel_cases, closSemTheory.store_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
  (TRY (drule_all lookup_refv >> rw [] >> gvs []) >>
   TRY (drule_all lookup_byte_array >> rw [] >> gvs []) >>
   TRY (drule_all lookup_array >> rw [] >> gvs []) >>
   gvs [state_rel_def, store_rel_def, finite_mapTheory.FLOOKUP_UPDATE, EL_LUPDATE] >> rw []
   >- (rename1 `FLOOKUP s2.refs idx = _` >> last_x_assum (qspec_then `idx` assume_tac) >> gvs [])
   >- (simp [Once v_rel_cases] >> metis_tac [])
   >- (rename1 `EL idx s1.refs` >> last_x_assum (qspec_then `idx` assume_tac) >> gvs [])));
val _ = if null (hyp rel_update_thunk_replay) then () else raise Fail "hypotheses: rel_update_thunk";
val _ = (print "rel_update_thunk_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl rel_update_thunk_replay); print "\n");
