load "flat_to_closProofTheory";
open HolKernel Parse boolLib bossLib listTheory pairTheory;
open flat_to_closProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
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
