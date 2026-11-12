load "clos_to_bvlProofTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "chain_installed_def=" clos_to_bvlProofTheory.chain_installed_def;
val _ = show_thm "chain_installed_cons=" clos_to_bvlProofTheory.chain_installed_cons;
val _ = show_thm "chain_installed_SUBMAP=" clos_to_bvlProofTheory.chain_installed_SUBMAP;
val _ = show_thm "chain_installed_thm=" clos_to_bvlProofTheory.chain_installed_thm;
val _ = show_thm "chain_installed_chain_exps=" clos_to_bvlProofTheory.chain_installed_chain_exps;
val _ = show_thm "submap_rel_def_typed=" closPropsTheory.SUBMAP_rel_def;
val _ = show_thm "evaluate_code_submap_typed=" closPropsTheory.evaluate_code_SUBMAP;
val _ = show_thm "chain_exps_semantics_typed=" clos_to_bvlProofTheory.chain_exps_semantics;
val _ = show_thm "chain_exps_semantics_call_typed=" clos_to_bvlProofTheory.chain_exps_semantics_call;
val _ = show_thm "alist_to_fmap_APPEND_typed=" alistTheory.alist_to_fmap_APPEND;
val _ = show_thm "lookup_fromList_typed=" sptreeTheory.lookup_fromList;
val _ = show_thm "lookup_fromAList_typed=" sptreeTheory.lookup_fromAList;
val _ = show_thm "fromAList_append_typed=" sptreeTheory.fromAList_append;
val _ = show_thm "init_code_ok_typed=" clos_to_bvlProofTheory.init_code_ok;
val _ = show_thm "clos_state_cc_def_typed=" clos_to_bvlProofTheory.clos_state_cc_def;
val _ = show_thm "kcompile_csyntax_ok_typed=" clos_to_bvlProofTheory.kcompile_csyntax_ok;
val _ = show_thm "elist_globals_SND_renumber_code_locs_list_typed=" clos_to_bvlProofTheory.elist_globals_SND_renumber_code_locs_list;
val _ = show_thm "elist_globals_SND_ncompile_inc_typed=" clos_to_bvlProofTheory.elist_globals_SND_ncompile_inc;
val _ = show_thm "compile_elist_globals_typed=" clos_to_bvlProofTheory.compile_elist_globals;
val _ = show_thm "mcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.mcompile_inc_uncurry;
val _ = show_thm "acompile_inc_uncurry_typed=" clos_to_bvlProofTheory.acompile_inc_uncurry;
val _ = show_thm "ccompile_inc_uncurry_typed=" clos_to_bvlProofTheory.ccompile_inc_uncurry;
val _ = show_thm "compile_inc_uncurry_typed=" clos_to_bvlProofTheory.compile_inc_uncurry;
val _ = show_thm "fcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.fcompile_inc_uncurry;
val _ = show_thm "semantics_cond_call_compile_inc_typed=" clos_to_bvlProofTheory.semantics_cond_call_compile_inc;
val _ = show_thm "compile_common_semantics_typed=" clos_to_bvlProofTheory.compile_common_semantics;
val _ = show_thm "compile_semantics_typed=" clos_to_bvlProofTheory.compile_semantics;
val _ = show_thm "BAG_UNION_MONO_typed=" clos_to_bvlProofTheory.BAG_UNION_MONO;
val _ = show_thm "BAG_FILTER_DEF_typed=" bagTheory.BAG_FILTER_DEF;
val _ = show_thm "FINITE_BAG_FILTER_typed=" bagTheory.FINITE_BAG_FILTER;
val _ = show_thm "BAG_IMAGE_DEF_typed=" bagTheory.BAG_IMAGE_DEF;
val _ = show_thm "BAG_CARD_RELn_typed=" bagTheory.BAG_CARD_RELn;
val _ = show_thm "BAG_CARD_typed=" bagTheory.BAG_CARD;
val _ = show_thm "FINITE_SUB_BAG_typed=" bagTheory.FINITE_SUB_BAG;
val _ = show_thm "SUB_BAG_CARD_typed=" bagTheory.SUB_BAG_CARD;
val _ = show_thm "BAG_IMAGE_SUB_BAG_typed=" clos_to_bvlProofTheory.BAG_IMAGE_SUB_BAG;
val _ = show_thm "trivia_1_typed=" clos_to_bvlProofTheory.trivia_1;
(* The source declaration is local; replay its original proof with inferred types. *)
val show_SUBSET_replay = Q.prove (
  `(!x. x IN s ==> x IN t) ==> s SUBSET t`,
  fs [pred_setTheory.SUBSET_DEF]);
val _ = show_thm "show_SUBSET_replay=" show_SUBSET_replay;
val REPLICATE_1_replay = Q.prove (`REPLICATE 1 x = [x]`, EVAL_TAC);
val _ = show_thm "REPLICATE_1_replay=" REPLICATE_1_replay;
val obvious_arith_comm_replay = Q.prove (
  `((a : num) = b + a) = (b = 0)`,
  Cases_on `b` >> fs []);
val _ = show_thm "obvious_arith_comm_replay=" obvious_arith_comm_replay;
val _ = show_thm "EXISTS_CONS_NOT_NULL_typed=" clos_to_bvlProofTheory.EXISTS_CONS_NOT_NULL;
val _ = show_thm "code_locs_Op_cons_typed=" clos_to_bvlProofTheory.code_locs_Op_cons;
val _ = show_thm "MAP_FST_chain_exps_typed=" clos_to_bvlProofTheory.MAP_FST_chain_exps;
val _ = show_thm "set_MAP_code_sort_typed=" clos_to_bvlProofTheory.set_MAP_code_sort;
val _ = show_thm "compile_exps_IMP_acc_typed=" clos_to_bvlProofTheory.compile_exps_IMP_acc;
(* Replay the local accumulator-suffix theorem with its inferred carriers. *)
val build_aux_lemma2_replay = Q.prove (
  `clos_to_bvl$build_aux n k aux = (a,b) ==> ?z. b = z ++ aux`,
  mp_tac (SPEC_ALL clos_to_bvlTheory.build_aux_acc) >> rw[] >> fs[]);
val _ = show_thm "build_aux_lemma2_replay=" build_aux_lemma2_replay;
(* Replay the original local recursive-layout label theorem. *)
local
  open preamble listTheory clos_to_bvlTheory
in
  val build_aux_thm_replay = Q.prove (
    `!c n aux n7 aux7.
      build_aux n c aux = (n7,aux7++aux) ==>
      MAP FST aux7 = REVERSE (GENLIST ($+ n o $* 2) (LENGTH c))`,
    Induct >> simp[build_aux_def] >> srw_tac[][] >>
    qmatch_assum_abbrev_tac `build_aux nn kk auxx = Z` >>
    qspecl_then [`kk`,`nn`,`auxx`] strip_assume_tac build_aux_acc >>
    Cases_on `build_aux nn kk auxx` >> UNABBREV_ALL_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac std_ss [Once (CONS_APPEND)] >>
    full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)] >> res_tac >>
    srw_tac[][GENLIST,REVERSE_APPEND,REVERSE_GENLIST,PRE_SUB1] >>
    simp[LIST_EQ_REWRITE]);
  val _ = show_thm "build_aux_thm_replay=" build_aux_thm_replay;
end;
val _ = show_thm "rel_dest_thunk_NotThunk_typed=" clos_to_bvlProofTheory.rel_dest_thunk_NotThunk;
val _ = show_thm "rel_dest_thunk_typed=" clos_to_bvlProofTheory.rel_dest_thunk;
val _ = show_thm "do_build_const_thm_typed=" clos_to_bvlProofTheory.do_build_const_thm;
(* The original local state-update equality with its independent state carriers. *)
val refs_lemma_replay = Q.prove (
  `(t2 with refs := t2.refs) = (t2 : ('a,'b) bvlSem$state)`,
  fs [bvlSemTheory.state_component_equality]);
val _ = show_thm "refs_lemma_replay=" refs_lemma_replay;
val _ = show_thm "evaluate_IMP_evaluate_chained_typed=" clos_to_bvlProofTheory.evaluate_IMP_evaluate_chained;
val _ = show_thm "chained_lemma_typed=" clos_to_bvlProofTheory.chained_lemma;
val _ = show_thm "code_installed_cons_typed=" clos_to_bvlProofTheory.code_installed_cons;
val _ = show_thm "compile_exps_same_aux_typed=" clos_to_bvlProofTheory.compile_exps_same_aux;
val _ = show_thm "compile_exps_twice_IS_SUBLIST_typed=" clos_to_bvlProofTheory.compile_exps_twice_IS_SUBLIST;
val _ = show_thm "compile_exps_APPEND_typed=" clos_to_bvlProofTheory.compile_exps_APPEND;
val _ = show_thm "chain_exps_cons_typed=" clos_to_bvlProofTheory.chain_exps_cons;
val _ = show_thm "code_installed_insert_typed=" clos_to_bvlProofTheory.code_installed_insert;
val _ = show_thm "FEVERY_FUPDATE_LIST_SUFF_typed=" clos_to_bvlProofTheory.FEVERY_FUPDATE_LIST_SUFF;
val _ = show_thm "not_domain_lookup_typed=" clos_to_bvlProofTheory.not_domain_lookup;
(* The original union lemmas are local; replay their full statements from the
   exported sparse-tree monotonicity theorems. *)
val cl_rel_union_replay = Q.prove (
  `!a x y. clos_to_bvlProof$cl_rel max_app f2 refs code a x y ==>
           clos_to_bvlProof$cl_rel max_app f2 refs (sptree$union code c2) a x y`,
  metis_tac [clos_to_bvlProofTheory.cl_rel_subspt, sptreeTheory.subspt_union]);
val _ = show_thm "cl_rel_union_replay=" cl_rel_union_replay;
val v_rel_union_replay = Q.prove (
  `!c2 x y. clos_to_bvlProof$v_rel max_app f2 refs code x y ==>
            clos_to_bvlProof$v_rel max_app f2 refs (sptree$union code c2) x y`,
  metis_tac [clos_to_bvlProofTheory.v_rel_subspt, sptreeTheory.subspt_union]);
val _ = show_thm "v_rel_union_replay=" v_rel_union_replay;
(* Replay original shared-array selector theorem. *)
local
  open preamble clos_to_bvlTheory clos_to_bvlProofTheory bvlSemTheory bvlPropsTheory listTheory backend_commonTheory
in
  open bvl_jumpProofTheory;
  val el_append2 = Q.prove (`∀l x. EL (LENGTH l) (l++[x]) = x`,
    Induct_on `l` >> srw_tac[][]);
  val _ = temp_delsimps ["NORMEQ_CONV"];
  val _ = diminish_srw_ss ["ABBREV"];
  val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "fromAList_def", "domain_union", "domain_insert"];
  val _ = set_trace "BasicProvers.var_eq_old" 1;
  val ARITH_TAC = intLib.ARITH_TAC;
  val el_append2_lemma_replay = Q.prove (
    `  !n args.
    n+1 = LENGTH args
    ⇒
    EL (SUC n) (args ++ [x]) = x`,
  Induct_on `args` >> srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1, el_append2]);
  val el_append2_lemma = el_append2_lemma_replay;
  val sum_genlist_triangle_help_replay = Q.prove (
    `  !x. SUM (GENLIST (\y. y) (x+1)) = x * (x + 1) DIV 2`,
  Induct >>
  fs [GENLIST, SUM_SNOC, GSYM ADD1] >>
  simp [ADD1] >>
  ARITH_TAC);
  val sum_genlist_triangle_help = sum_genlist_triangle_help_replay;
  val sum_genlist_triangle_replay = Q.prove (
    `  !x. SUM (GENLIST (\y. y) x) = x * (x - 1) DIV 2`,
  rw [] >>
  mp_tac (Q.SPEC `x-1` sum_genlist_triangle_help) >>
  Cases_on `x = 0` >>
  simp []);
  val sum_genlist_triangle = sum_genlist_triangle_replay;
  val triangle_table_size_replay = Q.prove (
    `  !max f. LENGTH (FLAT (GENLIST (\x. (GENLIST (\y. f x y) x)) max)) =
    max * (max -1) DIV 2`,
  rw [LENGTH_FLAT, MAP_GENLIST, combinTheory.o_DEF, sum_genlist_triangle]);
  val triangle_table_size = triangle_table_size_replay;
  val tri_lemma_replay = Q.prove (
    `  !tot max_app.
    tot < max_app ⇒
    tot + tot * (tot − 1) DIV 2 < max_app + (max_app − 1) * (max_app − 2) DIV 2`,
  Induct_on `max_app` >>
  rw [ADD1] >>
  `tot = max_app ∨ tot < max_app` by decide_tac >>
  rw [] >>
  res_tac >>
  `max_app + (max_app − 1) * (max_app − 2) DIV 2 < max_app + (max_app * (max_app − 1) DIV 2 + 1)`
  suffices_by decide_tac >>
  simp [] >>
  rpt (pop_assum kall_tac) >>
  Induct_on `max_app` >>
  rw [ADD1] >>
  ARITH_TAC);
  val tri_lemma = tri_lemma_replay;
  val triangle_div_lemma_replay = Q.prove (
    `  !max_app n tot.
    tot < max_app ∧ n < tot
    ⇒
    n + tot * (tot − 1) DIV 2 < max_app * (max_app − 1) DIV 2`,
  rw [] >>
  `(tot - 1) + (tot * (tot − 1) DIV 2) < max_app * (max_app − 1) DIV 2`
  suffices_by decide_tac >>
  `((max_app - 1) - 1) + ((max_app - 1) * ((max_app - 1) − 1) DIV 2) < max_app * (max_app − 1) DIV 2`
  suffices_by (
    rw [] >>
    `tot + tot * (tot − 1) DIV 2 < max_app + (max_app − 1) * (max_app − 2) DIV 2`
    suffices_by rw [] >>
    simp [tri_lemma]) >>
  Cases_on `max_app` >>
  fs [] >>
  Cases_on `tot` >>
  fs [ADD1] >>
  Cases_on `n'` >>
  fs [ADD1] >>
  ARITH_TAC);
  val triangle_div_lemma = triangle_div_lemma_replay;
  val triangle_el_replay = Q.prove (
    `  !n tot max_app stuff f g.
    n < tot ∧ tot < max_app
    ⇒
    EL (n + tot * (tot − 1) DIV 2)
      (FLAT
         (GENLIST
            (λtot.
               GENLIST
                 (λprev. f tot prev) tot)
            max_app) ++
       stuff) =
    f tot n`,
  Induct_on `max_app` >>
  rw [GENLIST, FLAT_SNOC] >>
  `tot = max_app ∨ tot < max_app` by decide_tac >>
  rw []
  >- simp [triangle_table_size, EL_APPEND_EQN] >>
  res_tac >>
  fs [] >>
  metis_tac [APPEND_ASSOC]);
  val triangle_el = triangle_el_replay;
  val triangle_el_no_suff_replay = Q.prove (
    `  !n tot max_app f g.
    n < tot ∧ tot < max_app
    ⇒
    EL (n + tot * (tot − 1) DIV 2)
      (FLAT
         (GENLIST
            (λtot.
               GENLIST
                 (λprev. f tot prev) tot)
            max_app)) =
    f tot n`,
  metis_tac [triangle_el, APPEND_NIL]);
  val triangle_el_no_suff = triangle_el_no_suff_replay;
  val evaluate_partial_app_fn_location_code_replay = Q.prove (
    `  !max_app n total_args st args tag ptr x fvs.
     partial_app_fn_location max_app total_args n ∈ domain st.code ∧
     n < total_args ∧ total_args < max_app ⇒
     evaluate
       ([partial_app_fn_location_code max_app
               (mk_elem_at (Var (LENGTH args + 1)) 1)
               (Op (IntOp (Const (&n))) [])],
        (x::(args++[Block tag (ptr::Number(&total_args)::fvs)])),
        st)
     =
     (Rval [Number (&(total_args * (total_args - 1) DIV 2 + n))], st)`,
  rw [partial_app_fn_location_code_def, evaluate_def, do_app_def,do_int_app_def,
      EL_CONS, el_append2, PRE_SUB1, partial_app_fn_location_def] >>
  rw [integerTheory.INT_ADD, integerTheory.INT_MUL, integerTheory.INT_DIV,
      integerTheory.INT_SUB]);
  val evaluate_partial_app_fn_location_code = evaluate_partial_app_fn_location_code_replay;
  val evaluate_generic_app1_replay = Q.prove (
    `  !n args st total_args l fvs cl.
    partial_app_fn_location max_app total_args n ∈ domain st.code ∧
    n < total_args ∧
    total_args < max_app ∧
    n + 1 = LENGTH args ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    cl = Block closure_tag (CodePtr l :: Number (&total_args) :: fvs)
    ⇒
    evaluate ([generate_generic_app max_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location max_app total_args n) ::
                                      Number (&(total_args - (n + 1))) ::
                                      cl::
                                      args)],
         dec_clock n st)`,
  srw_tac[][generate_generic_app_def] >>
  srw_tac[][evaluate_def, do_app_def,do_int_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  fsrw_tac[][do_int_app_def] >>
  `((&total_args):int − &(n+1) >= 0)` by intLib.ARITH_TAC >>
  srw_tac[][] >>
  TRY (rfs [] >> NO_TAC) >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac [ARITH_ss] [ADD1, evaluate_genlist_vars_rev, evaluate_def] >>
  rw [LENGTH_GENLIST, evaluate_def, do_app_def, evaluate_APPEND, el_append2] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ]) >>
  simp [evaluate_partial_app_fn_location_code, global_table_def] >>
  simp [triangle_table_size, partial_app_fn_location_def, triangle_el_no_suff,
        triangle_div_lemma] >>
  srw_tac[][evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB, el_append2, TAKE_LENGTH_APPEND] >>
  CCONTR_TAC >>
  intLib.ARITH_TAC);
  val evaluate_generic_app1 = evaluate_generic_app1_replay;
  val evaluate_generic_app2_replay = Q.prove (
    `  !n args st rem_args prev_args l clo cl.
    partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n + LENGTH prev_args) ∈ domain st.code ∧
    n < rem_args ∧
    n + 1 = LENGTH args ∧
    LENGTH prev_args > 0 ∧
    rem_args + LENGTH prev_args < max_app ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    cl = Block partial_app_tag (CodePtr l :: Number (&rem_args) :: clo :: prev_args)
    ⇒
    evaluate ([generate_generic_app max_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n + LENGTH prev_args)) ::
                                      Number (&rem_args - &(n+1)) ::
                                      clo ::
                                      args ++
                                      prev_args)],
         dec_clock n st)`,
  srw_tac[][generate_generic_app_def, mk_const_def] >>
  srw_tac[][evaluate_def, do_app_def, do_int_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `~(&rem_args − &(n+1):int < 0)` by intLib.ARITH_TAC >>
  srw_tac[][el_append2] >>
  fsrw_tac[][do_int_app_def] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ] >> NO_TAC) >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][evaluate_def, do_app_def] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac[][ADD1] >>
  full_simp_tac(srw_ss())[do_int_app_def] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ] >> NO_TAC) >>
  fs [] >>
  srw_tac [ARITH_ss] [evaluate_genlist_vars_rev, EL_CONS, PRE_SUB1, el_append2] >>
  simp [evaluate_def, do_app_def] >>
  srw_tac [ARITH_ss] [EL_CONS, PRE_SUB1, el_append2] >>
  fsrw_tac[][do_int_app_def] >>
  simp [dec_clock_def] >>
  `&rem_args − &LENGTH args + &(n + (LENGTH prev_args + 1)):int = &(rem_args + LENGTH prev_args)` by intLib.ARITH_TAC >>
  fs [partial_app_fn_location_code_def, global_table_def] >>
  simp [evaluate_APPEND, REVERSE_APPEND, TAKE_LENGTH_APPEND, LENGTH_GENLIST,
        evaluate_def, do_app_def, do_int_app_def,mk_label_def] >>
  simp [integerTheory.INT_ADD, integerTheory.INT_MUL, integerTheory.INT_DIV, integerTheory.INT_SUB] >>
  rw [REVERSE_APPEND, ADD1] >>
  rw [] >>
  fs [ADD1]
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- (
    REWRITE_TAC [ADD_ASSOC, triangle_el_no_suff] >>
    `n + LENGTH prev_args < rem_args + LENGTH prev_args` by decide_tac >>
    `rem_args + LENGTH prev_args < max_app` by decide_tac >>
    REWRITE_TAC [ADD_ASSOC] >>
    simp [triangle_el_no_suff, triangle_div_lemma])
  >- (
    fs [triangle_table_size] >>
    pop_assum mp_tac >>
    REWRITE_TAC [ADD_ASSOC, triangle_el_no_suff] >>
    `n + LENGTH prev_args < rem_args + LENGTH prev_args` by decide_tac >>
    `rem_args + LENGTH prev_args < max_app` by decide_tac >>
    REWRITE_TAC [ADD_ASSOC] >>
    simp [triangle_div_lemma]));
  val evaluate_generic_app2 = evaluate_generic_app2_replay;
  val evaluate_generic_app_partial_replay = Q.prove (
    `  !total_args prev_args st args cl sub_cl.
    partial_app_fn_location
      max_app
      total_args
      (LENGTH prev_args + (LENGTH args - 1)) ∈ domain st.code ∧
    total_args < max_app ∧
    LENGTH args < (total_args + 1) - LENGTH prev_args ∧
    LENGTH args ≠ 0 ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    unpack_closure cl (prev_args, total_args, sub_cl)
    ⇒
    evaluate ([generate_generic_app max_app (LENGTH args-1)], args++[cl], st) =
    if st.clock < LENGTH args - 1 then
      (Rerr(Rabort Rtimeout_error), st with clock := 0)
    else
      (Rval [Block partial_app_tag
                   (CodePtr (partial_app_fn_location
                               max_app total_args
                               (LENGTH prev_args + (LENGTH args - 1))) ::
                            Number (&(total_args -
                                      (LENGTH prev_args + LENGTH args))) ::
                            sub_cl:: args++ prev_args)],
         dec_clock (LENGTH args - 1) st)`,
  rpt GEN_TAC >>
  strip_tac >>
  full_simp_tac(srw_ss())[unpack_closure_cases]
  >- (qspecl_then [‘LENGTH args - 1’, ‘args’, ‘st’, ‘total_args’] mp_tac
                  evaluate_generic_app1 >>
      srw_tac [ARITH_ss] [] >>
      rev_full_simp_tac(srw_ss())[] >>
      ‘&Num total_args' = total_args'’ by intLib.COOPER_TAC >>
      ‘LENGTH args <> 0’ by simp[] >>
      full_simp_tac(std_ss++ARITH_ss)[])
  >- (qspecl_then [‘LENGTH args - 1’, ‘args’, ‘st’, ‘Num rem_args’, ‘prev_args’]
                  mp_tac evaluate_generic_app2 >>
      full_simp_tac (srw_ss()++ARITH_ss) [] >>
      srw_tac [ARITH_ss] [] >>
      ‘LENGTH args <> 0’ by simp [] \\ full_simp_tac (std_ss++ARITH_ss)[] >>
      Cases_on ‘prev_args’ >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      rfs [] >>
      gs[iffRL integerTheory.INT_OF_NUM, Excl "INT_OF_NUM",
         integerTheory.int_ge, int_arithTheory.INT_NUM_SUB] >>
      ‘LENGTH args <> 0’ by simp [] \\ gs[]));
  val _ = show_thm "evaluate_generic_app_partial_replay=" evaluate_generic_app_partial_replay;
  val v_rel_num_rem_args_replay = Q.prove (
    `  !f refs code v1 v2 n.
    v_rel max_app f refs code v1 v2 ∧
    num_remaining_args v1 = SOME n
    ⇒
    ?tag ptr rest exp.
      v2 = Block tag (CodePtr ptr::Number (&n-1)::rest) ∧
      n ≠ 0 ∧
      lookup ptr code = SOME (n+1, exp)`,
  srw_tac[][v_rel_cases] >>
  full_simp_tac(srw_ss())[num_remaining_args_def]
  >- (full_simp_tac(srw_ss())[cl_rel_cases] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[num_remaining_args_def, int_arithTheory.INT_NUM_SUB,closure_code_installed_def,
          EVERY_EL, EL_MAP] >>
      pop_assum (mp_tac o GSYM) >>
      srw_tac[][] >>
      pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      Cases_on `EL k exps_ps` >>
      simp [] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      simp [EL_MAP])
  >- (full_simp_tac(srw_ss())[cl_rel_cases] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[get_num_args_def, add_args_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[num_remaining_args_def, int_arithTheory.INT_NUM_SUB] >>
      intLib.ARITH_TAC));
  val _ = show_thm "v_rel_num_rem_args_replay=" v_rel_num_rem_args_replay;
  val unpack_closure_thm_replay = Q.prove (
  `v_rel max_app f1 t1.refs t1.code func (Block tag (ptr::Number (&n-1)::rest)) ∧
   num_remaining_args func = SOME n
   ⇒
   ?prev_args total_args clo.
     unpack_closure (Block tag (ptr::Number (&n-1)::rest)) (prev_args, total_args, clo) ∧
     total_args < max_app ∧
     n = total_args − LENGTH prev_args + 1  ∧
     (tag = closure_tag ⇒ prev_args = [] ∧ clo = Block tag (ptr::Number (&n-1)::rest))`,
  srw_tac[][unpack_closure_cases, v_rel_cases, cl_rel_cases, num_remaining_args_def] >>
  full_simp_tac(srw_ss())[num_remaining_args_def] >>
  rw_tac bool_ss [] >>
  TRY ARITH_TAC >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[closure_code_installed_def, EVERY_EL] >>
  res_tac >>
  rev_full_simp_tac(srw_ss())[] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[add_args_def, get_num_args_def, EL_MAP] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  TRY decide_tac >>
  TRY (Cases_on `ys`) >>
  full_simp_tac(srw_ss())[ADD1, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [integerTheory.int_ge, integerTheory.INT_LE_SUB_LADD, integerTheory.INT_LE_LT1] >>
  TRY(simp[closure_tag_def]>>NO_TAC) >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  srw_tac[][EL_MAP] >>
  decide_tac) |> INST_TYPE[alpha|->``:'ffi``];
  val _ = show_thm "unpack_closure_thm_replay=" unpack_closure_thm_replay;
  val arith_helper_lem_replay = Q.prove (
    `  LENGTH args' ≠ 0 ⇒ x − 1 − (LENGTH args' − 1) = x − LENGTH args'`,
  decide_tac);
  val _ = show_thm "arith_helper_lem_replay=" arith_helper_lem_replay;
  val arith_helper_lem3_replay = Q.prove (
    `  LENGTH args' < total_args + 1 − LENGTH prev_args ∧
   LENGTH args' ≠ 0 ∧
   total_args − LENGTH prev_args + 1 = num_args − LENGTH prev_args
   ⇒
   total_args − (LENGTH args' + LENGTH prev_args − 1) = total_args + 1 − (LENGTH args' + LENGTH prev_args) ∧
   LENGTH args' + LENGTH prev_args < total_args + 1 ∧
   num_args = total_args+1`,
  simp_tac(std_ss++ARITH_ss)[int_arithTheory.INT_NUM_SUB]);
  val _ = show_thm "arith_helper_lem3_replay=" arith_helper_lem3_replay;
  val _ = show_thm "get_cl_env_def_typed=" clos_to_bvlProofTheory.get_cl_env_def;
  val _ = show_thm "unpack_closure_rules_typed=" clos_to_bvlProofTheory.unpack_closure_rules;
  val _ = show_thm "unpack_closure_cases_typed=" clos_to_bvlProofTheory.unpack_closure_cases;
  val take_drop_lemma_replay = Q.prove (
    `  !rem_args arg_list.
   LENGTH arg_list > rem_args
   ⇒
   TAKE (rem_args + 1) (DROP (LENGTH arg_list − (rem_args + 1)) (arg_list ++ stuff)) =
   DROP (LENGTH arg_list − (rem_args + 1)) arg_list`,
  Induct_on `arg_list` >>fs[ADD1]>>rw[]>>
  Cases_on`rem_args = LENGTH arg_list`>>fs[TAKE_LENGTH_APPEND]);
  val take_drop_lemma = take_drop_lemma_replay;
  val evaluate_generic_app_full_replay = Q.prove (
    `  !n args st rem_args vs l tag exp clo.
    lookup l st.code = SOME (rem_args + 2, exp) ∧
    n + 1 = LENGTH args ∧
    n > rem_args ∧
    rem_args < max_app
    ⇒
    evaluate ([generate_generic_app max_app n], args++[Block tag (CodePtr l :: Number (&rem_args) :: vs)], st) =
    if st.clock < rem_args + 1 then (Rerr(Rabort Rtimeout_error), st with clock := 0) else
      case evaluate ([exp],
                     DROP (LENGTH args − (rem_args + 1)) args ++
                     [Block tag (CodePtr l::Number (&rem_args)::vs)],
                     dec_clock (rem_args + 1) st) of
        | (Rval [v], st') =>
            (case
               evaluate
                 ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 3)) (n − rem_args))],
                  v::Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                      args++[Block tag (CodePtr l::Number (&rem_args)::vs)],
                  st')
             of
               (Rval v,s2) => (Rval [HD v],s2)
             | x => x)
        | x => x`,
  srw_tac[][generate_generic_app_def, mk_const_def] >>
  srw_tac[][evaluate_def, do_app_def, do_int_app_def, el_append2] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [partial_app_tag_def] >>
  fsrw_tac[][do_int_app_def] >>
  `(&rem_args − &(LENGTH args):int < 0)` by intLib.ARITH_TAC >>
  srw_tac[][] >>
  `evaluate ([mk_elem_at (Var (LENGTH args + 1)) 1],
          Number (&rem_args − &LENGTH args):: (args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)]),
          st) =
    (Rval [Number (&rem_args)], st)`
          by srw_tac [ARITH_ss] [evaluate_def, do_app_def,do_int_app_def, PRE_SUB1, EL_CONS, el_append2] >>
  `n + 2 = LENGTH args + 1` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_Jump >>
  srw_tac [ARITH_ss] [LENGTH_GENLIST, evaluate_def, do_app_def] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, do_app_def, evaluate_def] >>
  srw_tac [ARITH_ss] [Once evaluate_CONS, evaluate_def, evaluate_APPEND] >>
  full_simp_tac(srw_ss())[] >>
  `(rem_args + 1) + ((LENGTH args + 1) - rem_args) ≤
     LENGTH (Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                 (args ++
                  [Block tag (CodePtr l::Number (&rem_args)::vs)]))`
             by (srw_tac[][] >>
                 decide_tac) >>
  imp_res_tac evaluate_genlist_vars >>
  pop_assum (qspec_then `st` mp_tac) >>
  `LENGTH args + 1 - rem_args = (LENGTH args + 1) - rem_args` by decide_tac >>
  simp [do_int_app_def] >>
  srw_tac[][] >>
  simp [EL_CONS, PRE_SUB1, el_append2, find_code_def, bvlSemTheory.state_component_equality, FRONT_APPEND] >>
  `LENGTH args > rem_args` by decide_tac >>
  srw_tac[][take_drop_lemma] >>
  qabbrev_tac `res1 =
    bvlSem$evaluate
      ([exp],
       DROP (LENGTH args − (rem_args + 1)) args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)],
       dec_clock (rem_args + 1) st)` >>
  Cases_on `res1` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `q` >>
  full_simp_tac(srw_ss())[] >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `t` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.FULL_CASE_TAC >>
  BasicProvers.FULL_CASE_TAC >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `t` >>
  full_simp_tac(srw_ss())[]);
  val _ = show_thm "evaluate_generic_app_full_replay=" evaluate_generic_app_full_replay;
  val evaluate_genlist_prev_args_no_rev_replay = Q.prove (
    `  !prev_args z x tag arg_list st.
    evaluate (GENLIST (λprev_arg.
      mk_elem_at (Var (LENGTH x)) (prev_arg + LENGTH z)) (LENGTH prev_args),
           x++(Block tag (z++prev_args))::arg_list,
           st)
    =
    (Rval prev_args,st)`,
  Induct_on `prev_args` >>
  srw_tac[][evaluate_def, GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def, do_app_def,do_int_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][] >>
  pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
  srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
  `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
  `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
          by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
  decide_tac);
  val evaluate_genlist_prev_args_no_rev = evaluate_genlist_prev_args_no_rev_replay;
  val _ = show_thm "evaluate_genlist_prev_args_no_rev_replay=" evaluate_genlist_prev_args_no_rev_replay;
  val evaluate_genlist_prev_args1_no_rev_replay = Q.prove (
    `  !prev_args x tag p n cl args st.
    evaluate (GENLIST (λprev_arg.
      mk_elem_at (Var (LENGTH args + 1)) (prev_arg + 3)) (LENGTH prev_args),
           x::(args++[Block tag (p::n::cl::prev_args)]),
           st)
    =
    (Rval prev_args,st)`,
  metis_tac [evaluate_genlist_prev_args_no_rev, APPEND, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``,
             DECIDE ``(SUC 0) = 1``, DECIDE ``SUC (SUC 0) = 2``, ADD1]);
  val evaluate_genlist_prev_args1_no_rev = evaluate_genlist_prev_args1_no_rev_replay;
  val _ = show_thm "evaluate_genlist_prev_args1_no_rev_replay=" evaluate_genlist_prev_args1_no_rev_replay;
  val evaluate_partial_app_fn_replay = Q.prove (
    `  !num_args args' num_args' prev_args tag num tag' l l' fvs exp code.
    lookup l code = SOME (LENGTH args' + LENGTH prev_args + 1,exp) /\
    LENGTH prev_args ≠ 0 ∧
    LENGTH prev_args < num_args ∧
    num_args = LENGTH prev_args + LENGTH args'
    ⇒
    !st. evaluate ([generate_partial_app_closure_fn (num_args - 1) (LENGTH prev_args - 1)],
           DROP (LENGTH args' + LENGTH prev_args − num_args) args' ++
           [Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs)::prev_args)],
           (st with code := code)) =
     if st.clock = 0 then
       (Rerr(Rabort Rtimeout_error), (st with code := code))
     else
       evaluate ([exp],
              DROP (LENGTH args' + LENGTH prev_args − num_args) args'++prev_args++[Block tag' (CodePtr l::num_args'::fvs)],
              dec_clock 1 (st with code := code))`,
  srw_tac[][evaluate_def, generate_partial_app_closure_fn_def, mk_const_def, do_app_def, do_int_app_def] >>
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (srw_ss()++ARITH_ss) [el_append2, evaluate_APPEND] >>
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (std_ss++ARITH_ss) [ADD1] >>
  srw_tac[][evaluate_def] >>
  qabbrev_tac `cl = Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs):: prev_args)` >>
  qspecl_then [`1`, `Block tag' (CodePtr l::num_args'::fvs)::(args' ++ [cl])`,
                       `LENGTH (args')`, `st with code := code`] assume_tac evaluate_genlist_vars >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (std_ss++ARITH_ss) [ADD1,EL_LENGTH_APPEND] >>
  srw_tac[][evaluate_genlist_prev_args1_no_rev, Abbr `cl`, evaluate_def, do_app_def, find_code_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1,EL_LENGTH_APPEND] >>
  srw_tac[][evaluate_genlist_prev_args1_no_rev, evaluate_def, do_app_def, do_int_app_def,find_code_def] >>
  srw_tac[][FRONT_APPEND, TAKE_LENGTH_APPEND, bvlSemTheory.state_component_equality] >> fs[]);
  val _ = show_thm "evaluate_partial_app_fn_replay=" evaluate_partial_app_fn_replay;
  val mk_cl_lem_replay = Q.prove (
    `  l < LENGTH env
   ⇒
   evaluate (GENLIST (λn. Var (n + 3)) l, a::b::c::env, st) =
   evaluate (GENLIST (λn. Var (n + 1)) l, a::env, st)`,
  srw_tac[][] >>
  `l + 3 ≤ LENGTH (a::b::c::env)` by srw_tac [ARITH_ss] [ADD1] >>
  `l + 1 ≤ LENGTH (a::env)` by srw_tac [ARITH_ss] [ADD1] >>
  imp_res_tac evaluate_genlist_vars >>
  srw_tac[][]);
  val _ = show_thm "mk_cl_lem_replay=" mk_cl_lem_replay;
  val mk_cl_lem = mk_cl_lem_replay;
  val evaluate_mk_cl_simpl_replay = Q.prove (
    `  evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 3)) (LENGTH args' − (n + 1)))],
                               v::a::b::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')
   =
   evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args' − (n + 1)))],
                               v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')`,
  srw_tac[][mk_cl_call_def, evaluate_def, do_app_def] >>
  reverse (Cases_on `v`) >>
  srw_tac[][] >>
  TRY (Cases_on `FLOOKUP st'.refs n'` \\ fs []) >>
  BasicProvers.FULL_CASE_TAC >>
  srw_tac[][evaluate_APPEND] >>
  ntac 2 (pop_assum (mp_tac o GSYM)) >>
  srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [evaluate_def, do_app_def] >>
  `LENGTH args' - (n + 1) < LENGTH (args' ++ [Block tag (CodePtr p::Number (&n)::xs)])`
              by srw_tac [ARITH_ss] [] >>
  srw_tac [ARITH_ss] [mk_cl_lem]);
  val _ = show_thm "evaluate_mk_cl_simpl_replay=" evaluate_mk_cl_simpl_replay;
  val evaluate_generic_app_full = evaluate_generic_app_full_replay;
  val evaluate_mk_cl_simpl = evaluate_mk_cl_simpl_replay;
  val evaluate_mk_cl_call_replay = Q.prove (
    `  !cl env s tag p n args args' exp exp2 xs.
    evaluate ([cl],env,s) = (Rval [Block tag (CodePtr p::Number &n::xs)], s) ∧
    evaluate (args,env,s) = (Rval args', s) ∧
    lookup p s.code = SOME (n+2, exp) ∧
    lookup (generic_app_fn_location (LENGTH args' - 1)) s.code =
      SOME (LENGTH args' + 1, generate_generic_app max_app (LENGTH args' - 1)) ∧
    LENGTH args' - 1 ≥ n ∧
    n < max_app ∧
    LENGTH args ≠ 0
    ⇒
    evaluate ([mk_cl_call cl args],env,s) =
     if n = LENGTH args - 1 then
       if s.clock < LENGTH args
       then (Rerr(Rabort Rtimeout_error),s with clock := 0)
       else evaluate ([exp],
                   args' ++ [Block tag (CodePtr p::Number (&(LENGTH args − 1))::xs)],
                   dec_clock (LENGTH args) s)
     else
         if s.clock < n + 2
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
         case evaluate ([exp],
                     DROP (LENGTH args' − (n + 1)) args' ++ [Block tag (CodePtr p::Number (&n)::xs)],
                     dec_clock (n + 2) s)
           of
            | (Rval [v],st') =>
                (case evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args' − (n + 1)))],
                              v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                              st') of
                    | (Rval v,s2) => (Rval [HD v],s2)
                    | x => x)
            | x => x`,
  srw_tac[][Once mk_cl_call_def, evaluate_def, do_app_def, do_int_app_def,do_eq_def, generic_app_fn_location_def] >>
  full_simp_tac(srw_ss())[ADD1] >>
  Cases_on `n = &(LENGTH args − 1)` >>
  srw_tac[][evaluate_APPEND, evaluate_def, do_app_def, do_int_app_def, do_eq_def, find_code_def, FRONT_APPEND] >>
  simp [] >>
  imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >>
  rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
  `LENGTH args <> 0` by simp[] >>
  `LENGTH args' - 1 + 1 = LENGTH args'` by decide_tac >>
  TRY(fs[] \\ NO_TAC) \\
  `lookup p (dec_clock 1 s).code = SOME (n+2,exp)` by srw_tac[][] >>
  imp_res_tac evaluate_generic_app_full >>
  srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def] >>
  simp [evaluate_mk_cl_simpl]);
  val _ = show_thm "evaluate_mk_cl_call_replay=" evaluate_mk_cl_call_replay;
  val evaluate_mk_cl_call = evaluate_mk_cl_call_replay;
  val bEval_def = bvlSemTheory.evaluate_def;
  val evaluate_mk_cl_call_spec_replay = Q.prove (
    `  !s env tag p n args exp xs.
    lookup p s.code = SOME (n+2, exp) ∧
    lookup (generic_app_fn_location (LENGTH args - 1)) s.code =
      SOME (LENGTH args + 1, generate_generic_app max_app (LENGTH args - 1)) ∧
    LENGTH args - 1 ≥ n ∧
    n < max_app ∧
    LENGTH args ≠ 0
    ⇒
    evaluate ([mk_cl_call (Var (LENGTH args)) (GENLIST Var (LENGTH args))],args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
     if n = LENGTH args - 1 then
       if s.clock < LENGTH args
       then (Rerr(Rabort Rtimeout_error),s with clock := 0)
       else evaluate ([exp],
                   args ++ [Block tag (CodePtr p::Number (&(LENGTH args − 1))::xs)],
                   dec_clock (LENGTH args) s)
     else
         if s.clock < n + 2
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
         case evaluate ([exp],
                     DROP (LENGTH args − (n + 1)) args ++ [Block tag (CodePtr p::Number (&n)::xs)],
                     dec_clock (n + 2) s)
           of
            | (Rval [v],st') =>
                (case evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args − (n + 1)))],
                              v::(args ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                              st') of
                    | (Rval v,s2) => (Rval [HD v],s2)
                    | x => x)
            | x => x`,
  rpt strip_tac >>
  `evaluate ([Var (LENGTH args)], args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
   (Rval [Block tag (CodePtr p::Number (&n)::xs)], s)`
           by simp [bEval_def, el_append3] >>
  `evaluate (GENLIST Var (LENGTH args), args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
    (Rval args, s)`
           by (qspecl_then [`0`, `args++[Block tag (CodePtr p::Number (&n)::xs)]++env`, `LENGTH args`]mp_tac evaluate_genlist_vars >>
               simp [ETA_THM] >>
               metis_tac [APPEND_ASSOC, TAKE_LENGTH_APPEND]) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] evaluate_mk_cl_call) >>
  rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  rev_full_simp_tac(srw_ss())[] >>
  first_x_assum match_mp_tac >>
  Cases_on`LENGTH args` \\ fs[GENLIST_CONS]);
  val _ = show_thm "evaluate_mk_cl_call_spec_replay=" evaluate_mk_cl_call_spec_replay;
  val cl_rel_run_lemma1_replay = Q.prove (
    `  num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var num_args, DROP (LENGTH args' - num_args) args' ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args'), t1)`,
  srw_tac[][] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++stuff`, `num_args`, `t1`] evaluate_genlist_vars) >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args') = num_args` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]);
  val _ = show_thm "cl_rel_run_lemma1_replay=" cl_rel_run_lemma1_replay;
  val cl_rel_run_lemma2_replay = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var (num_args + 1), DROP (LENGTH args' - num_args) args' ++ [f] ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args' ++ [f]), t1)`,
  srw_tac[][] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++[f]++stuff`, `num_args+1`, `t1`] evaluate_genlist_vars) >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args'++[f]) = num_args+1` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]) |> Q.INST [`stuff`|-> `[]`] |> SIMP_RULE (srw_ss()) [];
  val _ = show_thm "cl_rel_run_lemma2_replay=" cl_rel_run_lemma2_replay;
  (* Replay the local polymorphic list-relation theorem. *)
  val cl_rel_run_lemma3_replay = Q.prove (
    `LIST_REL R args args' ⇒
     LIST_REL R (DROP (LENGTH args' − n) args) (DROP (LENGTH args' − n) args')`,
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    srw_tac[][] >>
    `n' + (LENGTH args' − n) < LENGTH args` by decide_tac >>
    `n' + (LENGTH args' − n) < LENGTH args'` by metis_tac [] >>
    srw_tac[][EL_DROP]);
  val _ = show_thm "cl_rel_run_lemma3_replay=" cl_rel_run_lemma3_replay;
  val bEval_def = bvlSemTheory.evaluate_def;
  val bEvalOp_def = bvlSemTheory.do_app_def;
  val bEval_free_let_Block_replay = Q.prove (
  `!ys zs.
    evaluate ([x],env,s) = (Rval [Block n (y::z::ys ++ zs)], s)
    ⇒
    evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  ho_match_mp_tac SNOC_INDUCT >>
  srw_tac[][free_let_def, bEval_def] >>
  full_simp_tac(srw_ss())[SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  res_tac >>
  full_simp_tac(srw_ss())[GENLIST, bvlPropsTheory.evaluate_SNOC, bEvalOp_def, bEval_def,
  do_int_app_def] >>
  simp [EL_CONS, PRE_SUB1, el_append3])
   |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];
  val _ = show_thm "bEval_free_let_Block_replay=" bEval_free_let_Block_replay;
  val genlist_el_replay = Q.prove (
    `!skip st r xs args p n env ys.
    FLOOKUP st.refs r = SOME (ValueArray (ys++xs)) ∧
    skip = LENGTH ys
    ⇒
    bvlSem$evaluate (GENLIST (λi. mk_elem_at (Var 0) (i+skip)) (LENGTH xs),
           RefPtr T r:: (args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr T r]::env),
           st)
    =
    (Rval xs, st)`,
  Induct_on `xs` >>
  srw_tac[][evaluate_def, GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def, do_app_def, do_int_app_def,combinTheory.o_DEF] >>
  `FLOOKUP st.refs r = SOME (ValueArray ((ys++[h])++xs))` by srw_tac[][] >>
  first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
  simp [ADD1] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ADD1] >>
  srw_tac[][EL_LENGTH_APPEND]);
  val _ = show_thm "genlist_el_replay=" genlist_el_replay;
  val genlist_el = genlist_el_replay;
  val evaluate_code_for_recc_case_replay = Q.prove (
    `!st r xs args c p n env.
    FLOOKUP st.refs r = SOME (ValueArray xs)
    ⇒
    evaluate ([SND (code_for_recc_case (LENGTH xs) (LENGTH args) c)],
              args ++ Block closure_tag [CodePtr p;Number &n;RefPtr T r]::env,
              st) =
    evaluate ([c],
              args ++ xs ++ [RefPtr T r] ++ args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr T r]::env,
              st)`,
  simp [code_for_recc_case_def, evaluate_def, do_app_def,do_int_app_def] >>
  simp [evaluate_APPEND, EL_LENGTH_APPEND] >>
  rpt strip_tac >>
  `LENGTH args + 1 ≤ LENGTH (RefPtr T r::(args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr T r]::env))`
              by (srw_tac[][] >> intLib.ARITH_TAC) >>
  imp_res_tac evaluate_genlist_vars >>
  full_simp_tac(srw_ss())[] >>
  mp_tac (Q.SPEC `0` genlist_el) >>
  simp [LENGTH_NIL_SYM] >>
  srw_tac[][TAKE_LENGTH_APPEND]);
  val _ = show_thm "evaluate_code_for_recc_case_replay=" evaluate_code_for_recc_case_replay;
end;
val _ = show_thm "get_loc_def_typed=" clos_to_bvlProofTheory.get_loc_def;
(* Replay the original location theorem and its local generated-label prerequisite. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory bvlSemTheory listTheory backend_commonTheory
  val p_genlist = Q.prove (
    `EL k exps_ps = ((n',e),p) ∧
   MAP SND exps_ps = GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps) ∧
   k < LENGTH exps_ps
   ⇒
   p = EL k (GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps))`,
  srw_tac[][] >>
  `EL k (MAP SND exps_ps) = EL k (GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps))` by metis_tac [] >>
  rev_full_simp_tac(srw_ss())[EL_MAP]);
in
  val cl_rel_get_loc_replay = Q.prove (
    `cl_rel max_app f1 refs code (env,fvs) func (Block tag (CodePtr p::n::ys))
   ⇒
   num_stubs max_app ≤ p ∧
   get_loc func = SOME (p-(num_stubs max_app))`,
  srw_tac[][cl_rel_cases] >>
  full_simp_tac(srw_ss())[get_loc_def, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  res_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  srw_tac[][] >>
  `p = EL k (GENLIST (λn. loc + num_stubs max_app + 2*n) (LENGTH exps_ps))` by metis_tac [p_genlist] >>
  srw_tac[][] >>
  intLib.ARITH_TAC);
  val _ = show_thm "cl_rel_get_loc_replay=" cl_rel_get_loc_replay;
end;
(* Replay the original local closure arity theorem. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory bvlSemTheory listTheory backend_commonTheory
in
  val cl_rel_get_num_args_replay = Q.prove (
    `cl_rel max_app f1 refs code (env,ys) func (Block tag (p::Number (&(total_args) - 1)::fvs))
   ⇒
   get_num_args func = SOME total_args`,
  srw_tac[][cl_rel_cases] >>
  full_simp_tac(srw_ss())[get_num_args_def, int_arithTheory.INT_NUM_SUB, EL_MAP, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  res_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  intLib.ARITH_TAC);
  val _ = show_thm "cl_rel_get_num_args_replay=" cl_rel_get_num_args_replay;
end;
(* Replay the two application error propagation theorems. *)
local
  open preamble clos_to_bvlTheory clos_to_bvlProofTheory bvlSemTheory bvlPropsTheory listTheory backend_commonTheory
in
  val evaluate_app_helper_replay = Q.prove (
    `  (!x. r ≠ Rval x) ∧ evaluate (c8,env,s) = (r,s')
    ⇒
    evaluate
           ([case loc of
              NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app)) (c8++[c7])],env,s) = (r, s')`,
  srw_tac[][] >>
  Cases_on `loc` >>
  srw_tac[][bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  srw_tac[][]);
  val _ = show_thm "evaluate_app_helper_replay=" evaluate_app_helper_replay;
  val evaluate_app_helper2_replay = Q.prove (
    `  (!x. r ≠ Rval x) ∧ evaluate (c8,env,s) = (Rval x, s') ∧ evaluate ([c7],env,s') = (r,s'')
    ⇒
    evaluate ([case loc of
              NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app)) (c8++[c7])],env,s) = (r, s'')`,
  srw_tac[][] >>
  Cases_on `loc` >>
  srw_tac[][bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  srw_tac[][]);
  val _ = show_thm "evaluate_app_helper2_replay=" evaluate_app_helper2_replay;
end;
(* Replay the recursive-closure array and environment construction theorem. *)
local
  open preamble clos_to_bvlTheory clos_to_bvlProofTheory bvlSemTheory bvlPropsTheory listTheory backend_commonTheory
in
  val map2_snoc = Q.prove (
    `  !l1 l2 f x y.
    LENGTH l1 = LENGTH l2 ⇒
    MAP2 f (SNOC x l1) (SNOC y l2) = MAP2 f l1 l2 ++ [f x y]`,
  Induct_on `l1` >>
  srw_tac[][] >>
  `l2 = [] ∨ ?h l2'. l2 = h::l2'` by (Cases_on `l2` >> srw_tac[][]) >>
  Cases_on `l2` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac[SNOC_APPEND]);
  val tl_append = Q.prove (
    `  !l1 l2. 0 < LENGTH l1 ⇒ TL (l1 ++ l2) = TL l1 ++ l2`,
  Cases_on `l1` >> srw_tac[][]);
  val evaluate_recc_Lets_replay = Q.prove (
    `  !(ll:(num#'a) list) n7 rr env' (t1:('c,'ffi) bvlSem$state) ys c8 (x:(num#'a)) (x':(num#'a)) ck.
     EVERY (\n. n7 + ns + 2* n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (evaluate
       ([recc_Lets (n7 + ns) (REVERSE (MAP FST ll)) (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + (ns + 2 * LENGTH ll)); Number (&(FST x-1)); RefPtr T rr]::env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) (MAP FST ll) ++
                [Block closure_tag [CodePtr (n7 + (ns + 2* LENGTH ll)); Number (&(FST x'-1)); RefPtr T rr]]++ys));clock := ck |>) =
      evaluate
       ([HD c8],
        MAP2 (\n args. Block closure_tag [CodePtr (n7 + ns + 2* n); Number &(args-1); RefPtr T rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x]) ++ env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP2 (\n args. Block closure_tag [CodePtr (n7 + ns + 2* n); Number &(args-1); RefPtr T rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x']) ++ ys)); clock := ck |>))`,
  recInduct SNOC_INDUCT \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [recc_Lets_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def,recc_Let_def,
     bvlSemTheory.do_app_def,bvlSemTheory.do_int_app_def]
  \\ simp []
  \\ full_simp_tac(srw_ss())[DECIDE ``0 < k + SUC n:num``,EVERY_SNOC,GENLIST, ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE,DECIDE ``n < SUC n + m``,DECIDE ``0 < 1 + SUC n``,
         DECIDE ``0 < 1 + n:num``,DECIDE ``2 < 1 + (1 + (1 + n:num))``]
  \\ simp []
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,MAP_APPEND,MAP, MAP_REVERSE, REVERSE_APPEND, tl_append]
  \\ `LENGTH l = LENGTH (MAP (K (Number 0:bvlSem$v)) (MAP FST (l:(num#'a) list)))` by srw_tac[][]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ pop_assum kall_tac
  \\ rw_tac std_ss [SIMP_RULE std_ss [GSYM APPEND_ASSOC] lupdate_append2, GSYM APPEND_ASSOC]
  \\ simp []
  \\ rw_tac std_ss [PROVE [APPEND_ASSOC] ``!(a:'a list) b c d. a ++ b ++ c ++ d = a ++ b ++ (c ++ d)``] >>
  first_x_assum (qspecl_then [`n7`, `rr`,
                   `Block closure_tag [CodePtr (n7 + (ns + 2 * SUC (LENGTH l))); Number (&(FST x'-1)); RefPtr T rr]::env'`,
                   `t1`,
                   `[Block closure_tag [CodePtr (n7 + (ns + 2 * SUC (LENGTH l))); Number (&(FST x''-1)); RefPtr T rr]] ++ ys`,
                   `c8`,
                    `x`,
                    `x`,
                    `ck`] assume_tac) >>
  rev_full_simp_tac std_ss [ADD_ASSOC] >>
  rw_tac std_ss [ADD_ASSOC] >>
  simp [GENLIST, GSYM ADD1, GSYM SNOC_APPEND, map2_snoc] >>
  simp [SNOC_APPEND, APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``SUC n + 1 = SUC (n+1)``,GENLIST]
  \\ FULL_SIMP_TAC std_ss [ADD1,SNOC_APPEND]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);
  val _ = show_thm "evaluate_recc_Lets_replay=" evaluate_recc_Lets_replay;
  val compile_exps_LIST_IMP_compile_exps_EL_replay = Q.prove (
    `  !exps aux1 c7 aux7 i n8 n4 aux5 num_args e.
      EL i exps = (num_args, e) ∧
      (compile_exps max_app (MAP SND exps) aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        compile_exps max_app [e] aux = ([c],aux1') /\
        lookup (n8 + 2*i) t1.code = SOME (num_args + 1,SND (code_for_recc_case k num_args c)) /\
        code_installed aux1' t1.code`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[SNOC_APPEND,EL_LENGTH_APPEND]
    \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND,compile_exps_SNOC]
    \\ fs[] \\ rpt (pairarg_tac \\ fs[])
    \\ qmatch_assum_rename_tac`_ = (c2,aux3)`
    \\ qmatch_assum_rename_tac`_ = (c1,aux2)`
    \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ full_simp_tac(srw_ss())[]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND, map2_snoc]
    \\ full_simp_tac(srw_ss())[SNOC_APPEND, build_aux_APPEND1]
    \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ IMP_RES_TAC build_aux_LENGTH
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ full_simp_tac(srw_ss())[LENGTH_MAP2]
    \\ Cases_on `code_for_recc_case k num_args d`
    \\ full_simp_tac(srw_ss())[]
    \\ (qspecl_then [`MAP2 (code_for_recc_case k) (MAP FST exps) c1`,`n8`,`aux3`]
           mp_tac build_aux_acc) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[code_for_recc_case_def] )
  \\ `i < LENGTH exps` by DECIDE_TAC
  \\ full_simp_tac(srw_ss())[EL_SNOC]
  \\ full_simp_tac(srw_ss())[MAP_SNOC, compile_exps_SNOC]
  \\ fs[] \\ rpt (pairarg_tac \\ fs[])
  \\ qmatch_assum_rename_tac`_ = (c2,aux3)`
  \\ qmatch_assum_rename_tac`_ = (c1,aux2)`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ imp_res_tac compile_exps_LENGTH
  \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND, map2_snoc]
  \\ full_simp_tac(srw_ss())[SNOC_APPEND, MAP,build_aux_APPEND1]
  \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ NTAC 4 (POP_ASSUM MP_TAC)
  \\ qspecl_then [`max_app`,`[SND x]`,`aux2`] mp_tac compile_exps_acc
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[code_installed_def]);
  val _ = show_thm "compile_exps_LIST_IMP_compile_exps_EL_replay=" compile_exps_LIST_IMP_compile_exps_EL_replay;
end;
(* Replay the original related-variable selection theorems. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory bvlSemTheory bvlPropsTheory listTheory finite_mapTheory
in
  val LESS_LENGTH_env_rel_IMP = Q.prove (
    `  !env env2 n.
      n < LENGTH env /\ env_rel max_app f refs code env env2 ==>
      n < LENGTH env2 /\ v_rel max_app f refs code (EL n env) (EL n env2)`,
  Induct \\ full_simp_tac(srw_ss())[LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]);
  val lookup_vars_IMP2 = Q.prove(
  `!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel max_app f refs code env env2 ==>
      ?ys. (!t1. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1))) /\
           EVERY2 (v_rel max_app f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)`,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def,evaluate_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ full_simp_tac(srw_ss())[])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
  val _ = show_thm "lookup_vars_IMP2_replay=" lookup_vars_IMP2;
  val lookup_vars_IMP_replay = Q.prove (
    `  !vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel max_app f refs code env env2 ==>
      ?ys. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1:('c, 'ffi) bvlSem$state)) /\
           EVERY2 (v_rel max_app f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)`,
  (* TODO: metis_tac is not VALID here *)
    PROVE_TAC[lookup_vars_IMP2]);
  val _ = show_thm "lookup_vars_IMP_replay=" lookup_vars_IMP_replay;
end;
(* Replay the equality-result and closure-test statements. *)
local
  open preamble clos_to_bvlTheory clos_to_bvlProofTheory bvlSemTheory listTheory backend_commonTheory
in
  val _ = show_thm "eq_res_def_typed=" eq_res_def;
  val eq_res_not_timeout_replay = Q.prove (
    `  eq_res x ≠ Rerr (Rabort Rtimeout_error)`,
  Cases_on`x`>>simp[]);
  val _ = show_thm "eq_res_not_timeout_replay=" eq_res_not_timeout_replay;
  val evaluate_check_closure_replay = Q.prove (
    `  n < LENGTH env ∧
   EL n env = bvlSem$Block t vs
   ⇒
   evaluate ([check_closure n e],env,s) =
   if t = closure_tag ∨ t = partial_app_tag then
     (eq_res (Eq_val T),s)
   else
     evaluate ([e],env,s)`,
  srw_tac[][check_closure_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[]);
  val _ = show_thm "evaluate_check_closure_replay=" evaluate_check_closure_replay;
end;
(* Replay finite reference-domain freshness. *)
local
  open preamble clos_to_bvlProofTheory bvlSemTheory finite_mapTheory
in
  val EXISTS_NOT_IN_refs_replay = Q.prove (
    `  ?x. ~(x IN FDOM (t1:('c,'ffi) bvlSem$state).refs)`,
  METIS_TAC [NUM_NOT_IN_FDOM]);
  val _ = show_thm "EXISTS_NOT_IN_refs_replay=" EXISTS_NOT_IN_refs_replay;
end;
(* Replay the generated-variable evaluation theorem. *)
local
  open preamble clos_to_bvlProofTheory bvlPropsTheory bvlSemTheory listTheory
in
  val evaluate_simple_genlist_vars_replay = Q.prove (
    `  !env1 env2 s.
    0 < LENGTH env1
    ⇒
    evaluate (GENLIST Var (LENGTH env1), env1++env2, s) = (Rval env1, s)`,
  srw_tac[][] >>
  qspecl_then [`0`, `env1++env2`, `LENGTH env1`, `s`] assume_tac evaluate_genlist_vars >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [TAKE_LENGTH_APPEND] >>
  metis_tac []);
  val _ = show_thm "evaluate_simple_genlist_vars_replay=" evaluate_simple_genlist_vars_replay;
end;
(* Replay the full application destination theorem, including unused binders. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory listTheory
in
  val dest_closure_full_app_replay = Q.prove (
    `  !loc_opt func args c f1 t1 exp args1 args2.
    dest_closure max_app loc_opt func args = SOME (Full_app exp args1 args2)
    ⇒
    ?rem_args loc num_args old_args cl_env.
      get_loc func = loc ∧
      num_remaining_args func = SOME rem_args ∧
      get_num_args func = SOME num_args ∧
      get_old_args func = SOME old_args ∧
      get_cl_env func = SOME cl_env ∧
      rem_args ≤ LENGTH args ∧
      rem_args ≤ num_args ∧
      num_args ≤ LENGTH old_args + LENGTH args ∧
      LENGTH args2 = LENGTH args - rem_args ∧
      check_loc max_app loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
  srw_tac[][dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[get_cl_env_def, get_old_args_def, get_loc_def, num_remaining_args_def, get_num_args_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][] >>
  TRY (Cases_on `o'`) >>
  full_simp_tac(srw_ss())[get_loc_def] >>
  simp [] >>
  decide_tac);
  val _ = show_thm "dest_closure_full_app_replay=" dest_closure_full_app_replay;
  val dest_closure_part_app_replay = Q.prove (
    `  !loc_opt func args c f1 t1.
    LENGTH args ≠ 0 ∧
    dest_closure max_app loc_opt func args = SOME (Partial_app c)
    ⇒
    loc_opt = NONE ∧
    SOME c = add_args func args ∧
    ?n. num_remaining_args func = SOME n ∧ LENGTH args < n ∧ LENGTH args ≤ max_app`,
  srw_tac[][dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[add_args_def, LET_THM, num_remaining_args_def] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `loc_opt` >>
  full_simp_tac(srw_ss())[check_loc_def] >>
  decide_tac);
  val _ = show_thm "dest_closure_part_app_replay=" dest_closure_part_app_replay;
end;
val _ = show_thm "get_old_args_def_typed=" clos_to_bvlProofTheory.get_old_args_def;
(* Replay the original local closure relation shape theorem. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory bvlSemTheory listTheory backend_commonTheory
in
  val cl_rel_dest_replay = Q.prove (
    `!f refs code cl cl' fvs fvs'.
    cl_rel max_app f refs code (fvs,fvs') cl cl'
    ⇒
    get_old_args cl = SOME [] ∧
    ?l num_args fvs.
      cl' = Block closure_tag (CodePtr l::Number (&num_args)::fvs)`,
  srw_tac[][cl_rel_cases] >>
  srw_tac[][get_old_args_def, EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  srw_tac[][]);
  val _ = show_thm "cl_rel_dest_replay=" cl_rel_dest_replay;
end;
val _ = show_thm "check_loc_prime_def_typed=" clos_to_bvlProofTheory.check_loc'_def;
val _ = show_thm "dest_closure_prime_def_typed=" clos_to_bvlProofTheory.dest_closure'_def;
(* Replay the original local partial-to-full destination theorem. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory
in
  val dest_closure_full_of_part_replay = Q.prove (
    `dest_closure max_app loc func args = SOME (Full_app body newenv rest) ∧
   LENGTH arg_env ≠ 0 ∧
   add_args cl arg_env = SOME func ∧
   get_num_args cl = SOME num_args ∧
   LENGTH arg_env < num_args
   ⇒
   dest_closure' loc cl (args++arg_env) = SOME (Full_app body newenv rest)`,
  srw_tac[][dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[add_args_def, check_loc_def, check_loc'_def, get_num_args_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  TRY decide_tac
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      srw_tac[][TAKE_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      srw_tac[][DROP_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (Cases_on `loc` >> full_simp_tac(srw_ss())[check_loc_def, check_loc'_def])
  >- (full_simp_tac(srw_ss())[LET_THM] >>
      BasicProvers.EVERY_CASE_TAC >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      TRY decide_tac
      >- (Cases_on `loc` >> full_simp_tac(srw_ss())[check_loc_def, check_loc'_def])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          srw_tac[][TAKE_APPEND2] >>
          srw_tac [ARITH_ss] [])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          srw_tac[][DROP_APPEND2] >>
          srw_tac [ARITH_ss] [])));
  val _ = show_thm "dest_closure_full_of_part_replay=" dest_closure_full_of_part_replay;
end;
(* Replay the original bounded-to-unbounded destination lemma. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory
in
  val dest_cl_imp_dest_cl_prime_replay = Q.prove (
    `dest_closure max_app l f a = SOME x ⇒ dest_closure' l f a = SOME x`,
  srw_tac[][dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `l` >>
  full_simp_tac(srw_ss())[check_loc_def, check_loc'_def, LET_THM] >>
  Cases_on `EL n l1` >>
  full_simp_tac(srw_ss())[]);
  val _ = show_thm "dest_cl_imp_dest_cl_prime_replay=" dest_cl_imp_dest_cl_prime_replay;
end;
(* Replay the original local list-relation theorem. *)
local
  open preamble clos_to_bvlProofTheory closSemTheory listTheory
in
  val list_rel_app_replay = Q.prove (
    `!R args args' l0 c l func rem_args.
    dest_closure max_app NONE func args = SOME (Full_app c l l0) ∧
    num_remaining_args func = SOME rem_args ∧
    LIST_REL R args args'
    ⇒
    LIST_REL R l0 (TAKE (LENGTH args' − rem_args) args')`,
  srw_tac[][dest_closure_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, check_loc_def, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [EL_TAKE, EL_REVERSE, EL_DROP, PRE_SUB1]);
  val _ = show_thm "list_rel_app_replay=" list_rel_app_replay;
end;
(* Replay the original local call-environment lemma and its local list prerequisite. *)
local
  open preamble clos_to_bvlTheory bvlSemTheory bvlPropsTheory
  val el_take_append = Q.prove (
    `!n l x l2. n <= LENGTH l ==> EL n (TAKE n l ++ [x] ++ l2) = x`,
    Induct_on `l` >> srw_tac[][] >> ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
    fs[EL_APPEND2,LENGTH_TAKE]);
  val bEval_def = bvlSemTheory.evaluate_def;
  val bEvalOp_def = bvlSemTheory.do_app_def;
  val bEval_APPEND = bvlPropsTheory.evaluate_APPEND;
in
val mk_call_simp2_replay = Q.prove(
  `!n args stuff stuff' v t.
    n ≤ LENGTH args ∧ LENGTH stuff' ≠ 0
    ⇒
    evaluate ([mk_cl_call (Var n) (GENLIST Var n)], (TAKE n args) ++ [v] ++ stuff, t)
    =
    evaluate ([mk_cl_call (Var 0) (GENLIST (\n. Var (n+1)) n)], v::(args++stuff'), t)`,
  strip_tac >>
  simp [mk_cl_call_def, bEval_def, bEvalOp_def, do_int_app_def, el_take_append] >>
  Cases_on `v` >>
  simp [] >>
  srw_tac[][] >>
  TRY (rename [`FLOOKUP t.refs rrr`] \\ Cases_on `FLOOKUP t.refs rrr` \\ fs []
       \\ Cases_on `x`\\ fs [] \\ IF_CASES_TAC \\ fs []) >>
  srw_tac[][] >>
  Cases_on`EL 1 l`>>simp[do_eq_def]>>
  simp[bEval_APPEND] >>
  rename [`TAKE n args ++ [xxx] ++ stuff`] >>
  qspecl_then [`0`, `TAKE n args ++ [xxx] ++ stuff`, `n`]mp_tac evaluate_genlist_vars >>
  qspecl_then [`1`, `xxx::(args ++ stuff')`, `n`]mp_tac evaluate_genlist_vars >>
  srw_tac [ARITH_ss] [ETA_THM, bEval_def, bEvalOp_def, do_int_app_def,el_take_append] >>
  srw_tac[][] >>
  `n+1 ≤ SUC (LENGTH args + LENGTH stuff')` by decide_tac >>
  srw_tac [ARITH_ss] [TAKE_APPEND1, TAKE_TAKE, EL_CONS])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
val _ = show_thm "mk_call_simp2_replay=" mk_call_simp2_replay;
end;
val _ = show_thm "num_remaining_args_def_typed=" clos_to_bvlProofTheory.num_remaining_args_def;
(* Replay the original local no-partial-arguments theorem. *)
local
  open preamble clos_to_bvlProofTheory
in
  val no_partial_args_replay = Q.prove (
    `num_remaining_args func = SOME x /\
     get_num_args func = SOME x /\ x <> 0 /\
     add_args cl arg_env = SOME func ==> arg_env = []`,
    Cases_on `cl` >>
    srw_tac[][add_args_def] >>
    full_simp_tac(srw_ss())[get_num_args_def, num_remaining_args_def] >>
    srw_tac[][] >>
    Cases_on `arg_env` >>
    full_simp_tac(srw_ss())[] >>
    decide_tac);
  val _ = show_thm "no_partial_args_replay=" no_partial_args_replay;
end;
val _ = show_thm "clos_tag_shift_eq_nil_tag_typed=" clos_to_bvlProofTheory.clos_tag_shift_eq_nil_tag;
(* Replay the original local byte-list and optional-decoding theorems. *)
local
  open preamble clos_to_bvlProofTheory backend_commonTheory
in
  val v_rel_IMP_v_to_bytes_lemma_replay = Q.prove (
    `!x y. v_rel max_app f refs code x y ==>
      !ns. (closSem$v_to_list x = SOME (MAP (closSem$Number o $& o (w2n:word8->num)) ns)) <=>
           (bvlSem$v_to_list y = SOME (MAP (bvlSem$Number o $& o (w2n:word8->num)) ns))`,
    ho_match_mp_tac closSemTheory.v_to_list_ind >> rw [] >>
    fs [bvlSemTheory.v_to_list_def,closSemTheory.v_to_list_def,v_rel_SIMP] >>
    Cases_on `tag = cons_tag` >> fs [] >> rveq >> fs [] >>
    res_tac >> fs [bvlPropsTheory.case_eq_thms,v_rel_SIMP] >-
      (Cases_on `ns` >> fs [] >> rveq >> fs [v_rel_SIMP] >> rveq >> fs [] >>
       rw [] >> fs [] >> eq_tac >> rw [] >> fs [v_rel_SIMP]) >>
    Cases_on `ys` >> fs [bvlSemTheory.v_to_list_def]);
  val _ = show_thm "v_rel_IMP_v_to_bytes_lemma_replay=" v_rel_IMP_v_to_bytes_lemma_replay;
  val v_rel_IMP_v_to_bytes_replay = Q.prove (
    `v_rel max_app f refs code x y ==> bvlSem$v_to_bytes y = closSem$v_to_bytes x`,
    rw [bvlSemTheory.v_to_bytes_def,closSemTheory.v_to_bytes_def] >>
    old_drule v_rel_IMP_v_to_bytes_lemma_replay >> fs []);
  val _ = show_thm "v_rel_IMP_v_to_bytes_replay=" v_rel_IMP_v_to_bytes_replay;
  val v_rel_IMP_v_to_words_lemma_replay = Q.prove (
    `!x y. v_rel max_app f refs code x y ==>
      !ns. (closSem$v_to_list x = SOME (MAP closSem$Word64 ns)) <=>
           (bvlSem$v_to_list y = SOME (MAP bvlSem$Word64 ns))`,
    ho_match_mp_tac closSemTheory.v_to_list_ind >> rw [] >>
    fs [bvlSemTheory.v_to_list_def,closSemTheory.v_to_list_def,v_rel_SIMP] >>
    Cases_on `tag = cons_tag` >> fs [] >> rveq >> fs [] >>
    res_tac >> fs [bvlPropsTheory.case_eq_thms,v_rel_SIMP] >-
      (Cases_on `ns` >> fs [] >> rveq >> fs [v_rel_SIMP] >> rveq >> fs [] >>
       rw [] >> fs [] >> eq_tac >> rw [] >> fs [v_rel_SIMP]) >>
    Cases_on `ys` >> fs [bvlSemTheory.v_to_list_def]);
  val _ = show_thm "v_rel_IMP_v_to_words_lemma_replay=" v_rel_IMP_v_to_words_lemma_replay;
  val v_rel_IMP_v_to_words_replay = Q.prove (
    `v_rel max_app f refs code x y ==> bvlSem$v_to_words y = closSem$v_to_words x`,
    rw [bvlSemTheory.v_to_words_def,closSemTheory.v_to_words_def] >>
    old_drule v_rel_IMP_v_to_words_lemma_replay >> fs []);
  val _ = show_thm "v_rel_IMP_v_to_words_replay=" v_rel_IMP_v_to_words_replay;
end;
(* Replay the original local chain-compilation accumulator theorem. *)
local
  open preamble listTheory clos_to_bvlTheory
in
  val compile_exps_chain_exps_cons_replay = Q.prove (
    `!n h t a new_exps aux x6 x7.
      compile_exps max_app (MAP (SND o SND) (chain_exps n (h::t))) a = (new_exps,aux) /\
      compile_exps max_app (h::t) a = (x6,x7) ==> x7 = aux`,
    Induct_on `t` >> fs [chain_exps_def] >> rw [] >> fs [] >>
    ntac 2 (pop_assum mp_tac) >>
    simp [Once compile_exps_CONS] >> fs [compile_exps_def] >>
    rpt (pairarg_tac >> fs []) >> rveq >> fs [] >> rw [] >> res_tac >> fs []);
  val _ = show_thm "compile_exps_chain_exps_cons_replay=" compile_exps_chain_exps_cons_replay;
end;
val _ = show_thm "build_aux_append_aux_typed=" clos_to_bvlProofTheory.build_aux_append_aux;
val _ = show_thm "compile_exps_append_aux_typed=" clos_to_bvlProofTheory.compile_exps_append_aux;
val _ = show_thm "compile_exps_eq_append_typed=" clos_to_bvlProofTheory.compile_exps_eq_append;
val _ = show_thm "SND_SND_known_compile_inc_typed=" clos_to_bvlProofTheory.SND_SND_known_compile_inc;
val _ = show_thm "alist_to_fmap_FEMPTY_typed=" clos_to_bvlProofTheory.alist_to_fmap_FEMPTY;
val _ = show_thm "code_locs_FST_ticks_compile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_ticks_compile_inc;
val _ = show_thm "code_locs_FST_letop_compile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_letop_compile_inc;
val _ = show_thm "ncompile_inc_code_locs_distinct_typed=" clos_to_bvlProofTheory.ncompile_inc_code_locs_distinct;
val _ = show_thm "every_Fn_vs_NONE_ncompile_inc_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_ncompile_inc;
val _ = show_thm "every_Fn_SOME_ncompile_inc_typed=" clos_to_bvlProofTheory.every_Fn_SOME_ncompile_inc;
val _ = show_thm "set_code_locs_collect_apps_typed=" clos_to_bvlProofTheory.set_code_locs_collect_apps;
val _ = show_thm "every_Fn_SOME_collect_apps_typed=" clos_to_bvlProofTheory.every_Fn_SOME_collect_apps;
val _ = show_thm "every_Fn_SOME_intro_multi_typed=" clos_to_bvlProofTheory.every_Fn_SOME_intro_multi;
val _ = show_thm "HD_FST_calls_typed=" clos_to_bvlProofTheory.HD_FST_calls;
val _ = show_thm "elist_globals_sing_typed=" clos_to_bvlProofTheory.elist_globals_sing;
val _ = show_thm "set_globals_HD_intro_multi_typed=" clos_to_bvlProofTheory.set_globals_HD_intro_multi;
val _ = show_thm "set_globals_SND_renumber_code_locs_typed=" clos_to_bvlProofTheory.set_globals_SND_renumber_code_locs;
val _ = show_thm "elist_globals_FLAT_typed=" clos_to_bvlProofTheory.elist_globals_FLAT;
val _ = show_thm "eval_sim_def_typed=" clos_to_bvlProofTheory.eval_sim_def;
val _ = show_thm "IMP_semantics_eq_typed=" clos_to_bvlProofTheory.IMP_semantics_eq;
(* Capture the complete closure initial-state predicate and clock invariance. *)
val _ = show_thm "clos_init_def_typed=" clos_to_bvlProofTheory.clos_init_def;
val _ = show_thm "clos_init_with_clock_typed=" clos_to_bvlProofTheory.clos_init_with_clock;
val FST_EQ_LEMMA_replay = Q.prove (
  `FST x = y <=> ?y1. x = (y,y1)`,
  Cases_on `x` >> fs []);
val _ = show_thm "FST_EQ_LEMMA_replay=" FST_EQ_LEMMA_replay;
(* This closure initial-clock theorem is local in the original script. *)
val initial_state_with_clock_replay = Q.prove (
  `(closSem$initial_state ffi ma code co cc k with clock :=
      (closSem$initial_state ffi ma code co cc k).clock + ck) =
      closSem$initial_state ffi ma code co cc (k + ck)`,
  fs [closSemTheory.initial_state_def]);
val _ = show_thm "initial_state_with_clock_replay=" initial_state_with_clock_replay;
(* The BVL clock theorem is local; replay the original proof and inferred types. *)
val initial_state_with_clock_bvl_replay = Q.prove (
  `(bvlSem$initial_state ffi code co cc k with clock :=
      (bvlSem$initial_state ffi code co cc k).clock + ck) =
      bvlSem$initial_state ffi code co cc (k + ck) /\
   (bvlProps$inc_clock ck (bvlSem$initial_state ffi code co cc k) =
      bvlSem$initial_state ffi code co cc (k + ck))`,
  fs [bvlSemTheory.initial_state_def, bvlPropsTheory.inc_clock_def]);
val _ = show_thm "initial_state_with_clock_bvl_replay=" initial_state_with_clock_bvl_replay;
(* These local declarations are replayed with the proofs from the original script. *)
local
  open preamble clos_to_bvlTheory bvlSemTheory
  val evaluate_init1_replay = Q.prove (
    `∀mapp2 mapp1 tot st.
      (∀n. n < mapp2 ⇒ partial_app_fn_location mapp1 tot n ∈ domain st.code) ⇒
      bvlSem$evaluate (REVERSE
        (GENLIST (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) mapp2), [Unit], st) =
      (Rval (REVERSE (GENLIST (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) mapp2)), st)`,
    Induct >> fs[bvlSemTheory.evaluate_def] >>
    rw[] >> simp[GENLIST,REVERSE_SNOC] >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    simp[bvlPropsTheory.evaluate_APPEND,bvlSemTheory.evaluate_def,do_app_def]);
  val evaluate_init_replay = Q.prove (
    `∀mapp2 mapp1 st.
      (∀m n. m < mapp2 ∧ n < m ⇒ partial_app_fn_location mapp1 m n ∈ domain st.code) ⇒
      bvlSem$evaluate (REVERSE (FLAT (GENLIST (λtot. GENLIST
        (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) tot) mapp2)), [Unit], st) =
      (Rval (REVERSE (FLAT (GENLIST (λtot. GENLIST
        (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) tot) mapp2))), st)`,
    Induct >> fs[bvlSemTheory.evaluate_def] >>
    simp[GENLIST,FLAT_SNOC] >>
    simp[REVERSE_APPEND,bvlPropsTheory.evaluate_APPEND] >>
    rw[] >>
    `∀n. n < mapp2 ⇒ partial_app_fn_location mapp1 mapp2 n ∈ domain st.code` by fs[] >>
    old_drule evaluate_init1_replay >> simp[]);
in
  val _ = show_thm "evaluate_init1_replay=" evaluate_init1_replay;
  val _ = show_thm "evaluate_init_replay=" evaluate_init_replay;
end;
val _ = show_thm "renumber_code_locs_fv1_typed=" clos_to_bvlProofTheory.renumber_code_locs_fv1;
val _ = show_thm "renumber_code_locs_list_fv_typed=" clos_to_bvlProofTheory.renumber_code_locs_list_fv;
val _ = show_thm "collect_apps_fv1_typed=" clos_to_bvlProofTheory.collect_apps_fv1;
val _ = show_thm "collect_args_fv1_typed=" clos_to_bvlProofTheory.collect_args_fv1;
val _ = show_thm "intro_multi_fv1_typed=" clos_to_bvlProofTheory.intro_multi_fv1;
val _ = show_thm "fv_append_typed=" closPropsTheory.fv_append;
val _ = show_thm "compile_every_Fn_SOME_typed=" clos_to_bvlProofTheory.compile_every_Fn_SOME;
val _ = show_thm "calls_preserves_every_Fn_vs_NONE_typed=" clos_callProofTheory.calls_preserves_every_Fn_vs_NONE;
val _ = show_thm "every_Fn_vs_NONE_cond_call_compile_inc_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_cond_call_compile_inc;
val _ = show_thm "cl_rel_subspt_typed=" clos_to_bvlProofTheory.cl_rel_subspt;
val _ = show_thm "v_rel_subspt_typed=" clos_to_bvlProofTheory.v_rel_subspt;
val _ = show_thm "env_rel_subspt_typed=" clos_to_bvlProofTheory.env_rel_subspt;
val _ = show_thm "every_Fn_vs_NONE_known_co_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_known_co;
val _ = show_thm "every_Fn_SOME_known_co_typed=" clos_to_bvlProofTheory.every_Fn_SOME_known_co;
val _ = show_thm "renumber_code_locs_list_csyntax_ok_typed=" clos_to_bvlProofTheory.renumber_code_locs_list_csyntax_ok;
val _ = show_thm "compile_every_Fn_vs_NONE_typed=" clos_to_bvlProofTheory.compile_every_Fn_vs_NONE;
val _ = show_thm "calls_compile_csyntax_ok_typed=" clos_to_bvlProofTheory.calls_compile_csyntax_ok;
val _ = show_thm "kcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.kcompile_inc_uncurry;
val _ = show_thm "code_locs_FST_SND_kcompile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_SND_kcompile_inc;
val _ = show_thm "compile_code_locs_ALL_DISTINCT_typed=" clos_to_bvlProofTheory.compile_code_locs_ALL_DISTINCT;
val _ = show_thm "recclosure_rel_def_typed=" clos_callProofTheory.recclosure_rel_def;
val _ = show_thm "clos_call_wfv_def_typed=" clos_callProofTheory.wfv_def;
val _ = show_thm "clos_call_every_refv_def_typed=" clos_callProofTheory.every_refv_def;
val _ = show_thm "clos_call_every_refv_mono_typed=" clos_callProofTheory.every_refv_mono;
val _ = show_thm "clos_call_wfv_state_def_typed=" clos_callProofTheory.wfv_state_def;
val _ = show_thm "clos_call_wfv_subg_typed=" clos_callProofTheory.wfv_subg;
val _ = show_thm "clos_call_wfv_SUBMAP_typed=" clos_callProofTheory.wfv_SUBMAP;
val _ = show_thm "clos_call_EVERY_wfv_SUBMAP_typed=" clos_callProofTheory.EVERY_wfv_SUBMAP;
val _ = show_thm "clos_call_EVERY_wfv_subg_typed=" clos_callProofTheory.EVERY_wfv_subg;
val _ = show_thm "clos_call_wfv_state_subg_typed=" clos_callProofTheory.wfv_state_subg;
val _ = show_thm "clos_call_wfv_state_SUBMAP_typed=" clos_callProofTheory.wfv_state_SUBMAP;
val _ = show_thm "clos_call_code_includes_subg_typed=" clos_callProofTheory.code_includes_subg;
val _ = show_thm "clos_call_code_includes_ALOOKUP_typed=" clos_callProofTheory.code_includes_ALOOKUP;
val _ = show_thm "clos_call_v_rel_def_typed=" clos_callProofTheory.v_rel_def;
val _ = show_thm "clos_call_v_rel_subg_typed=" clos_callProofTheory.v_rel_subg;
val _ = show_thm "clos_call_v_rel_SUBMAP_typed=" clos_callProofTheory.v_rel_SUBMAP;
val _ = show_thm "clos_call_v_rel_SUBMAP_subg_typed=" clos_callProofTheory.v_rel_SUBMAP_subg;
val _ = show_thm "clos_call_LIST_REL_v_rel_SUBMAP_typed=" clos_callProofTheory.LIST_REL_v_rel_SUBMAP;
val _ = show_thm "clos_call_LIST_REL_v_rel_subg_typed=" clos_callProofTheory.LIST_REL_v_rel_subg;
val _ = show_thm "clos_call_env_rel_SUBMAP_typed=" clos_callProofTheory.env_rel_SUBMAP;
val _ = show_thm "clos_call_env_rel_subg_typed=" clos_callProofTheory.env_rel_subg;
val _ = show_thm "clos_call_v_rel_Unit_typed=" clos_callProofTheory.v_rel_Unit;
val _ = show_thm "clos_call_v_to_list_thm_typed=" clos_callProofTheory.v_to_list_thm;
val _ = show_thm "clos_call_v_to_bytes_thm_typed=" clos_callProofTheory.v_to_bytes_thm;
val _ = show_thm "clos_call_v_to_words_thm_typed=" clos_callProofTheory.v_to_words_thm;
val _ = show_thm "clos_call_v_to_list_wfv_typed=" clos_callProofTheory.v_to_list_wfv;
val _ = show_thm "clos_call_wfv_Boolv_typed=" clos_callProofTheory.wfv_Boolv;
val _ = show_thm "clos_call_vrel_v2l_l2v_typed=" clos_callProofTheory.vrel_v2l_l2v;
val _ = show_thm "clos_call_wfv_v2l_l2v_typed=" clos_callProofTheory.wfv_v2l_l2v;
val _ = show_thm "clos_call_vrel_list_to_v_typed=" clos_callProofTheory.vrel_list_to_v;
val _ = show_thm "clos_call_wfv_v2l_typed=" clos_callProofTheory.wfv_v2l;
val _ = show_thm "clos_call_do_app_thm_typed=" clos_callProofTheory.do_app_thm;
val _ = show_thm "clos_call_domain_FST_insert_each_typed=" clos_callProofTheory.domain_FST_insert_each;
val _ = show_thm "clos_call_SND_insert_each_typed=" clos_callProofTheory.SND_insert_each;
val _ = show_thm "clos_call_FST_insert_each_same_typed=" clos_callProofTheory.FST_insert_each_same;
val _ = show_thm "clos_call_insert_each_pair_arg_typed=" clos_callProofTheory.insert_each_pair_arg;
val _ = show_thm "clos_call_insert_each_subspt_typed=" clos_callProofTheory.insert_each_subspt;
val _ = show_thm "clos_call_calls_subspt_typed=" clos_callProofTheory.calls_subspt;
val _ = show_thm "clos_call_calls_IS_SUFFIX_typed=" clos_callProofTheory.calls_IS_SUFFIX;
val _ = show_thm "clos_call_calls_subg_typed=" clos_callProofTheory.calls_subg;
val _ = show_thm "clos_call_calls_domain_locs_typed=" clos_callProofTheory.calls_domain_locs;
val _ = show_thm "clos_call_NOT_IN_domain_FST_g_typed=" clos_callProofTheory.NOT_IN_domain_FST_g;
val _ = show_thm "clos_call_wfg_insert_each_typed=" clos_callProofTheory.wfg'_insert_each;
val _ = show_thm "clos_call_v_rel_Boolv_typed=" clos_callProofTheory.v_rel_Boolv;
val _ = show_thm "clos_call_make_g_def_typed=" clos_callProofTheory.make_g_def;
val _ = show_thm "clos_call_make_g_wfg_typed=" clos_callProofTheory.make_g_wfg;
val _ = show_thm "clos_call_co_ok_def_typed=" clos_callProofTheory.co_ok_def;
val _ = show_thm "clos_call_co_ok_IMP_full_gs_eq_shift_seq_typed=" clos_callProofTheory.co_ok_IMP_full_gs_eq_shift_seq;
val _ = show_thm "clos_call_co_ok_IMP_wfg_full_gs_typed=" clos_callProofTheory.co_ok_IMP_wfg_full_gs;
val _ = show_thm "clos_call_co_ok_IMP_make_g_typed=" clos_callProofTheory.co_ok_IMP_make_g;
val _ = show_thm "clos_call_code_inv_def_typed=" clos_callProofTheory.code_inv_def;
val _ = show_thm "clos_call_code_inv_k_typed=" clos_callProofTheory.code_inv_k;
val _ = show_thm "clos_call_SUBMAP_FUPDATE_LIST_typed=" clos_callProofTheory.SUBMAP_FUPDATE_LIST;
val _ = show_thm "clos_call_includes_state_def_typed=" clos_callProofTheory.includes_state_def;
val _ = show_thm "clos_call_includes_state_EX_typed=" clos_callProofTheory.includes_state_EX;
(* This theorem is local in HOL; replay its statement and proof to retain inferred types. *)
val clos_call_env_rel_Op_Install_replay = Q.prove (
  `clos_callProof$env_rel r env env2 0 [(0, closLang$Op v6 closLang$Install e1)] <=>
   clos_callProof$env_rel r env env2 0 (MAP (λx. (0,x)) e1)`,
  fs [clos_callProofTheory.env_rel_def] >> rw [] >> fs [closPropsTheory.fv1_thm, listTheory.EXISTS_MAP]
  >> qsuff_tac `!x. EXISTS (λx'. closProps$fv1 x x') e1 = closProps$fv x e1` >> fs []
  >> Induct_on `e1` >> fs []);
val _ = show_thm "clos_call_env_rel_Op_Install_replay=" clos_call_env_rel_Op_Install_replay;
val _ = show_thm "clos_call_state_rel_def_typed=" clos_callProofTheory.state_rel_def;
val _ = show_thm "clos_call_state_rel_max_app_typed=" clos_callProofTheory.state_rel_max_app;
val _ = show_thm "clos_call_state_rel_clock_typed=" clos_callProofTheory.state_rel_clock;
val _ = show_thm "clos_call_state_rel_with_clock_typed=" clos_callProofTheory.state_rel_with_clock;
val _ = show_thm "clos_call_state_rel_flookup_refs_typed=" clos_callProofTheory.state_rel_flookup_refs;
val _ = show_thm "oracle_monotonic_init_subset_typed=" clos_to_bvlProofTheory.oracle_monotonic_init_subset;
val _ = show_thm "DISJOINT_LE_GT_typed=" clos_to_bvlProofTheory.DISJOINT_LE_GT;
val _ = show_thm "cond_mti_monotonic_elist_globals_typed=" clos_to_bvlProofTheory.cond_mti_monotonic_elist_globals;
val _ = show_thm "number_compile_inc_esgc_free_typed=" clos_to_bvlProofTheory.number_compile_inc_esgc_free;
val _ = show_thm "number_monotonic_elist_globals_typed=" clos_to_bvlProofTheory.number_monotonic_elist_globals;
val _ = show_thm "chain_exps_GT_typed=" clos_to_bvlProofTheory.chain_exps_GT;
val _ = show_thm "chain_exps_LE_typed=" clos_to_bvlProofTheory.chain_exps_LE;
val _ = show_thm "chain_exps_ALL_DISTINCT_typed=" clos_to_bvlProofTheory.chain_exps_ALL_DISTINCT;
val _ = show_thm "every_Fn_vs_SOME_def_typed=" closPropsTheory.every_Fn_vs_SOME_def;
val _ = show_thm "num_stubs_def_typed=" clos_to_bvlTheory.num_stubs_def;
val _ = show_thm "compile_prog_code_locs_typed=" clos_to_bvlProofTheory.compile_prog_code_locs;
val _ = show_thm "compile_exps_code_locs_typed=" clos_to_bvlProofTheory.compile_exps_code_locs;
val _ = show_thm "chain_exps_every_Fn_SOME_typed=" clos_to_bvlProofTheory.chain_exps_every_Fn_SOME;
(* The earlier theorem shares a HOL name with the later implication. *)
val chain_exps_every_Fn_SOME_8596_replay = Q.prove (
  `!x y. closProps$every_Fn_SOME (MAP (SND o SND) (clos_to_bvl$chain_exps x y)) <=> closProps$every_Fn_SOME y`,
  recInduct clos_to_bvlTheory.chain_exps_ind
  >> rw [clos_to_bvlTheory.chain_exps_def]
  >> pop_assum mp_tac
  >> once_rewrite_tac [rich_listTheory.CONS_APPEND]
  >> fs [closPropsTheory.every_Fn_SOME_APPEND]);
val _ = show_thm "chain_exps_every_Fn_SOME_8596_replay=" chain_exps_every_Fn_SOME_8596_replay;
val _ = show_thm "chain_exps_every_Fn_vs_SOME_typed=" clos_to_bvlProofTheory.chain_exps_every_Fn_vs_SOME;
val _ = show_thm "chain_exps_obeys_max_app_typed=" clos_to_bvlProofTheory.chain_exps_obeys_max_app;
val _ = show_thm "chain_exps_no_Labels_typed=" clos_to_bvlProofTheory.chain_exps_no_Labels;
