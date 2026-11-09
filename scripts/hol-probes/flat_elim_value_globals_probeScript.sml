load "flat_elimProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "pure_every_eta=" flat_elimProofTheory.is_pure_EVERY_aconv;
val _ = show_thm "value_globals=" flat_elimProofTheory.find_v_globals_def;
val _ = show_thm "refs_globals=" flat_elimProofTheory.find_refs_globals_def;
val _ = show_thm "lookups_append=" flat_elimProofTheory.find_lookupsL_APPEND;
val _ = show_thm "value_globals_append=" flat_elimProofTheory.find_v_globalsL_APPEND;
val _ = show_thm "refs_globals_append=" flat_elimProofTheory.find_refs_globals_APPEND;
val _ = show_thm "lookups_reverse=" flat_elimProofTheory.find_lookupsL_REVERSE;
val _ = show_thm "value_globals_reverse=" flat_elimProofTheory.find_v_globalsL_REVERSE;
val _ = show_thm "value_globals_el=" flat_elimProofTheory.find_v_globalsL_EL;
val _ = show_thm "refs_globals_el=" flat_elimProofTheory.find_refs_globals_EL;
val _ = show_thm "env_globals=" flat_elimProofTheory.find_env_globals_def;
val _ = show_thm "result_globals=" flat_elimProofTheory.find_result_globals_def;
val _ = show_thm "primitive_result_globals=" flat_elimProofTheory.find_sem_prim_res_globals_def;
val _ = show_thm "value_has_eval=" flat_elimProofTheory.v_has_Eval_def1;
val _ = show_thm "globals_relation=" flat_elimProofTheory.globals_rel_def;
val _ = show_thm "globals_transitivity=" flat_elimProofTheory.globals_rel_trans;
val _ = show_thm "declarations_closed=" flat_elimProofTheory.decs_closed_def;
val _ = show_thm "closed_tail=" flat_elimProofTheory.decs_closed_reduce;
val _ = show_thm "closed_head=" flat_elimProofTheory.decs_closed_reduce_HD;
val _ = show_thm "state_relation=" flat_elimProofTheory.flat_state_rel_def;
val _ = show_thm "state_transitivity=" flat_elimProofTheory.flat_state_rel_trans;
val _ = show_thm "state_pmatch=" flat_elimProofTheory.flat_state_rel_pmatch;
val _ = show_thm "state_pmatch_rows=" flat_elimProofTheory.flat_state_rel_pmatch_rows;
val _ = show_thm "selected_row_lookups=" flat_elimProofTheory.pmatch_rows_find_lookups;
val _ = show_thm "value_to_list_globals=" flat_elimProofTheory.find_v_globals_v_to_list;
val _ = show_thm "list_to_value_globals=" flat_elimProofTheory.find_v_globals_list_to_v;
val _ = show_thm "list_append_globals=" flat_elimProofTheory.find_v_globals_list_to_v_APPEND;
val _ = show_thm "list_to_value_eval=" flat_elimProofTheory.v_has_Eval_list_to_v;
val _ = show_thm "value_to_list_eval=" flat_elimProofTheory.v_has_Eval_v_to_list;
val _ = show_thm "evaluation_length=" flatPropsTheory.evaluate_length;
val _ = show_thm "evaluation_singleton=" flatPropsTheory.evaluate_sing;
val _ = show_thm "evaluation_simulation=" flat_elimProofTheory.evaluate_keep_flat_state_rel_eq_lemma;
val _ = show_thm "singleton_evaluation_simulation=" flat_elimProofTheory.evaluate_sing_keep_flat_state_rel_eq;
val _ = show_thm "declaration_evaluation_simulation=" flat_elimProofTheory.evaluate_dec_flat_state_rel;
val _ = show_thm "total_pattern_no_match=" flat_elimProofTheory.total_pat_IMP;
val _ = show_thm "row_total_pattern_no_match=" flat_elimProofTheory.EXISTS_total_pat;
val _ = show_thm "pure_evaluation_simulation=" flat_elimProofTheory.evaluate_flat_state_rel_lemma;
val _ = show_thm "discarded_singleton=" flat_elimProofTheory.evaluate_sing_notKeep_flat_state_rel;
val _ = show_thm "declaration_removal=" flat_elimProofTheory.flat_decs_removal_lemma;
val _ = show_thm "initial_state_removal=" flat_elimProofTheory.flat_removal_thm;
val _ = show_thm "flat_eval_sim_definition=" flatPropsTheory.eval_sim_def;
val _ = show_thm "flat_remove_eval_sim=" flat_elimProofTheory.flat_remove_eval_sim;
val _ = show_thm "flat_remove_semantics=" flat_elimProofTheory.flat_remove_semantics;
val _ = show_thm "global_bag_operator=" flatPropsTheory.op_gbag_def;
val _ = show_thm "global_bag_expressions=" flatPropsTheory.set_globals_def;
val _ = show_thm "global_closure_free=" flatPropsTheory.esgc_free_def;
val _ = show_thm "removed_global_bag_empty=" flat_elimProofTheory.remove_flat_prog_elist_globals_eq_empty;
val _ = show_thm "removed_global_closure_free=" flat_elimProofTheory.remove_flat_prog_esgc_free;
val _ = show_thm "removed_global_sub_bag=" flat_elimProofTheory.remove_flat_prog_sub_bag;
val _ = show_thm "removed_global_distinct=" flat_elimProofTheory.remove_flat_prog_distinct_globals;
val _ = show_thm "primitive_simulation=" flat_elimProofTheory.do_app_SOME_flat_state_rel;
val _ = show_thm "result_values=" flatPropsTheory.result_vs_def;
val _ = show_thm "refs_update_reachable=" flat_elimProofTheory.find_refs_globals_LUPDATE;
val _ = show_thm "pmatch_reachable=" flat_elimProofTheory.pmatch_Match_reachable;
val _ = show_thm "pmatch_no_eval=" flat_elimProofTheory.pmatch_not_has_Eval;
val _ = show_eval "closure_lookup=" ``sptree$lookup 3 (flat_elimProof$find_v_globals (flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$GlobalVarLookup 3) [])))``;
val _ = show_eval "tuple_lookup=" ``sptree$lookup 3 (flat_elimProof$find_v_globals (flatSem$Conv NONE [flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$GlobalVarLookup 3) [])]))``;
val _ = show_eval "closure_eval=" ``flat_elimProof$v_has_Eval (flatSem$Closure <|v := []|> «x» (flatLang$App backend_common$None (flatLang$Src ast$Eval) []))``;
val _ = show_thm "refs_globals_mem_typed=" flat_elimProofTheory.find_refs_globals_MEM;
val _ = show_thm "lookups_list_mem_typed=" flat_elimProofTheory.find_lookupsL_MEM;
(* This theorem is local in HOL, so replay its original proof. *)
val filter_sub_bag_replay = prove (
  ``flatProps$elist_globals (FILTER P ds) <= flatProps$elist_globals ds``,
  Induct_on `ds` \\ rw [] \\ fs [bagTheory.SUB_BAG_UNION]);
val _ = show_thm "filter_sub_bag_typed=" filter_sub_bag_replay;
val filter_empty_replay = prove (
  ``flatProps$elist_globals ds = {||} ==>
    flatProps$elist_globals (FILTER P ds) = {||}``,
  Induct_on `ds` \\ rw [] \\ fs [bagTheory.SUB_BAG_UNION]);
val _ = show_thm "filter_empty_typed=" filter_empty_replay;
val esgc_free_filter_replay = prove (
  ``EVERY flatProps$esgc_free ds ==> EVERY flatProps$esgc_free (FILTER P ds)``,
  Induct_on `ds` \\ rw []);
val _ = show_thm "esgc_free_filter_typed=" esgc_free_filter_replay;

(* Replay the local has_Eval_def theorem from flat_elimProofScript.sml. *)
open flatLangTheory flat_elimTheory;
val has_eval_cases_replay = prove (
  ``(has_Eval (Handle htrace e pes) = (has_Eval e \/ EXISTS has_Eval (MAP SND pes))) /\
    (has_Eval (Con ctrace c es) = EXISTS has_Eval es) /\
    (has_Eval (Fun ftrace farg e) = has_Eval e) /\
    (has_Eval (App t op es) = (op = Src Eval \/ EXISTS has_Eval es)) /\
    (has_Eval (If t e1 e2 e3) = (has_Eval e1 \/ has_Eval e2 \/ has_Eval e3)) /\
    (has_Eval (Mat t e pes) = (has_Eval e \/ EXISTS has_Eval (MAP SND pes))) /\
    (has_Eval (Let ltrace opt e1 e2) = (has_Eval e1 \/ has_Eval e2)) /\
    (has_Eval (Letrec rtrace funs e) = (has_Eval e \/ EXISTS has_Eval (MAP (SND o SND) funs))) /\
    (has_Eval (Raise xtrace e) = has_Eval e) /\
    (has_Eval (Var_local vtrace varnum) = F) /\
    (has_Eval (Lit littrace v) = F)``,
  `!es. has_Eval_list es <=> EXISTS has_Eval es` by
     (Induct >> fs [flat_elimTheory.has_Eval_def]) >>
  `!pes. has_Eval_pats pes <=> EXISTS has_Eval (MAP SND pes)` by
     (Induct >> fs [flat_elimTheory.has_Eval_def, pairTheory.FORALL_PROD]) >>
  `!pes. has_Eval_funs pes <=> EXISTS has_Eval (MAP (SND o SND) pes)` by
     (Induct >> fs [flat_elimTheory.has_Eval_def, pairTheory.FORALL_PROD]) >>
  rw [] >> simp [Once flat_elimTheory.has_Eval_def]);
val _ = show_thm "has_eval_cases_typed=" has_eval_cases_replay;

(* Replay the local fvg_v_to_flat theorem from flat_elimProofScript.sml. *)
load "preamble";
open preamble flatSemTheory flat_elimProofTheory;
val fvg_v_to_flat_replay = prove (
  ``sptree$domain (find_v_globals (v_to_flat v)) SUBSET sptree$domain reachable /\
    ~v_has_Eval (v_to_flat v)``,
  Cases_on `v`
  >> simp [v_to_flat_def, find_v_globals_def, v_has_Eval_def,
           semanticPrimitivesTheory.Boolv_def, Boolv_def]
  >> every_case_tac
  >> simp [find_v_globals_def, v_has_Eval_def, Boolv_def]);
val _ = show_thm "fvg_v_to_flat_typed=" fvg_v_to_flat_replay;

(* Replay the local pair lemmas used in the do_app_cases conversion. *)
val pair_case_eq_replay = prove (
  ``pair_CASE x f = v <=> ?x1 x2. x = (x1,x2) /\ f x1 x2 = v``,
  Cases_on `x` >> srw_tac[][]);
val _ = show_thm "pair_case_eq_typed=" pair_case_eq_replay;
val pair_lam_lem_replay = prove (
  ``!f v z. (let (x,y) = z in f x y) = v <=> ?x1 x2. z = (x1,x2) /\ f x1 x2 = v``,
  srw_tac[][]);
val _ = show_thm "pair_lam_lem_typed=" pair_lam_lem_replay;

(* Replay the local list-index theorem used by the elimination proof. *)
val el_rep_none_some_replay = prove (
  ``n < LENGTH xs + i ==>
    (EL n (xs ++ REPLICATE i NONE) = SOME y <=>
      n < LENGTH xs /\ EL n xs = SOME y)``,
  rw [EL_APPEND_EQN] >> simp [EL_REPLICATE]);
val _ = show_thm "el_rep_none_some_typed=" el_rep_none_some_replay;
val _ = show_thm "flat_do_app_cases_typed=" flat_elimProofTheory.do_app_cases;

(* Replay the local natural-order fact used in do_app_SOME_flat_state_rel. *)
val not_le_less_replay = prove (``(~(x >= y)) ==> ((x :num) < y)``, simp []);
val _ = show_thm "not_le_less_typed=" not_le_less_replay;

(* Replay the local character-list dependency theorem. *)
val fvg_map_char_empty_replay = prove (
  ``find_v_globals (list_to_v (MAP (\c. Litv (Char c)) ss)) = LN``,
  Induct_on `ss` >> simp [find_v_globals_def, list_to_v_def]);
val _ = show_thm "fvg_map_char_empty_typed=" fvg_map_char_empty_replay;

(* Replay the local Eval-free list indexing theorem. *)
val not_v_has_eval_every_el_replay = prove (
  ``EVERY ($~ o v_has_Eval) xs /\ i < LENGTH xs ==> ~v_has_Eval (EL i xs)``,
  simp [EVERY_EL]);
val _ = show_thm "not_v_has_eval_every_el_typed=" not_v_has_eval_every_el_replay;
val _ = show_thm "every_el_imp_typed=" flat_elimProofTheory.EVERY_EL_IMP;
val _ = show_thm "find_v_globals_unit_typed=" flat_elimProofTheory.find_v_globals_Unitv;
(* The original ML binding is not exported, so replay its EVAL. *)
val v_has_eval_unit_replay = EVAL ``v_has_Eval Unitv``;
val _ = show_thm "v_has_eval_unit_typed=" v_has_eval_unit_replay;
val _ = show_thm "v_has_eval_def_typed=" flat_elimProofTheory.v_has_Eval_def;
val _ = show_thm "find_v_globals_list_update_typed=" flat_elimProofTheory.find_v_globalsL_LUPDATE;
val _ = show_thm "find_v_globals_list_replicate_typed=" flat_elimProofTheory.find_v_globalsL_REPLICATE;
val _ = show_thm "find_v_globals_map_recclosure_typed=" flat_elimProofTheory.find_v_globals_MAP_Recclosure;

(* Replay the local transitive list-index dependency theorem. *)
val find_v_globals_el_trans_replay = prove (
  ``n < LENGTH vs /\ domain (find_v_globalsL vs) SUBSET R ==>
    domain (find_v_globals (EL n vs)) SUBSET R``,
  metis_tac [find_v_globalsL_EL, SUBSET_TRANS]);
val _ = show_thm "find_v_globals_el_trans_typed=" find_v_globals_el_trans_replay;
val _ = show_thm "find_v_globals_list_mem_typed=" flat_elimProofTheory.find_v_globalsL_MEM;
val _ = show_thm "find_loc_every_empty_typed=" flat_elimProofTheory.find_loc_EVERY_isEmpty;
val _ = show_thm "sum_map_v3_size_typed=" flat_elimProofTheory.SUM_MAP_v3_size;
val _ = show_thm "flat_value_size_def_typed=" flatSemTheory.v_size_def;
val _ = show_thm "mlstring_size_def_typed=" mlstringTheory.mlstring_size_def;
val _ = show_thm "hol_char_size_def_typed=" stringTheory.char_size_def;
val _ = show_thm "ast_lit_size_def_typed=" astTheory.lit_size_def;
val _ = show_thm "ast_op_size_def_typed=" astTheory.op_size_def;
val _ = show_thm "flat_exp_size_def_typed=" flatLangTheory.exp_size_def;
val _ = show_thm "flat_pat_size_def_typed=" flatLangTheory.pat_size_def;
val _ = show_eval "ast_lit_size_negative_int=" ``ast$lit_size (ast$IntLit (~42))``;
val _ = show_eval "ast_lit_size_char=" ``ast$lit_size (ast$Char (CHR 255))``;
val _ = show_eval "ast_lit_size_string=" ``ast$lit_size (ast$StrLit (mlstring$implode [CHR 65; CHR 0; CHR 255]))``;
val _ = show_eval "ast_lit_size_word8=" ``ast$lit_size (ast$Word8 (255w :word8))``;
val _ = show_eval "ast_lit_size_word64=" ``ast$lit_size (ast$Word64 (4294967297w :word64))``;
val _ = show_eval "ast_lit_size_float64=" ``ast$lit_size (ast$Float64 (9223372036854775808w :word64))``;
val _ = show_thm "ast_shift_size_def_typed=" astTheory.shift_size_def;
val _ = show_thm "ast_arith_size_def_typed=" astTheory.arith_size_def;
val _ = show_thm "ast_word_size_size_def_typed=" astTheory.word_size_size_def;
val _ = show_thm "ast_thunk_mode_size_def_typed=" astTheory.thunk_mode_size_def;
val _ = show_thm "ast_thunk_op_size_def_typed=" astTheory.thunk_op_size_def;
val _ = show_thm "ast_opb_size_def_typed=" astTheory.opb_size_def;
val _ = show_thm "ast_test_size_def_typed=" astTheory.test_size_def;
val _ = show_thm "ast_prim_type_size_def_typed=" astTheory.prim_type_size_def;
val _ = show_eval "ast_op_size_arith=" ``ast$op_size (ast$Arith ast$Add (ast$WordT ast$W8))``;
val _ = show_eval "ast_op_size_from_to=" ``ast$op_size (ast$FromTo (ast$WordT ast$W8) (ast$WordT ast$W64))``;
val _ = show_eval "ast_op_size_shift=" ``ast$op_size (ast$Shift ast$W64 ast$Ror 42)``;
val _ = show_eval "ast_op_size_test=" ``ast$op_size (ast$Test (ast$Compare ast$Lt) (ast$WordT ast$W64))``;
val _ = show_eval "ast_op_size_thunk=" ``ast$op_size (ast$ThunkOp (ast$AllocThunk ast$Evaluated))``;
val _ = show_eval "ast_op_size_ffi=" ``ast$op_size (ast$FFI (mlstring$implode [CHR 65; CHR 0; CHR 255]))``;
val _ = show_eval "ast_op_size_nullary=" ``ast$op_size ast$Eval``;
val _ = show_thm "flat_op_size_def_typed=" flatLangTheory.op_size_def;
val _ = show_thm "backend_tra_size_def_typed=" backend_commonTheory.tra_size_def;
val _ = show_eval "flat_op_size_src=" ``flatLang$op_size (flatLang$Src (ast$Shift ast$W64 ast$Ror 42))``;
val _ = show_eval "flat_op_size_tag=" ``flatLang$op_size (flatLang$TagLenEq 3 5)``;
val _ = show_eval "flat_op_size_id=" ``flatLang$op_size flatLang$Id``;
val _ = show_eval "backend_tra_size_nested=" ``backend_common$tra_size (backend_common$Union (backend_common$SourceLoc 1 2 3 4) (backend_common$Cons backend_common$None 5))``;
val _ = show_thm "option_size_def_typed=" basicSizeTheory.option_size_def;
val _ = show_thm "pair_size_def_typed=" basicSizeTheory.pair_size_def;
val _ = show_eval "flat_pat_size_nested=" ``flatLang$pat_size (flatLang$Pcon (SOME (2,SOME (3,[(4,5)]))) [flatLang$Pany; flatLang$Plit (ast$IntLit (~2))])``;
val _ = show_eval "flat_exp_size_letrec=" ``flatLang$exp_size (flatLang$Letrec (mlstring$implode [CHR 102]) [(mlstring$implode [CHR 103], mlstring$implode [CHR 120], flatLang$Lit backend_common$None (ast$IntLit 4))] (flatLang$App backend_common$None (flatLang$Src ast$Eval) [flatLang$Lit backend_common$None (ast$IntLit 2)]))``;
val _ = show_eval "flat_exp_size_branch=" ``flatLang$exp_size (flatLang$Handle (backend_common$Cons backend_common$None 2) (flatLang$Raise backend_common$None (flatLang$Lit backend_common$None (ast$Char (CHR 65)))) [(flatLang$Pref flatLang$Pany, flatLang$Con backend_common$None (SOME (2,SOME 3)) [])])``;
val _ = show_eval "flat_exp_size_binding=" ``flatLang$exp_size (flatLang$Let backend_common$None (SOME (mlstring$implode [CHR 120])) (flatLang$Var_local backend_common$None (mlstring$implode [CHR 120])) (flatLang$If backend_common$None (flatLang$Lit backend_common$None (ast$IntLit 1)) (flatLang$Fun (mlstring$implode []) (mlstring$implode [CHR 121]) (flatLang$Lit backend_common$None (ast$IntLit 2))) (flatLang$Mat backend_common$None (flatLang$Lit backend_common$None (ast$IntLit 3)) [(flatLang$Pany, flatLang$Lit backend_common$None (ast$IntLit 4))])))``;
val _ = show_thm "bool_size_def_typed=" basicSizeTheory.bool_size_def;
val _ = show_thm "flat_environment_size_def_typed=" flatSemTheory.environment_size_def;
fun show_flat_value_size label tm =
  let val th = (REWRITE_CONV [flatSemTheory.v_size_def] THENC EVAL) tm
  in print label; print_term (rhs (concl th)); print "\n" end;
val _ = show_flat_value_size "flat_value_size_closure=" ``flatSem$v_size (flatSem$Closure <|v := [(mlstring$implode [CHR 97],flatSem$Litv (ast$IntLit 2))]|> (mlstring$implode [CHR 120]) (flatLang$Lit backend_common$None (ast$IntLit 4)))``;
val _ = show_flat_value_size "flat_value_size_recclosure=" ``flatSem$v_size (flatSem$Recclosure <|v := []|> [(mlstring$implode [CHR 102],mlstring$implode [CHR 120],flatLang$Lit backend_common$None (ast$IntLit 1))] (mlstring$implode [CHR 102]))``;
val _ = show_eval "flat_value_size_vector=" ``flatSem$v_size (flatSem$Vectorv [flatSem$Conv (SOME (2,SOME 3)) [flatSem$Loc T 4]])``;
