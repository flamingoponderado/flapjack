load "flat_patternProofTheory";
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "no_mat_decode_pos=" flat_patternProofTheory.decode_pos_no_Mat;
val _ = show_thm "no_mat_decode_test=" flat_patternProofTheory.decode_test_no_Mat;
val _ = show_thm "no_mat_decode_guard=" flat_patternProofTheory.decode_guard_no_Mat;
val _ = show_thm "no_mat_compile_bindings=" flat_patternProofTheory.compile_pat_bindings_no_Mat;
val _ = show_thm "no_mat_naive_match=" flat_patternProofTheory.naive_pattern_match_no_Mat;
val _ = show_thm "no_mat_naive_matches=" flat_patternProofTheory.naive_pattern_matches_no_Mat;
val _ = show_thm "no_mat_compile_pats=" flat_patternProofTheory.compile_pats_no_Mat;
val _ = show_thm "globals_decode_dtree=" flat_patternProofTheory.set_globals_decode_dtree_empty;
val _ = show_thm "set_toList_fromList=" flat_patternProofTheory.set_toList_fromList;
val _ = show_thm "no_mat_decode_dtree=" flat_patternProofTheory.decode_dtree_no_Mat;
val _ = show_thm "esgc_decode_dtree=" flat_patternProofTheory.esgc_free_decode_dtree;
val _ = show_thm "operator_global_flag=" flat_patternProofTheory.op_sets_globals_gbag;
val _ = show_thm "operator_sets_globals_def=" flat_patternTheory.op_sets_globals_def;
val singleton_global_bag = prove (
  ``!n:num. flatProps$op_gbag (flatLang$GlobalVarInit n) =
      (\x. if x = n then 1 else 0)``,
  simp [flatPropsTheory.op_gbag_def, bagTheory.BAG_INSERT, bagTheory.EMPTY_BAG]);
val _ = show_thm "singleton_global_bag=" singleton_global_bag;
val _ = show_thm "expression_global_flag=" flat_patternProofTheory.compile_exp_set_globals_FST_SND;
val _ = show_thm "tuple_global_flag=" flat_patternProofTheory.compile_exp_set_globals_tup;
val _ = show_thm "fst_snd_eq_case_typed=" flat_patternProofTheory.FST_SND_EQ_CASE;
val _ = show_thm "sub_bag_2_typed=" flat_patternProofTheory.SUB_BAG_2;
val _ = show_thm "inv_on_foldr_typed=" flat_patternProofTheory.inv_on_FOLDR;
val _ = show_thm "evaluate_decs_sing_typed=" flat_patternProofTheory.evaluate_decs_sing;
val _ = show_thm "option_all_forall_typed=" flat_patternProofTheory.OPTION_ALL_FORALL;
val _ = show_thm "smart_if_thm_typed=" flat_patternProofTheory.SmartIf_thm;
val _ = show_thm "do_eq_boolv_typed=" flat_patternProofTheory.do_eq_Boolv;
val _ = show_thm "fold_boolv_typed=" flat_patternProofTheory.fold_Boolv;
val _ = show_thm "max_list_less_every_typed=" flat_patternProofTheory.MAX_LIST_LESS_EVERY;
val _ = show_thm "global_bag_list_empty=" flatPropsTheory.elist_globals_eq_empty;
val _ = show_thm "sum_string_ords=" flat_patternProofTheory.sum_string_ords_eq;
val _ = show_thm "sum_string_ords_def=" flat_patternTheory.sum_string_ords_def;
val _ = show_thm "dec_name_to_num_def=" flat_patternTheory.dec_name_to_num_def;
val dec_name_to_num_explode = prove (
  ``!name. flat_pattern$dec_name_to_num name =
      case mlstring$explode name of
      | a :: b :: rest =>
          if a = #"." /\ b = #"." then flat_pattern$sum_string_ords 2 name else 0
      | _ => 0``,
  Cases THEN rename1 `strlit s` THEN Cases_on `s` THEN TRY (Cases_on `t`) THEN
    simp [flat_patternTheory.dec_name_to_num_def, mlstringTheory.strlen_def,
      mlstringTheory.strsub_def, mlstringTheory.explode_thm]);
val _ = show_thm "dec_name_to_num_explode=" dec_name_to_num_explode;
val _ = show_thm "dot_ord=" (EVAL ``ORD #"."``);
val _ = show_thm "enc_num_to_name_aux_def=" flat_patternTheory.enc_num_to_name_aux_def;
val _ = show_thm "enc_num_to_name_def=" flat_patternTheory.enc_num_to_name_def;
val _ = show_thm "generated_name_aux=" flat_patternProofTheory.dec_enc_aux;
val _ = show_thm "generated_name_roundtrip=" flat_patternProofTheory.dec_enc;
val _ = show_thm "generated_name_injective=" flat_patternProofTheory.enc_num_to_name_inj;
val _ = show_thm "list_rel_alookup_optrel=" flat_patternProofTheory.LIST_REL_ALOOKUP_OPTREL;
val _ = show_thm "list_rel_alookup=" flat_patternProofTheory.LIST_REL_ALOOKUP;
val _ = show_thm "list_rel_filter_mono=" flat_patternProofTheory.LIST_REL_FILTER_MONO;
val _ = show_thm "cond_false=" flat_patternProofTheory.COND_false;
val _ = show_thm "cond_true=" flat_patternProofTheory.COND_true;
val _ = show_thm "filter_eq_mono=" flat_patternProofTheory.FILTER_EQ_MONO;
val _ = show_thm "filter_eq_mono_trans=" flat_patternProofTheory.FILTER_EQ_MONO_TRANS;
val _ = show_thm "filter_eq_alookup_eq=" flat_patternProofTheory.FILTER_EQ_ALOOKUP_EQ;
val _ = show_thm "alookup_filter_eq=" flat_patternProofTheory.ALOOKUP_FILTER_EQ;
val _ = show_thm "enumerate_def=" miscTheory.enumerate_def;
val _ = show_thm "mem_enumerate_el=" flat_patternProofTheory.MEM_enumerate_EL;
val _ = show_thm "all_distinct_enumerate=" flat_patternProofTheory.ALL_DISTINCT_enumerate;
val _ = show_thm "pure_eval_to_def=" flat_patternProofTheory.pure_eval_to_def;
val _ = show_thm "append_length_eq=" flat_patternProofTheory.APPEND_LENGTH_EQ;
val _ = show_thm "pmatch_list_append_match=" flat_patternProofTheory.pmatch_list_append_Match_exists;
val _ = show_thm "alookup_def=" alistTheory.ALOOKUP_def;
val alookup_reversed_eq = prove (
  ``(!q:'a. ALOOKUP ([]:('a # 'b) list) q = NONE) /\
    (!x:'a. !y:'b. !t q. ALOOKUP ((x,y)::t) q =
      if q = x then SOME y else ALOOKUP t q)``,
  simp [alistTheory.ALOOKUP_def] THEN metis_tac []);
val _ = show_thm "alookup_reversed_eq=" alookup_reversed_eq;
val _ = show_thm "optrel_def=" optionTheory.OPTREL_def;
val optrel_clauses = prove (
  ``(!R:'a -> 'b -> bool. OPTREL R NONE NONE) /\
    (!R:'a -> 'b -> bool. !x y. OPTREL R (SOME x) (SOME y) <=> R x y) /\
    (!R:'a -> 'b -> bool. !x. ~OPTREL R (SOME x) NONE) /\
    (!R:'a -> 'b -> bool. !y. ~OPTREL R NONE (SOME y))``,
  simp [optionTheory.OPTREL_def]);
val _ = show_thm "optrel_clauses=" optrel_clauses;
val _ = show_thm "lookup_relation=" flat_patternProofTheory.ALOOKUP_rel_def;
val _ = show_thm "lookup_relation_empty=" flat_patternProofTheory.ALOOKUP_rel_empty;
val _ = show_thm "lookup_relation_cons_false=" flat_patternProofTheory.ALOOKUP_rel_cons_false;
val _ = show_thm "lookup_relation_append_false=" flat_patternProofTheory.ALOOKUP_rel_APPEND_L_false;
val _ = show_thm "lookup_relation_reflexive=" flat_patternProofTheory.ALOOKUP_rel_refl;
val _ = show_thm "lookup_relation_cons=" flat_patternProofTheory.ALOOKUP_rel_cons;
val _ = show_thm "lookup_relation_mono=" flat_patternProofTheory.ALOOKUP_rel_mono;
val _ = show_thm "lookup_relation_mono_rel=" flat_patternProofTheory.ALOOKUP_rel_mono_rel;
val _ = show_thm "lookup_relation_append=" flat_patternProofTheory.ALOOKUP_rel_append_suff;
val _ = show_thm "lookup_relation_equal=" flat_patternProofTheory.ALOOKUP_rel_EQ_ALOOKUP;
val _ = show_thm "lookup_relation_fst=" flat_patternProofTheory.ALOOKUP_rel_eq_fst;
val _ = show_thm "environment_set_noop=" flat_patternProofTheory.env_set_v_noop;
val _ = show_thm "sptree_lookup=" sptreeTheory.lookup_def;
val _ = show_thm "sptree_insert=" sptreeTheory.insert_def;
val _ = show_thm "sptree_domain_lookup=" sptreeTheory.domain_lookup;
val _ = show_thm "sptree_even_mod2=" arithmeticTheory.EVEN_MOD2;
val _ = show_thm "sptree_domain=" sptreeTheory.domain_def;
val sptree_domain_is_some = prove (
  ``!t. sptree$domain t = {k | IS_SOME (sptree$lookup k t)}``,
  simp [pred_setTheory.EXTENSION, sptreeTheory.domain_lookup, optionTheory.IS_SOME_EXISTS]);
val _ = show_thm "sptree_domain_is_some=" sptree_domain_is_some;
val sptree_lookup_distributed = prove (
  ``(!k t1 t2. sptree$lookup k (BN t1 t2) =
      if k = 0 then NONE else if k MOD 2 = 0 then
        sptree$lookup ((k - 1) DIV 2) t1 else sptree$lookup ((k - 1) DIV 2) t2) /\
    (!k a t1 t2. sptree$lookup k (BS t1 a t2) =
      if k = 0 then SOME a else if k MOD 2 = 0 then
        sptree$lookup ((k - 1) DIV 2) t1 else sptree$lookup ((k - 1) DIV 2) t2)``,
  simp [sptreeTheory.lookup_def, arithmeticTheory.EVEN_MOD2, boolTheory.COND_RAND]);
val _ = show_thm "sptree_lookup_distributed=" sptree_lookup_distributed;
val _ = show_thm "binding_fold_evaluation=" flat_patternProofTheory.pat_bindings_evaluate_FOLDR_lemma;
val _ = show_thm "every_mapi_simple=" flat_patternProofTheory.EVERY_MAPi_simple;
val _ = show_thm "compile_pat_bindings_def=" flat_patternTheory.compile_pat_bindings_def;
val _ = show_thm "compile_pat_rhs_def=" flat_patternTheory.compile_pat_rhs_def;
val _ = show_thm "compile_pat_bindings_simulation=" flat_patternProofTheory.compile_pat_bindings_simulation;
val _ = show_thm "value_relation_left_cases=" flat_patternProofTheory.v_rel_l_cases;
val _ = show_thm "esgc_decode_pos=" flat_patternProofTheory.esgc_free_decode_pos;
val _ = show_thm "esgc_decode_test=" flat_patternProofTheory.esgc_free_decode_test;
val _ = show_thm "esgc_decode_guard=" flat_patternProofTheory.esgc_free_decode_guard;
val _ = show_thm "esgc_bindings=" flat_patternProofTheory.esgc_free_compile_pat_bindings;
val _ = show_thm "esgc_naive_match=" flat_patternProofTheory.esgc_free_naive_pattern_match;
val _ = show_thm "esgc_naive_matches=" flat_patternProofTheory.esgc_free_naive_pattern_matches;
val _ = show_thm "esgc_compile_pats=" flat_patternProofTheory.esgc_free_compile_pats;
val _ = show_thm "globals_decode_pos=" flat_patternProofTheory.set_globals_decode_pos;
val _ = show_thm "globals_decode_test=" flat_patternProofTheory.set_globals_decode_test;
val _ = show_thm "globals_decode_guard=" flat_patternProofTheory.set_globals_decode_guard;
val _ = show_thm "globals_bindings=" flat_patternProofTheory.set_globals_compile_pat_bindings;
val _ = show_thm "globals_naive_match=" flat_patternProofTheory.set_globals_naive_pattern_match;
val _ = show_thm "globals_naive_matches=" flat_patternProofTheory.set_globals_naive_pattern_matches;
val _ = show_thm "globals_compile_pats=" flat_patternProofTheory.set_globals_compile_pats;
val _ = show_thm "compile_global_bounds=" flat_patternProofTheory.compile_exp_set_globals;
val _ = show_thm "compile_decs_global_bounds=" flat_patternProofTheory.compile_decs_elist_globals;
val _ = show_thm "compile_exp_esgc=" flat_patternProofTheory.compile_exp_esgc_free;
val _ = show_thm "compile_decs_esgc=" flat_patternProofTheory.compile_decs_esgc_free;
val _ = show_thm "no_mat_definition=" flatPropsTheory.no_Mat_def;
val _ = show_thm "no_mat_decs_definition=" flatPropsTheory.no_Mat_decs_def;
val _ = show_thm "compile_exp_no_mat=" flat_patternProofTheory.compile_exp_no_Mat;
val _ = show_thm "compile_decs_no_mat=" flat_patternProofTheory.compile_decs_no_Mat;
val _ = show_thm "decode_pos_definition=" flat_patternTheory.decode_pos_def;
val _ = show_thm "decode_test_definition=" flat_patternTheory.decode_test_def;
val _ = show_thm "simp_guard_definition=" flat_patternTheory.simp_guard_def;
val _ = show_thm "decode_guard_definition=" flat_patternTheory.decode_guard_def;
val _ = show_thm "decode_dtree_definition=" flat_patternTheory.decode_dtree_def;
val _ = show_thm "encode_pat_definition=" flat_patternTheory.encode_pat_def;
val _ = show_thm "naive_match_definition=" flat_patternTheory.naive_pattern_match_def;
val _ = show_thm "naive_matches_definition=" flat_patternTheory.naive_pattern_matches_def;
val _ = show_thm "max_dec_name_definition=" flat_patternTheory.max_dec_name_def;
val _ = show_thm "alookup_rel_mono_typed=" flat_patternProofTheory.ALOOKUP_rel_mono;
val _ = show_thm "alookup_rel_eq_typed=" flat_patternProofTheory.ALOOKUP_rel_EQ_ALOOKUP;
val _ = show_thm "alookup_rel_append_typed=" flat_patternProofTheory.ALOOKUP_rel_append_suff;
