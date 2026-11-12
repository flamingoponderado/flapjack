(* Typed source declarations for flat_elimProof (task 148). *)
load "preamble";
load "flat_elimProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble flat_elimProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="flat_elimProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by flat_elimProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of flat_elimProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "remove_flat_prog_sub_bag_typed" "remove_flat_prog_sub_bag";
val _ = emit "remove_flat_prog_elist_globals_eq_empty_typed" "remove_flat_prog_elist_globals_eq_empty";
val _ = emit "remove_flat_prog_esgc_free_typed" "remove_flat_prog_esgc_free";
val _ = emit "remove_flat_prog_distinct_globals_typed" "remove_flat_prog_distinct_globals";
val _ = emit "flat_remove_eval_sim_typed" "flat_remove_eval_sim";
val _ = emit "flat_remove_semantics_typed" "flat_remove_semantics";
val _ = emit "evaluate_sing_notKeep_flat_state_rel_typed" "evaluate_sing_notKeep_flat_state_rel";
val _ = emit "flat_decs_removal_lemma_typed" "flat_decs_removal_lemma";
val _ = emit "flat_removal_thm_typed" "flat_removal_thm";
val _ = emit "evaluate_flat_state_rel_lemma_typed" "evaluate_flat_state_rel_lemma";
val _ = emit "is_pure_EVERY_aconv_typed" "is_pure_EVERY_aconv";
val _ = emit "total_pat_IMP_typed" "total_pat_IMP";
val _ = emit "EXISTS_total_pat_typed" "EXISTS_total_pat";
val _ = emit "evaluate_sing_keep_flat_state_rel_eq_typed" "evaluate_sing_keep_flat_state_rel_eq";
val _ = emit "evaluate_dec_flat_state_rel_typed" "evaluate_dec_flat_state_rel";
val _ = emit "evaluate_keep_flat_state_rel_eq_lemma_typed" "evaluate_keep_flat_state_rel_eq_lemma";
val _ = emit "do_app_SOME_flat_state_rel_typed" "do_app_SOME_flat_state_rel";
val _ = emit "find_v_globals_v_to_list_typed" "find_v_globals_v_to_list";
val _ = emit "find_v_globals_list_to_v_typed" "find_v_globals_list_to_v";
val _ = emit "find_v_globals_list_to_v_APPEND_typed" "find_v_globals_list_to_v_APPEND";
val _ = emit "v_has_Eval_list_to_v_typed" "v_has_Eval_list_to_v";
val _ = emit "v_has_Eval_v_to_list_typed" "v_has_Eval_v_to_list";
val _ = emit "find_refs_globals_LUPDATE_typed" "find_refs_globals_LUPDATE";
val _ = emit "pmatch_Match_reachable_typed" "pmatch_Match_reachable";
val _ = emit "pmatch_not_has_Eval_typed" "pmatch_not_has_Eval";
val _ = emit "flat_state_rel_pmatch_typed" "flat_state_rel_pmatch";
val _ = emit "flat_state_rel_pmatch_rows_typed" "flat_state_rel_pmatch_rows";
val _ = emit "pmatch_rows_find_lookups_typed" "pmatch_rows_find_lookups";
val _ = emit "decs_closed_reduce_typed" "decs_closed_reduce";
val _ = emit "decs_closed_reduce_HD_typed" "decs_closed_reduce_HD";
val _ = emit "decs_closed_def_typed" "decs_closed_def";
val _ = emit "find_v_globals_def_typed" "find_v_globals_def";
val _ = emit "find_refs_globals_def_typed" "find_refs_globals_def";
val _ = emit "find_env_globals_def_typed" "find_env_globals_def";
val _ = emit "find_result_globals_def_typed" "find_result_globals_def";
val _ = emit "find_sem_prim_res_globals_def_typed" "find_sem_prim_res_globals_def";
val _ = emit "v_has_Eval_def1_typed" "v_has_Eval_def1";
val _ = emit "globals_rel_def_typed" "globals_rel_def";
val _ = emit "globals_rel_trans_typed" "globals_rel_trans";
val _ = emit "flat_state_rel_def_typed" "flat_state_rel_def";
val _ = emit "flat_state_rel_trans_typed" "flat_state_rel_trans";
val _ = emit "find_refs_globals_MEM_typed" "find_refs_globals_MEM";
val _ = emit "find_lookupsL_MEM_typed" "find_lookupsL_MEM";
val _ = emit "find_lookupsL_APPEND_typed" "find_lookupsL_APPEND";
val _ = emit "find_lookupsL_REVERSE_typed" "find_lookupsL_REVERSE";
val _ = emit "find_v_globalsL_REVERSE_typed" "find_v_globalsL_REVERSE";
val _ = emit "find_v_globalsL_APPEND_typed" "find_v_globalsL_APPEND";
val _ = emit "find_refs_globals_APPEND_typed" "find_refs_globals_APPEND";
val _ = emit "find_v_globalsL_EL_typed" "find_v_globalsL_EL";
val _ = emit "find_refs_globals_EL_typed" "find_refs_globals_EL";
val _ = emit "EVERY_EL_IMP_typed" "EVERY_EL_IMP";
val _ = emit "find_v_globals_Unitv_typed" "find_v_globals_Unitv";
val _ = emit "v_has_Eval_def_typed" "v_has_Eval_def";
val _ = emit "find_v_globalsL_LUPDATE_typed" "find_v_globalsL_LUPDATE";
val _ = emit "find_v_globalsL_REPLICATE_typed" "find_v_globalsL_REPLICATE";
val _ = emit "find_v_globals_MAP_Recclosure_typed" "find_v_globals_MAP_Recclosure";
val _ = emit "find_v_globalsL_MEM_typed" "find_v_globalsL_MEM";
val _ = emit "find_loc_EVERY_isEmpty_typed" "find_loc_EVERY_isEmpty";
val _ = emit "SUM_MAP_v3_size_typed" "SUM_MAP_v3_size";
