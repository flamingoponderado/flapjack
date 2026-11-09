(* Typed source statements for closure annotation correctness. *)
load "clos_annotateProofTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble clos_annotateTheory closPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "const_zero_typed=" clos_annotateTheory.const_0_def;
val _ = show "no_overlap_typed=" clos_annotateTheory.no_overlap_def;
val _ = show "alt_free_sing_typed=" clos_annotateTheory.alt_free_sing_def;
val _ = show "alt_free_def_typed=" clos_annotateTheory.alt_free_def;
val _ = show "alt_free_sing_eq_typed=" clos_annotateTheory.alt_free_sing_eq;
val _ = show "get_var_typed=" clos_annotateTheory.get_var_def;
val _ = show "shifted_env_typed=" clos_annotateTheory.shifted_env_def;
val _ = show "shift_def_typed=" clos_annotateTheory.shift_def;
val _ = show "shift_sing_eq_typed=" clos_annotateTheory.shift_sing_eq;
val _ = show "shift_sing_typed=" clos_annotateTheory.shift_sing_def;
val _ = show "annotate_def_typed=" clos_annotateTheory.annotate_def;
val _ = show "alt_fv_def_typed=" clos_annotateProofTheory.alt_fv_def;
val _ = show "alt_free_thm_typed=" clos_annotateProofTheory.alt_free_thm;
val _ = show "alt_fv1_def_typed=" clos_annotateProofTheory.alt_fv1_def;
val _ = show "alt_fv_nil_typed=" clos_annotateProofTheory.alt_fv_nil;
val _ = show "alt_fv_cons_typed=" clos_annotateProofTheory.alt_fv_cons;
val _ = show "alt_fv_REPLICATE_typed=" clos_annotateProofTheory.alt_fv_REPLICATE;
val _ = show "v_rel_rules_typed=" clos_annotateProofTheory.v_rel_rules;
val _ = show "annotate_sing_typed=" clos_annotateTheory.annotate_sing_def;
val _ = show "annotate_list_typed=" clos_annotateTheory.annotate_list_def;
val _ = show "annotate_sing_eq_typed=" clos_annotateTheory.annotate_sing_eq;
val _ = show "compile_def_typed=" clos_annotateTheory.compile_def;
val _ = show "compile_eq_typed=" clos_annotateTheory.compile_eq;
val _ = show "compile_inc_def_typed=" clos_annotateTheory.compile_inc_def;
val _ = show "compile_inc_eq_typed=" clos_annotateTheory.compile_inc_eq;
val _ = show "MAP_FST_compile_typed=" clos_annotateProofTheory.MAP_FST_compile;
val _ = show "semantics_annotate_typed=" clos_annotateProofTheory.semantics_annotate;
val _ = show "shift_obeys_max_app_typed=" clos_annotateProofTheory.shift_obeys_max_app;
val _ = show "alt_free_obeys_max_app_typed=" clos_annotateProofTheory.alt_free_obeys_max_app;
val _ = show "annotate_obeys_max_app_typed=" clos_annotateProofTheory.annotate_obeys_max_app;
val _ = show "obeys_max_app_ann_typed=" clos_annotateProofTheory.obeys_max_app_ann;
val _ = show "shift_no_Labels_typed=" clos_annotateProofTheory.shift_no_Labels;
val _ = show "alt_free_no_Labels_typed=" clos_annotateProofTheory.alt_free_no_Labels;
val _ = show "annotate_no_Labels_typed=" clos_annotateProofTheory.annotate_no_Labels;
val _ = show "no_Labels_ann_typed=" clos_annotateProofTheory.no_Labels_ann;
val _ = show "app_call_dests_def_typed=" closPropsTheory.app_call_dests_def;
val _ = show "app_call_dests_append_typed=" closPropsTheory.app_call_dests_append;
val _ = show "call_dests_shift_typed=" clos_annotateProofTheory.call_dests_shift;
val _ = show "code_locs_shift_typed=" clos_annotateProofTheory.code_locs_shift;
val _ = show "code_locs_alt_free_typed=" clos_annotateProofTheory.code_locs_alt_free;
val _ = show "code_locs_annotate_typed=" clos_annotateProofTheory.code_locs_annotate;
val _ = show "annotate_code_locs_typed=" clos_annotateProofTheory.annotate_code_locs;
val _ = show "code_locs_const_0_typed=" clos_annotateProofTheory.code_locs_const_0;
(* Replay the original local proofs: local declarations are not exported by
   clos_annotateProofTheory, so bind the first replay explicitly for the second. *)
val alt_free_code_locs_replay = prove (
  ``!xs. set (code_locs (FST (alt_free xs))) SUBSET set (code_locs xs)``,
  ho_match_mp_tac clos_annotateTheory.alt_free_ind
  >> simp[alt_free_def,code_locs_def,UNCURRY] >> rw[]
  >> Cases_on `alt_free [x]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free [x1]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free [x2]` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> Cases_on `alt_free xs` >> full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  >> fs[MAP_MAP_o,o_DEF,SUBSET_DEF,code_locs_def,GSYM MAP_K_REPLICATE]
  >> ONCE_REWRITE_TAC [code_locs_map]
  >> simp[MEM_FLAT,MEM_GENLIST,MEM_MAP,PULL_EXISTS,UNCURRY,HD_FST_alt_free]
  >> metis_tac[HD_FST_alt_free,FST,PAIR]);
val _ = show "alt_free_code_locs_local_typed=" alt_free_code_locs_replay;
val alt_free_code_locs_distinct_replay = prove (
  ``!xs. ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs (FST (alt_free xs)))``,
  recInduct alt_free_ind
  >> rw[alt_free_def,code_locs_def]
  >> rpt(pairarg_tac >> fs[])
  >> fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def] >> rw[]
  >> fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def,GSYM MAP_K_REPLICATE,code_locs_map,FLAT_MAP_NIL]
  >> TRY (
    rename1`GENLIST`
    >> fs[MEM_GENLIST,MAP_MAP_o,o_DEF,UNCURRY,HD_FST_alt_free,PULL_EXISTS]
    >> imp_res_tac alt_free_SING >> fs[] >> rveq
    >> fs[ALL_DISTINCT_FLAT,EL_MAP]
    >> fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >> rw[]
    >> metis_tac[SUBSET_DEF,alt_free_code_locs_replay,FST] )
  >> metis_tac[SUBSET_DEF,alt_free_code_locs_replay,FST,alt_free_SING,HD]);
val _ = show "alt_free_code_locs_distinct_local_typed=" alt_free_code_locs_distinct_replay;
val _ = show "code_locs_REP_const_0_typed=" clos_annotateProofTheory.code_locs_REP_const_0;
val _ = show "EVERY_shift_sing_typed=" clos_annotateProofTheory.EVERY_shift_sing;
val _ = show "HD_annotate_SING_typed=" clos_annotateProofTheory.HD_annotate_SING;
val _ = show "every_Fn_vs_SOME_shift_typed=" clos_annotateProofTheory.every_Fn_vs_SOME_shift;
val _ = show "every_Fn_vs_SOME_annotate_typed=" clos_annotateProofTheory.every_Fn_vs_SOME_annotate;
val _ = show "every_Fn_SOME_shift_typed=" clos_annotateProofTheory.every_Fn_SOME_shift;
val _ = show "every_Fn_SOME_const_0_typed=" clos_annotateProofTheory.every_Fn_SOME_const_0;
val _ = show "every_Fn_SOME_alt_free_typed=" clos_annotateProofTheory.every_Fn_SOME_alt_free;
val _ = show "every_Fn_SOME_annotate_typed=" clos_annotateProofTheory.every_Fn_SOME_annotate;
val _ = show "every_Fn_SOME_ann_typed=" clos_annotateProofTheory.every_Fn_SOME_ann;
(* env_set_default is local to the original proof script. *)
val env_set_default_replay = prove (
  ``x SUBSET clos_annotateProof$env_ok 0 0 sptree$LN [] env'``,
  full_simp_tac (srw_ss())
    [SUBSET_DEF, IN_DEF, clos_annotateProofTheory.v_rel_cases |> CONJUNCT2]);
val _ = show "env_set_default_local_typed=" env_set_default_replay;
