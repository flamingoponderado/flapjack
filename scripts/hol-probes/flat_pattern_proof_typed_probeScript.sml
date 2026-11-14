load "preamble";
load "flat_patternProofTheory";
load "flatLangTheory";
load "pattern_compTheory";
load "quantHeuristicsTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open flat_patternProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="flat_patternProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

fun emit_as label th = emit label th;

fun fetch_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");

fun source_text_of relpath =
  let
    val stream = TextIO.openIn (OS.Path.concat (source_cake, relpath))
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in text end;

val source_text = source_text_of "compiler/backend/proofs/flat_patternProofScript.sml";

val source_lines = String.fields (fn c => c = #"\n") source_text;

fun strip_leading s =
  Substring.string (Substring.dropl (fn c => c = #" " orelse c = #"\t")
    (Substring.full s));

fun decl_head line name kw =
  let
    val line' = strip_leading line
  in
    if not (String.isPrefix kw line') then NONE
    else
      let
        val rest = strip_leading (String.extract (line', String.size kw, NONE))
      in
        if String.isPrefix name rest andalso
           (String.size rest = String.size name orelse
            let val c = String.sub (rest, String.size name) in
              not (Char.isAlphaNum c) andalso c <> #"_"
            end)
        then SOME rest
        else NONE
      end
  end;

fun statement_of name =
  let
    fun scan [] = raise Fail ("missing declaration " ^ name)
      | scan (l :: rest) =
          (case decl_head l name "Theorem" of
             SOME _ => ("Proof", rest)
           | NONE => (case decl_head l name "Definition" of
                        SOME _ => ("End", rest)
                      | NONE => scan rest))
    val (stop, body) = scan source_lines
    fun take [] = []
      | take (l :: rest) =
          if String.isPrefix stop (strip_leading l) then []
          else l :: take rest
    val stmt = String.concatWith "\n" (take body)
  in
    if String.size stmt = 0 then raise Fail ("empty statement " ^ name)
    else stmt
  end;

fun strip_antiquote s =
  let
    fun go [] acc = String.concat (List.rev acc)
      | go (#"^" :: rest) acc =
        (case rest of
           (c :: _) => if Char.isAlphaNum c orelse c = #"_"
                       then go rest acc
                       else go rest (String.str #"^" :: acc)
         | [] => go rest (String.str #"^" :: acc))
      | go (c :: rest) acc = go rest (String.str c :: acc)
  in go (String.explode s) [] end;

fun capture label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (statement_of name))]
  in (print (label ^ "="); print_term tm; print "\n") end;

fun capture_dt label ty =
  let
    val cs = TypeBase.constructors_of ty
  in
    print (label ^ "=");
    print (String.concatWith "; "
      (map (fn c => let val (n,t) = dest_const c
         in n ^ ":" ^ type_to_string t end) cs));
    print "\n"
  end;

val _ = emit_exported "set_toList_fromList_typed" "set_toList_fromList";
val _ = emit_exported "decode_pos_no_Mat_typed" "decode_pos_no_Mat";
val _ = emit_exported "decode_test_no_Mat_typed" "decode_test_no_Mat";
val _ = emit_exported "decode_guard_no_Mat_typed" "decode_guard_no_Mat";
val _ = emit_exported "compile_pat_bindings_no_Mat_typed" "compile_pat_bindings_no_Mat";
val _ = emit_exported "naive_pattern_match_no_Mat_typed" "naive_pattern_match_no_Mat";
val _ = emit_exported "naive_pattern_matches_no_Mat_typed" "naive_pattern_matches_no_Mat";
val _ = emit_exported "simp_guard_thm_typed" "simp_guard_thm";
val _ = emit_exported "encode_pat_match_simulation_typed" "encode_pat_match_simulation";
val _ = emit_exported "compile_match_pmatch_rows_typed" "compile_match_pmatch_rows";
val _ = emit_exported "compile_match_EL_typed" "compile_match_EL";
val _ = emit_exported "compile_pats_no_Mat_typed" "compile_pats_no_Mat";
val _ = emit_exported "decode_dtree_no_Mat_typed" "decode_dtree_no_Mat";
val _ = emit_exported "set_globals_decode_dtree_empty_typed" "set_globals_decode_dtree_empty";
val _ = emit_exported "esgc_free_decode_dtree_typed" "esgc_free_decode_dtree";
val _ = emit_exported "naive_pattern_matches_correct_typed" "naive_pattern_matches_correct";
val _ = emit_exported "evaluate_compile_pat_rhs_typed" "evaluate_compile_pat_rhs";
val _ = emit_exported "evaluate_compile_pats_typed" "evaluate_compile_pats";
val _ = emit_exported "evaluate_SmartIf_typed" "evaluate_SmartIf";
val _ = emit_exported "state_rel_dec_clock_typed" "state_rel_dec_clock";
val _ = emit_exported "encode_val_def_typed" "encode_val_def";
val _ = emit_exported "encode_refs_def_typed" "encode_refs_def";
val _ = emit_exported "decode_test_simulation_typed" "decode_test_simulation";
val _ = emit_exported "decode_pos_simulation_typed" "decode_pos_simulation";
val _ = emit_exported "decode_guard_simulation_typed" "decode_guard_simulation";
val _ = emit_exported "decode_dtree_simulation_typed" "decode_dtree_simulation";
val _ = emit_exported "evaluate_Bool_typed" "evaluate_Bool";
val _ = emit_exported "compile_pat_bindings_simulation_typed" "compile_pat_bindings_simulation";
val _ = emit_exported "pmatch_list_append_Match_exists_typed" "pmatch_list_append_Match_exists";
val _ = emit_exported "APPEND_LENGTH_EQ_typed" "APPEND_LENGTH_EQ";
val _ = emit_exported "pmatch_list_Match_IMP_LENGTH_typed" "pmatch_list_Match_IMP_LENGTH";
val _ = emit_exported "pure_eval_to_def_typed" "pure_eval_to_def";
val _ = emit_exported "MEM_enumerate_EL_typed" "MEM_enumerate_EL";
val _ = emit_exported "ALL_DISTINCT_enumerate_typed" "ALL_DISTINCT_enumerate";
val _ = emit_exported "FILTER_EQ_ALOOKUP_EQ_typed" "FILTER_EQ_ALOOKUP_EQ";
val _ = emit_exported "COND_false_typed" "COND_false";
val _ = emit_exported "COND_true_typed" "COND_true";
val _ = emit_exported "LIST_REL_FILTER_MONO_typed" "LIST_REL_FILTER_MONO";
val _ = emit_exported "LIST_REL_ALOOKUP_typed" "LIST_REL_ALOOKUP";
val _ = emit_exported "LIST_REL_ALOOKUP_OPTREL_typed" "LIST_REL_ALOOKUP_OPTREL";
val _ = emit_exported "state_rel_def_typed" "state_rel_def";
val _ = emit_exported "state_rel_initial_state_typed" "state_rel_initial_state";
(* Inductive v_rel: captured through its rules theorem. *)
val _ = emit_exported "v_rel_typed" "v_rel_rules";
val _ = emit_exported "compile_exp_no_Mat_typed" "compile_exp_no_Mat";
val _ = emit_exported "compile_decs_no_Mat_typed" "compile_decs_no_Mat";
val _ = emit_exported "compile_exp_esgc_free_typed" "compile_exp_esgc_free";
val _ = emit_exported "compile_decs_esgc_free_typed" "compile_decs_esgc_free";
val _ = emit_exported "compile_exp_set_globals_typed" "compile_exp_set_globals";
val _ = emit_exported "compile_decs_elist_globals_typed" "compile_decs_elist_globals";
val _ = emit_exported "set_globals_naive_pattern_matches_typed" "set_globals_naive_pattern_matches";
val _ = emit_exported "set_globals_compile_pats_typed" "set_globals_compile_pats";
val _ = emit_exported "set_globals_decode_pos_typed" "set_globals_decode_pos";
val _ = emit_exported "set_globals_decode_test_typed" "set_globals_decode_test";
val _ = emit_exported "set_globals_decode_guard_typed" "set_globals_decode_guard";
val _ = emit_exported "set_globals_compile_pat_bindings_typed" "set_globals_compile_pat_bindings";
val _ = emit_exported "set_globals_naive_pattern_match_typed" "set_globals_naive_pattern_match";
val _ = emit_exported "esgc_free_compile_pats_typed" "esgc_free_compile_pats";
val _ = emit_exported "esgc_free_decode_pos_typed" "esgc_free_decode_pos";
val _ = emit_exported "esgc_free_decode_test_typed" "esgc_free_decode_test";
val _ = emit_exported "esgc_free_decode_guard_typed" "esgc_free_decode_guard";
val _ = emit_exported "esgc_free_compile_pat_bindings_typed" "esgc_free_compile_pat_bindings";
val _ = emit_exported "esgc_free_naive_pattern_match_typed" "esgc_free_naive_pattern_match";
val _ = emit_exported "esgc_free_naive_pattern_matches_typed" "esgc_free_naive_pattern_matches";
val _ = emit_exported "ALOOKUP_rel_MAP_same_typed" "ALOOKUP_rel_MAP_same";
val _ = emit_exported "install_conf_rel_def_typed" "install_conf_rel_def";
val _ = emit_exported "EVERY_MAPi_simple_typed" "EVERY_MAPi_simple";
val _ = emit_exported "ALOOKUP_rel_def_typed" "ALOOKUP_rel_def";
val _ = emit_exported "ALOOKUP_rel_empty_typed" "ALOOKUP_rel_empty";
val _ = emit_exported "ALOOKUP_rel_cons_false_typed" "ALOOKUP_rel_cons_false";
val _ = emit_exported "ALOOKUP_rel_refl_typed" "ALOOKUP_rel_refl";
val _ = emit_exported "pat_bindings_evaluate_FOLDR_lemma_typed" "pat_bindings_evaluate_FOLDR_lemma";
val _ = emit_exported "env_set_v_noop_typed" "env_set_v_noop";
val _ = emit_exported "ALOOKUP_rel_mono_typed" "ALOOKUP_rel_mono";
val _ = emit_exported "ALOOKUP_rel_cons_typed" "ALOOKUP_rel_cons";
val _ = emit_exported "ALOOKUP_rel_mono_rel_typed" "ALOOKUP_rel_mono_rel";
val _ = emit_exported "ALOOKUP_rel_EQ_ALOOKUP_typed" "ALOOKUP_rel_EQ_ALOOKUP";
val _ = emit_exported "ALOOKUP_rel_APPEND_L_false_typed" "ALOOKUP_rel_APPEND_L_false";
val _ = emit_exported "ALOOKUP_rel_append_suff_typed" "ALOOKUP_rel_append_suff";
val _ = emit_exported "ALOOKUP_rel_eq_fst_typed" "ALOOKUP_rel_eq_fst";
val _ = emit_exported "sum_string_ords_eq_typed" "sum_string_ords_eq";
val _ = emit_exported "dec_enc_aux_typed" "dec_enc_aux";
val _ = emit_exported "dec_enc_typed" "dec_enc";
val _ = emit_exported "enc_num_to_name_inj_typed" "enc_num_to_name_inj";
val _ = emit_exported "op_sets_globals_gbag_typed" "op_sets_globals_gbag";
val _ = emit_exported "compile_exp_set_globals_FST_SND_typed" "compile_exp_set_globals_FST_SND";
val _ = emit_exported "compile_exp_set_globals_tup_typed" "compile_exp_set_globals_tup";
val _ = emit_exported "match_rel_def_typed" "match_rel_def";
val _ = emit_exported "match_rel_thms_typed" "match_rel_thms";
val _ = emit_exported "match_rel_IMP_typed" "match_rel_IMP";
val _ = emit_exported "MAX_ADD_LESS_typed" "MAX_ADD_LESS";
val _ = emit_exported "LESS_MAX_ADD_typed" "LESS_MAX_ADD";
val _ = emit_exported "MAX_ADD_LE_typed" "MAX_ADD_LE";
val _ = emit_exported "env_rel_mono_typed" "env_rel_mono";
val _ = emit_exported "env_rel_ALOOKUP_typed" "env_rel_ALOOKUP";
val _ = emit_exported "ALOOKUP_MAP_3_typed" "ALOOKUP_MAP_3";
val _ = emit_exported "do_opapp_thm_typed" "do_opapp_thm";
val _ = emit_exported "do_opapp_thm_REVERSE_typed" "do_opapp_thm_REVERSE";
val _ = emit_exported "pmatch_thm_typed" "pmatch_thm";
val _ = emit_exported "simple_val_rel_step_isClosure_typed" "simple_val_rel_step_isClosure";
val _ = emit_exported "simple_val_rel_typed" "simple_val_rel";
val _ = emit_exported "simple_state_rel_typed" "simple_state_rel";
val _ = emit_exported "compile_exps_evaluate_typed" "compile_exps_evaluate";
val _ = emit_exported "compile_decs_eval_sim_typed" "compile_decs_eval_sim";
val _ = emit_exported "compile_decs_semantics_typed" "compile_decs_semantics";
val _ = emit_exported "do_if_Boolv_typed" "do_if_Boolv";
val _ = emit_exported "FST_SND_EQ_CASE_typed" "FST_SND_EQ_CASE";
val _ = emit_exported "SUB_BAG_2_typed" "SUB_BAG_2";
val _ = emit_exported "inv_on_FOLDR_typed" "inv_on_FOLDR";
val _ = emit_exported "evaluate_decs_sing_typed" "evaluate_decs_sing";
val _ = emit_exported "OPTION_ALL_FORALL_typed" "OPTION_ALL_FORALL";
val _ = emit_exported "pmatch_rows_encode_typed" "pmatch_rows_encode";
val _ = emit_exported "SmartIf_thm_typed" "SmartIf_thm";
val _ = emit_exported "do_eq_Boolv_typed" "do_eq_Boolv";
val _ = emit_exported "app_pos_Term_IMP_typed" "app_pos_Term_IMP";
val _ = emit_exported "MAX_LIST_LESS_EVERY_typed" "MAX_LIST_LESS_EVERY";
val _ = emit_exported "do_if_helper_typed" "do_if_helper";
val _ = emit_exported "do_app_thm_REVERSE_typed" "do_app_thm_REVERSE";
val _ = emit_exported "pmatch_rows_same_FST_typed" "pmatch_rows_same_FST";
val _ = emit_exported "max_dec_name_LESS_EVERY_typed" "max_dec_name_LESS_EVERY";
val _ = emit_exported "do_eval_thm_typed" "do_eval_thm";
val _ = emit_exported "naive_pattern_match_correct_typed" "naive_pattern_match_correct";
val _ = emit_exported "FLOOKUP_encode_refs_typed" "FLOOKUP_encode_refs";
val _ = emit_exported "ALOOKUP_FILTER_EQ_typed" "ALOOKUP_FILTER_EQ";
val _ = emit_exported "FILTER_EQ_MONO_typed" "FILTER_EQ_MONO";
val _ = emit_exported "FILTER_EQ_MONO_TRANS_typed" "FILTER_EQ_MONO_TRANS";
val _ = emit_exported "v_rel_l_cases_typed" "v_rel_l_cases";
val _ = emit_exported "naive_pattern_match_correct_inst_typed" "naive_pattern_match_correct_inst";
val _ = emit_exported "fold_Boolv_typed" "fold_Boolv";
val _ = emit_exported "do_app_thm_typed" "do_app_thm";
val _ = capture "state_rel_IMP_clock_typed" "state_rel_IMP_clock";

(* Generated relation theorems and the derived local comp_thm. *)
val _ = emit_exported "v_rel_ind_typed" "v_rel_ind";
val _ = emit_exported "v_rel_cases_typed" "v_rel_cases";

(* comp_thm: pattern_compTheory.comp_thm rewritten exactly as in the source. *)
val _ = emit_as "comp_thm_typed"
  (fetch_other ("pattern_comp","comp_thm")
    |> REWRITE_RULE [GSYM (fetch_other ("quantHeuristics","IS_SOME_EQ_NOT_NONE"))]
    |> SIMP_RULE bool_ss [IS_SOME_EXISTS, PULL_EXISTS]);
