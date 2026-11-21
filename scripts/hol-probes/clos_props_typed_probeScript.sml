(* Typed source declarations for closProps (task 239).
   Exported theorems and definitions are fetched from the theory DB; `[local]`
   theorems are parsed from the pinned source text with `^antiquotation`
   splices expanded, as in bvi_props_typed_probeScript.sml. *)
load "preamble";
load "closPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble closPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="closProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by closProps")
  | SOME (th,_) => show label th;


(* `[local]` theorems are not exported by the theory; parse their pinned
   source statements, expanding `^x` splices to the term bound by
   `val x = ``...``;`. *)
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

val source_text = source_text_of "compiler/backend/semantics/closPropsScript.sml";

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
           | NONE => scan rest)
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

local
  fun lead_trim s =
    Substring.string (Substring.dropl
      (fn c => c = #" " orelse c = #"\t") (Substring.full s));

  fun tail_trim s =
    let
      fun drop [] = []
        | drop (c :: rest) =
            if c = #" " orelse c = #"\t" orelse c = #";" then drop rest
            else c :: rest
    in String.implode (List.rev (drop (List.rev (String.explode s)))) end;

  (* ``term`` or curly-quoted "term" (UTF-8), possibly spanning lines *)
  fun quoted body =
    let
      fun close acc [] = NONE
        | close acc (#"`" :: #"`" :: _) = SOME (String.implode (List.rev acc))
        | close acc (#"\226" :: #"\128" :: #"\157" :: _) =
            SOME (String.implode (List.rev acc))
        | close acc (c :: rest) = close (c :: acc) rest
      fun scan [] = NONE
        | scan (#"`" :: #"`" :: rest) = close [] rest
        | scan (#"\226" :: #"\128" :: #"\156" :: rest) = close [] rest
        | scan (_ :: rest) = scan rest
    in scan (String.explode body) end;

  fun ends_semi s =
    let
      fun go [] = false
        | go (c :: rest) =
            if c = #" " orelse c = #"\t" then go rest else c = #";"
    in go (List.rev (String.explode s)) end;

  fun chunk_for lines name =
    let
      val pre = "val " ^ name ^ " ="
      fun scan [] = NONE
        | scan (l :: rest) =
            if String.isPrefix pre (lead_trim l) then
              let
                fun take acc [] = SOME (String.concatWith "\n" (List.rev acc))
                  | take acc (m :: ms) =
                      let val acc' = m :: acc in
                        if isSome (quoted (String.concatWith "\n" (List.rev acc')))
                           orelse ends_semi m
                        then SOME (String.concatWith "\n" (List.rev acc'))
                        else take acc' ms
                      end
              in
                case take [l] rest of
                  NONE => NONE
                | SOME c =>
                    SOME (String.extract (lead_trim c, String.size pre, NONE))
              end
            else scan rest
    in scan lines end;

  fun type_text body =
    case quoted body of
      NONE => NONE
    | SOME q =>
        let val q' = lead_trim q in
          if String.isPrefix ":" q' then
            SOME (tail_trim (String.extract (q', 1, NONE)))
          else
            (case Substring.position ":" (Substring.full q) of
               (_, rhs) =>
                 if Substring.isEmpty rhs then NONE
                 else SOME (tail_trim
                   (String.extract (Substring.string rhs, 1, NONE))))
        end;

  fun expansion lines name =
    case chunk_for lines name of
      NONE => NONE
    | SOME body =>
        if String.isPrefix "mk_var" (lead_trim body) then
          (case type_text body of
             SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
           | NONE => NONE)
        else
          (case quoted body of
             SOME q => SOME ("(" ^ q ^ ")")
           | NONE => NONE);
in
  fun strip_antiquote s =
    let
      val lines = String.fields (fn c => c = #"\n") source_text
      fun take_name (cs, acc) =
        case cs of
          (c :: rest) =>
            if Char.isAlphaNum c orelse c = #"_"
            then take_name (rest, c :: acc)
            else (String.implode (List.rev acc), cs)
        | [] => (String.implode (List.rev acc), [])
      fun go [] acc = String.concat (List.rev acc)
        | go (#"^" :: rest) acc =
            let val (name, rest') = take_name (rest, []) in
              case expansion lines name of
                SOME e => go rest' (e :: acc)
              | NONE => go rest (String.str #"^" :: acc)
            end
        | go (c :: rest) acc = go rest (String.str c :: acc)
    in go (String.explode s) [] end;
end;

fun capture label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (statement_of name))]
  in (print (label ^ "="); print_term tm; print "\n") end;


val _ = emit "with_same_clock_typed" "with_same_clock";
val _ = emit "dec_clock_code_typed" "dec_clock_code";
val _ = emit "dec_clock_ffi_typed" "dec_clock_ffi";
val _ = emit "dec_clock_compile_oracle_typed" "dec_clock_compile_oracle";
val _ = emit "dec_clock_compile_typed" "dec_clock_compile";
val _ = emit "list_to_v_EVERY_APPEND_typed" "list_to_v_EVERY_APPEND";
val _ = capture "forall_sum_typed" "forall_sum";
val _ = emit "evaluate_better_ind_typed" "evaluate_better_ind";
val _ = emit "ref_rel_simp_typed" "ref_rel_simp";
val _ = emit "code_locs_cons_typed" "code_locs_cons";
val _ = emit "code_locs_map_typed" "code_locs_map";
val _ = emit "BIGUNION_MAP_code_locs_SND_SND_typed" "BIGUNION_MAP_code_locs_SND_SND";
val _ = emit "contains_App_SOME_EXISTS_typed" "contains_App_SOME_EXISTS";
val _ = emit "every_Fn_SOME_APPEND_typed" "every_Fn_SOME_APPEND";
val _ = emit "IMP_every_Fn_vs_NONE_TAKE_typed" "IMP_every_Fn_vs_NONE_TAKE";
val _ = emit "every_Fn_vs_NONE_APPEND_typed" "every_Fn_vs_NONE_APPEND";
val _ = emit "every_Fn_vs_SOME_APPEND_typed" "every_Fn_vs_SOME_APPEND";
val _ = emit "exp3_size_typed" "exp3_size";
val _ = emit "exp1_size_rw_typed" "exp1_size_rw";
val _ = emit "fv_nil_typed" "fv_nil";
val _ = emit "fv1_intro_typed" "fv1_intro";
val _ = emit "fv1_thm_typed" "fv1_thm";
val _ = emit "fv_cons_typed" "fv_cons";
val _ = emit "fv_exists_typed" "fv_exists";
val _ = emit "fv_MAPi_typed" "fv_MAPi";
val _ = emit "fv_GENLIST_Var_typed" "fv_GENLIST_Var";
val _ = emit "fv_REPLICATE_typed" "fv_REPLICATE";
val _ = emit "v_ind_typed" "v_ind";
val _ = emit "do_app_err_typed" "do_app_err";
val _ = emit "Boolv_11_typed" "Boolv_11";
val _ = emit "evaluate_LENGTH_typed" "evaluate_LENGTH";
val _ = emit "evaluate_app_IMP_LENGTH_typed" "evaluate_app_IMP_LENGTH";
val _ = emit "do_install_const_typed" "do_install_const";
val _ = emit "evaluate_const_typed" "evaluate_const";
val _ = emit "evaluate_app_const_typed" "evaluate_app_const";
val _ = emit "evaluate_code_typed" "evaluate_code";
val _ = emit "evaluate_app_code_typed" "evaluate_app_code";
val _ = emit "evaluate_MAP_Op_Const_typed" "evaluate_MAP_Op_Const";
val _ = emit "lookup_vars_NONE_typed" "lookup_vars_NONE";
val _ = emit "lookup_vars_SOME_typed" "lookup_vars_SOME";
val _ = emit "lookup_vars_MEM_typed" "lookup_vars_MEM";
val _ = emit "clock_lemmas_typed" "clock_lemmas";
val _ = emit "evaluate_app_rw_typed" "evaluate_app_rw";
val _ = emit "pure_correct_typed" "pure_correct";
val _ = capture "pair_lam_lem_typed" "pair_lam_lem";
val _ = emit "do_app_split_list_typed" "do_app_split_list";
val _ = emit "is_closure_def_typed" "is_closure_def";
val _ = emit "clo_to_loc_def_typed" "clo_to_loc_def";
val _ = emit "clo_to_env_def_typed" "clo_to_env_def";
val _ = emit "clo_to_partial_args_def_typed" "clo_to_partial_args_def";
val _ = emit "clo_add_partial_args_def_typed" "clo_add_partial_args_def";
val _ = emit "clo_to_num_params_def_typed" "clo_to_num_params_def";
val _ = emit "rec_clo_ok_def_typed" "rec_clo_ok_def";
val _ = emit "dest_closure_full_length_typed" "dest_closure_full_length";
val _ = emit "evaluate_app_clock_less_typed" "evaluate_app_clock_less";
val _ = emit "clo_add_partial_args_nil_typed" "clo_add_partial_args_nil";
val _ = emit "clo_can_apply_def_typed" "clo_can_apply_def";
val _ = emit "check_closures_def_typed" "check_closures_def";
val _ = emit "dest_closure_partial_is_closure_typed" "dest_closure_partial_is_closure";
val _ = emit "is_closure_add_partial_args_nil_typed" "is_closure_add_partial_args_nil";
val _ = emit "evaluate_app_clock0_typed" "evaluate_app_clock0";
val _ = emit "evaluate_app_clock0_timeout_typed" "evaluate_app_clock0_timeout";
val _ = emit "evaluate_app_clock_drop_typed" "evaluate_app_clock_drop";
val _ = emit "dest_closure_is_closure_typed" "dest_closure_is_closure";
val _ = emit "stage_partial_app_typed" "stage_partial_app";
val _ = emit "dest_closure_full_addargs_typed" "dest_closure_full_addargs";
val _ = emit "evaluate_append_typed" "evaluate_append";
val _ = emit "evaluate_GENLIST_Var_typed" "evaluate_GENLIST_Var";
val _ = emit "evaluate_length_imp_typed" "evaluate_length_imp";
val _ = emit "evaluate_app_length_imp_typed" "evaluate_app_length_imp";
val _ = emit "dest_closure_none_append_typed" "dest_closure_none_append";
val _ = emit "dest_closure_none_append2_typed" "dest_closure_none_append2";
val _ = emit "dest_closure_rest_length_typed" "dest_closure_rest_length";
val _ = emit "dest_closure_partial_twice_typed" "dest_closure_partial_twice";
val _ = emit "evaluate_app_append_typed" "evaluate_app_append";
val _ = capture "revnil_typed" "revnil";
val _ = emit "dest_closure_full_maxapp_typed" "dest_closure_full_maxapp";
val _ = emit "dest_closure_full_split_prime_typed" "dest_closure_full_split'";
val _ = emit "dest_closure_partial_split_typed" "dest_closure_partial_split";
val _ = emit "dest_closure_partial_split_prime_typed" "dest_closure_partial_split'";
val _ = emit "dest_closure_NONE_Full_to_Partial_typed" "dest_closure_NONE_Full_to_Partial";
val _ = emit "dec_clock_with_clock_typed" "dec_clock_with_clock";
val _ = emit "do_app_ffi_error_IMP_typed" "do_app_ffi_error_IMP";
val _ = emit "do_app_add_to_clock_typed" "do_app_add_to_clock";
val _ = emit "do_install_add_to_clock_typed" "do_install_add_to_clock";
val _ = emit "do_install_type_error_add_to_clock_typed" "do_install_type_error_add_to_clock";
val _ = emit "do_install_not_Rraise_typed" "do_install_not_Rraise";
val _ = emit "do_install_not_Rffi_error_typed" "do_install_not_Rffi_error";
val _ = emit "evaluate_add_clock_initial_state_typed" "evaluate_add_clock_initial_state";
val _ = capture "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = capture "evaluate_io_events_mono_imp_typed" "evaluate_io_events_mono_imp";
val _ = capture "with_clock_ffi_typed" "with_clock_ffi";
val _ = emit "evaluate_add_to_clock_io_events_mono_typed" "evaluate_add_to_clock_io_events_mono";
val _ = emit "do_app_never_timesout_typed" "do_app_never_timesout";
val _ = emit "evaluate_timeout_clocks0_typed" "evaluate_timeout_clocks0";
val _ = emit "exp_size_MEM_typed" "exp_size_MEM";
val _ = emit "evaluate_eq_nil_typed" "evaluate_eq_nil";
val _ = emit "exp2_size_rw_typed" "exp2_size_rw";
val _ = emit "v_size_lemma_typed" "v_size_lemma";
val _ = emit "elglobals_EQ_EMPTY_typed" "elglobals_EQ_EMPTY";
val _ = emit "elist_globals_FOLDR_typed" "elist_globals_FOLDR";
val _ = emit "elist_globals_reverse_typed" "elist_globals_reverse";
val _ = emit "isClos_cases_typed" "isClos_cases";
val _ = capture "simple_val_rel_alt_typed" "simple_val_rel_alt";
val _ = emit "simple_state_rel_ffi_typed" "simple_state_rel_ffi";
val _ = emit "simple_state_rel_fdom_typed" "simple_state_rel_fdom";
val _ = capture "simple_state_rel_update_ffi_typed" "simple_state_rel_update_ffi";
val _ = capture "simple_state_rel_update_bytes_typed" "simple_state_rel_update_bytes";
val _ = capture "simple_state_rel_update_values_typed" "simple_state_rel_update_values";
val _ = capture "simple_state_rel_update_thunks_typed" "simple_state_rel_update_thunks";
val _ = capture "simple_state_rel_update_globals_typed" "simple_state_rel_update_globals";
val _ = capture "simple_state_rel_get_global_typed" "simple_state_rel_get_global";
val _ = capture "isClos_IMP_v_to_list_NONE_typed" "isClos_IMP_v_to_list_NONE";
val _ = capture "v_rel_to_list_ByteVector_typed" "v_rel_to_list_ByteVector";
val _ = capture "v_rel_to_list_byte1_typed" "v_rel_to_list_byte1";
val _ = capture "v_rel_to_list_byte2_typed" "v_rel_to_list_byte2";
val _ = capture "v_to_list_SOME_typed" "v_to_list_SOME";
val _ = capture "v_to_list_NONE_typed" "v_to_list_NONE";
val _ = emit "simple_state_rel_FLOOKUP_refs_IMP_typed" "simple_state_rel_FLOOKUP_refs_IMP";
val _ = capture "refs_ffi_lemma_typed" "refs_ffi_lemma";
val _ = capture "result_rel_Rval2_typed" "result_rel_Rval2";
val _ = capture "PAIR_REL_SIMP_typed" "PAIR_REL_SIMP";
val _ = emit "LIST_REL_REFL_EVERY_typed" "LIST_REL_REFL_EVERY";
val _ = emit "POS_INT_EQ_NUM_typed" "POS_INT_EQ_NUM";
val _ = emit "simple_val_rel_Boolv_typed" "simple_val_rel_Boolv";
val _ = emit "simple_compile_state_rel_def_typed" "simple_compile_state_rel_def";
val _ = emit "val_rel_to_words_lemma_typed" "val_rel_to_words_lemma";
val _ = emit "simple_val_rel_do_install_typed" "simple_val_rel_do_install";
val _ = emit "LIST_REL_LAST_typed" "LIST_REL_LAST";
val _ = capture "FST_EQ_LEMMA_typed" "FST_EQ_LEMMA";
val _ = emit "initial_state_max_app_typed" "initial_state_max_app";
val _ = emit "eval_sim_def_typed" "eval_sim_def";
val _ = capture "initial_state_with_clock_typed" "initial_state_with_clock";
val _ = emit "IMP_semantics_eq_typed" "IMP_semantics_eq";
val _ = emit "IMP_semantics_eq_no_fail_typed" "IMP_semantics_eq_no_fail";
val _ = emit "semantics_CURRY_I_gen_typed" "semantics_CURRY_I_gen";
val _ = emit "semantics_nil_typed" "semantics_nil";
val _ = emit "find_code_SUBMAP_typed" "find_code_SUBMAP";
val _ = emit "find_code_SUBMAP_rel_typed" "find_code_SUBMAP_rel";
val _ = emit "SUBMAP_rel_EX_typed" "SUBMAP_rel_EX";
val _ = emit "do_install_SUBMAP_typed" "do_install_SUBMAP";
val _ = emit "do_app_SUBMAP_Rerr_typed" "do_app_SUBMAP_Rerr";
val _ = emit "do_app_SUBMAP_Rval_typed" "do_app_SUBMAP_Rval";
val _ = capture "SUBMAP_refs_clocks_eqs_typed" "SUBMAP_refs_clocks_eqs";
val _ = capture "SUBMAP_dec_clock_typed" "SUBMAP_dec_clock";
val _ = emit "app_call_dests_cons_typed" "app_call_dests_cons";
val _ = emit "any_dest_cons_typed" "any_dest_cons";
val _ = emit "call_dest_cons_typed" "call_dest_cons";
val _ = emit "app_dest_cons_typed" "app_dest_cons";
val _ = emit "any_dest_append_typed" "any_dest_append";
val _ = emit "call_dest_append_typed" "call_dest_append";
val _ = emit "app_dest_append_typed" "app_dest_append";
val _ = emit "app_call_dests_map_typed" "app_call_dests_map";
val _ = emit "any_dests_call_dests_app_dests_typed" "any_dests_call_dests_app_dests";
val _ = emit "get_code_labels_code_locs_typed" "get_code_labels_code_locs";
val _ = emit "initial_state_clock_typed" "initial_state_clock";
