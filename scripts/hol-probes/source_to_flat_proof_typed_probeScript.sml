load "preamble";
load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open source_to_flatProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="source_to_flatProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/source_to_flatProofScript.sml";

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

(* SML antiquotation `^x` splices the term bound by `val x = ...` in the source
   script. Deleting the marker loses the type constraint the spliced term
   carries and unlinks type variables that the splice shares between conjuncts
   (e.g. source_to_flatProof's `val s_i1 = ``s_i1 : ('f_orac_st, 'ffi)
   flatSem$state``;` is spliced into both conjuncts of pmatch). Expand each
   splice to the bound term instead; a splice whose binding is not recognised
   is left intact, so the re-parse fails loudly rather than silently weakening
   the captured statement. *)
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

  (* ``term`` or curly-quoted “term” (UTF-8), possibly spanning lines *)
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

  (* the `val name = ...` chunk, joined across lines until the term closes *)
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

  (* `rand ``l = r`` ` splices the right-hand side of the equation *)
  fun after_last_eq q =
    let
      fun go acc [] = String.implode (List.rev acc)
        | go acc (#" " :: #"=" :: #" " :: rest) = go [] rest
        | go acc (c :: rest) = go (c :: acc) rest
    in lead_trim (go [] (String.explode q)) end;

  (* the type written in `x : ty`, or in `mk_var ("x", ``: ty``)` *)
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
          let
            fun from_type_of () =
              case Substring.position "type_of " (Substring.full body) of
                (_, rhs) =>
                  if Substring.isEmpty rhs then NONE
                  else
                    let
                      val rest = Substring.string
                        (Substring.triml (String.size "type_of ") rhs)
                      val ys = String.tokens
                        (fn c => not (Char.isAlphaNum c) andalso c <> #"_") rest
                    in
                      case ys of
                        [] => NONE
                      | (y :: _) =>
                          (case chunk_for lines y of
                             NONE => NONE
                           | SOME yb => type_text yb)
                    end
          in
            case type_text body of
              SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
            | NONE =>
                (case from_type_of () of
                   SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
                 | NONE => NONE)
          end
        else if String.isPrefix "rand" (lead_trim body) then
          (case quoted body of
             SOME q => SOME ("(" ^ after_last_eq q ^ ")")
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


val _ = emit_exported "ALL_DISJOINT_CONS_typed" "ALL_DISJOINT_CONS";
val _ = emit_exported "ALL_DISJOINT_DEF_typed" "ALL_DISJOINT_DEF";
val _ = emit_exported "ALL_DISJOINT_MOVE_typed" "ALL_DISJOINT_MOVE";
val _ = emit_exported "ALL_DISJOINT_SUBSETS_typed" "ALL_DISJOINT_SUBSETS";
val _ = emit_exported "ALL_DISJOINT_elem_typed" "ALL_DISJOINT_elem";
val _ = emit_exported "ALOOKUP_MAP_3_typed" "ALOOKUP_MAP_3";
val _ = capture "ALOOKUP_alloc_defs_typed" "ALOOKUP_alloc_defs";
val _ = capture "ALOOKUP_alloc_defs_EL_typed" "ALOOKUP_alloc_defs_EL";
val _ = emit_exported "Boolv_11_typed" "Boolv_11";
val _ = emit_exported "EL_APPEND_IF_typed" "EL_APPEND_IF";
val _ = capture "EL_add_SOME_SOME_typed" "EL_add_SOME_SOME";
val _ = emit_exported "FILTER_MAPi_ID_typed" "FILTER_MAPi_ID";
val _ = capture "FST_PAIR_MAP_I_typed" "FST_PAIR_MAP_I";
val _ = capture "FST_SND_EQ_CASE_typed" "FST_SND_EQ_CASE";
val _ = emit_exported "LIST_REL_IMP_EL_typed" "LIST_REL_IMP_EL";
val _ = emit_exported "LIST_REL_IMP_EL2_typed" "LIST_REL_IMP_EL2";
val _ = emit_exported "LIST_REL_sv_rel_weak_typed" "LIST_REL_sv_rel_weak";
val _ = emit_exported "MAPi_SNOC_typed" "MAPi_SNOC";
val _ = capture "NOT_NULL_EQ_typed" "NOT_NULL_EQ";
val _ = capture "SND_eq_typed" "SND_eq";
val _ = emit_exported "SUB_BAG_IMP_typed" "SUB_BAG_IMP";
val _ = capture "abort_compile_dec_result_typed" "abort_compile_dec_result";
val _ = emit_exported "abort_def_typed" "abort_def";
val _ = emit_exported "abort_simps_typed" "abort_simps";
val _ = emit_exported "alloc_tags1_imp_typed" "alloc_tags1_imp";
val _ = emit_exported "alloc_tags_invariant_typed" "alloc_tags_invariant";
val _ = emit_exported "bind_locals_def_typed" "bind_locals_def";
val _ = emit_exported "bind_locals_fold_nsBind_typed" "bind_locals_fold_nsBind";
val _ = capture "build_tdefs_no_mod_typed" "build_tdefs_no_mod";
val _ = emit_exported "can_pmatch_all_IMP_pmatch_rows_typed" "can_pmatch_all_IMP_pmatch_rows";
val _ = emit_exported "check_type_IMP_v_rel_typed" "check_type_IMP_v_rel";
val _ = emit_exported "check_type_v_rel_MAP_flat_to_v_typed" "check_type_v_rel_MAP_flat_to_v";
val _ = emit_exported "check_type_v_rel_flat_to_v_typed" "check_type_v_rel_flat_to_v";
val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = emit_exported "compile_decs_elist_globals_typed" "compile_decs_elist_globals";
val _ = emit_exported "compile_decs_env_gen_inv_typed" "compile_decs_env_gen_inv";
val _ = emit_exported "compile_decs_esgc_free_typed" "compile_decs_esgc_free";
val _ = emit_exported "compile_decs_future_rel_typed" "compile_decs_future_rel";
val _ = emit_exported "compile_decs_generation_typed" "compile_decs_generation";
val _ = emit_exported "compile_decs_idx_prev_typed" "compile_decs_idx_prev";
val _ = emit_exported "compile_decs_num_bindings_typed" "compile_decs_num_bindings";
val _ = emit_exported "compile_esgc_free_typed" "compile_esgc_free";
val _ = emit_exported "compile_exp_esgc_free_typed" "compile_exp_esgc_free";
val _ = capture "compile_exps_length_typed" "compile_exps_length";
val _ = emit_exported "compile_flat_correct_typed" "compile_flat_correct";
val _ = emit_exported "compile_flat_esgc_free_typed" "compile_flat_esgc_free";
val _ = emit_exported "compile_flat_sub_bag_typed" "compile_flat_sub_bag";
val _ = emit_exported "compile_funs_dom2_typed" "compile_funs_dom2";
val _ = emit_exported "compile_globals_BAG_ALL_DISTINCT_typed" "compile_globals_BAG_ALL_DISTINCT";
val _ = emit_exported "compile_no_Mat_typed" "compile_no_Mat";
val _ = emit_exported "compile_prog_correct_typed" "compile_prog_correct";
val _ = emit_exported "compile_prog_esgc_free_typed" "compile_prog_esgc_free";
val _ = emit_exported "compile_prog_semantics_typed" "compile_prog_semantics";
val _ = emit_exported "compile_semantics_typed" "compile_semantics";
val _ = capture "ctor_same_type_SND_typed" "ctor_same_type_SND";
val _ = capture "ctor_same_type_refl_typed" "ctor_same_type_refl";
val _ = emit_exported "declare_env_store_env_id_typed" "declare_env_store_env_id";
val _ = capture "do_app_typed" "do_app";
val _ = capture "do_app_rec_help_typed" "do_app_rec_help";
val _ = capture "do_arith_INL_typed" "do_arith_INL";
val _ = capture "do_arith_INR_typed" "do_arith_INR";
val _ = capture "do_conversion_INL_typed" "do_conversion_INL";
val _ = capture "do_conversion_INR_typed" "do_conversion_INR";
val _ = capture "do_eq_typed" "do_eq";
val _ = emit_exported "do_eval_typed" "do_eval";
val _ = capture "do_opapp_typed" "do_opapp";
val _ = capture "do_test_lemma_typed" "do_test_lemma";
val _ = capture "drestrict_lem_typed" "drestrict_lem";
val _ = capture "drop_4_via_el_typed" "drop_4_via_el";
val _ = emit_exported "env_all_rel_typed" "env_all_rel_rules";
val _ = emit_exported "env_all_rel_cases_typed" "env_all_rel_cases";
val _ = capture "env_all_rel_weak_typed" "env_all_rel_weak";
val _ = capture "env_domain_eq_append_typed" "env_domain_eq_append";
val _ = emit_exported "env_domain_eq_def_typed" "env_domain_eq_def";
val _ = emit_exported "env_gen_future_rel_def_typed" "env_gen_future_rel_def";
val _ = emit_exported "env_gen_future_rel_forward_typed" "env_gen_future_rel_forward";
val _ = emit_exported "env_gen_inv_def_typed" "env_gen_inv_def";
val _ = emit_exported "env_gen_rel_def_typed" "env_gen_rel_def";
val _ = emit_exported "env_rel_LIST_REL_typed" "env_rel_LIST_REL";
val _ = capture "env_rel_append_typed" "env_rel_append";
val _ = emit_exported "env_rel_bind_one_typed" "env_rel_bind_one";
val _ = capture "env_rel_dom_typed" "env_rel_dom";
val _ = capture "env_rel_el_typed" "env_rel_el";
val _ = capture "env_rel_lookup_typed" "env_rel_lookup";
val _ = capture "env_rel_one_typed" "env_rel_one";
val _ = emit_exported "env_rel_weak_typed" "env_rel_weak";
val _ = emit_exported "env_store_inv_def_typed" "env_store_inv_def";
val _ = capture "env_updated_lem_typed" "env_updated_lem";
val _ = capture "eta2_typed" "eta2";
val _ = emit_exported "eval_ref_inv_def_typed" "eval_ref_inv_def";
val _ = emit_exported "eval_state_call_rel_def_typed" "eval_state_call_rel_def";
val _ = emit_exported "eval_state_call_rel_refl_typed" "eval_state_call_rel_refl";
val _ = emit_exported "eval_state_call_rel_trans_typed" "eval_state_call_rel_trans";
val _ = emit_exported "evaluate_Bool_typed" "evaluate_Bool";
val _ = capture "evaluate_foldr_let_err_typed" "evaluate_foldr_let_err";
val _ = capture "evaluate_make_varls_typed" "evaluate_make_varls";
val _ = emit_exported "fin_idx_match_def_typed" "fin_idx_match_def";
val _ = capture "find_recfun_typed" "find_recfun";
val _ = capture "flookup_funion_submap_typed" "flookup_funion_submap";
val _ = capture "fst_lem_typed" "fst_lem";
val _ = capture "funion_submap_typed" "funion_submap";
val _ = emit_exported "genv_allocated_idxs_def_typed" "genv_allocated_idxs_def";
val _ = emit_exported "genv_c_ok_def_typed" "genv_c_ok_def";
val _ = emit_exported "genv_c_ok_extend_typed" "genv_c_ok_extend";
val _ = emit_exported "genv_c_ok_pmatch_stamps_ok_typed" "genv_c_ok_pmatch_stamps_ok";
val _ = emit_exported "genv_c_ok_same_type_FST_eq_imp_same_ctor_typed" "genv_c_ok_same_type_FST_eq_imp_same_ctor";
val _ = emit_exported "genv_c_tys_ok_def_typed" "genv_c_tys_ok_def";
val _ = emit_exported "genv_c_tys_ok_extend_typed" "genv_c_tys_ok_extend";
val _ = emit_exported "genv_lookup_cons_typed" "genv_lookup_cons";
val _ = emit_exported "genv_lookup_nil_typed" "genv_lookup_nil";
val _ = capture_dt "global_env_typed" (mk_type ("global_env", []));
val _ = capture "global_env_inv_add_locals_typed" "global_env_inv_add_locals";
val _ = capture "global_env_inv_append_typed" "global_env_inv_append";
val _ = capture "global_env_inv_extend_typed" "global_env_inv_extend";
val _ = capture "global_env_inv_extend2_typed" "global_env_inv_extend2";
val _ = emit_exported "global_env_inv_weak_typed" "global_env_inv_weak";
val _ = emit_exported "has_bools_def_typed" "has_bools_def";
val _ = emit_exported "has_exns_def_typed" "has_exns_def";
val _ = emit_exported "has_lists_def_typed" "has_lists_def";
val _ = emit_exported "idx_block_def_typed" "idx_block_def";
val _ = emit_exported "idx_block_union_final_typed" "idx_block_union_final";
val _ = emit_exported "idx_final_block_def_typed" "idx_final_block_def";
val _ = emit_exported "idx_prev_def_typed" "idx_prev_def";
val _ = emit_exported "idx_prev_refl_typed" "idx_prev_refl";
val _ = emit_exported "idx_prev_trans_typed" "idx_prev_trans";
val _ = emit_exported "idx_range_rel_def_typed" "idx_range_rel_def";
val _ = emit_exported "idx_range_rel_v_REPLICATE_NONE_typed" "idx_range_rel_v_REPLICATE_NONE";
val _ = emit_exported "idx_range_shrink_typed" "idx_range_shrink";
val _ = capture_dt "idx_types_typed" (mk_type ("idx_types", []));
val _ = emit_exported "idx_types_FORALL_typed" "idx_types_FORALL";
val _ = emit_exported "inc_compile_esgc_free_typed" "inc_compile_esgc_free";
val _ = emit_exported "inc_compile_globals_BAG_ALL_DISTINCT_typed" "inc_compile_globals_BAG_ALL_DISTINCT";
val _ = emit_exported "inc_compile_no_Mat_typed" "inc_compile_no_Mat";
val _ = emit_exported "inc_compile_prog_env_submap_typed" "inc_compile_prog_env_submap";
val _ = emit_exported "inc_compile_prog_esgc_free_typed" "inc_compile_prog_esgc_free";
val _ = emit_exported "inc_compile_prog_idx_prev_typed" "inc_compile_prog_idx_prev";
val _ = emit_exported "inc_compile_prog_nonempty_typed" "inc_compile_prog_nonempty";
val _ = emit_exported "init_eval_state_ok_def_typed" "init_eval_state_ok_def";
val _ = emit_exported "init_genv_def_typed" "init_genv_def";
val _ = emit_exported "init_genv_els_def_typed" "init_genv_els_def";
val _ = emit_exported "init_genv_next_typed" "init_genv_next";
val _ = emit_exported "init_genv_ok_typed" "init_genv_ok";
val _ = emit_exported "init_genv_ty_els_def_typed" "init_genv_ty_els_def";
val _ = emit_exported "init_genv_tys_ok_typed" "init_genv_tys_ok";
val _ = emit_exported "init_global_env_inv_def_typed" "init_global_env_inv_def";
val _ = emit_exported "init_global_env_inv_imp_typed" "init_global_env_inv_imp";
val _ = emit_exported "invariant_IMP_s_rel_typed" "invariant_IMP_s_rel";
val _ = emit_exported "invariant_begin_alloc_blanks_typed" "invariant_begin_alloc_blanks";
val _ = emit_exported "invariant_change_clock_typed" "invariant_change_clock";
val _ = emit_exported "invariant_change_eval_ref_typed" "invariant_change_eval_ref";
val _ = emit_exported "invariant_dec_clock_typed" "invariant_dec_clock";
val _ = emit_exported "invariant_def_typed" "invariant_def";
val _ = emit_exported "invariant_end_eval_typed" "invariant_end_eval";
val _ = capture "invariant_env_gen_inv_typed" "invariant_env_gen_inv";
val _ = emit_exported "invariant_genv_c_ok_typed" "invariant_genv_c_ok";
val _ = emit_exported "invariant_globals_typed" "invariant_globals";
val _ = emit_exported "invariant_idx_range_shrink_typed" "invariant_idx_range_shrink";
val _ = emit_exported "invariant_idx_range_shrink_gen_typed" "invariant_idx_range_shrink_gen";
val _ = emit_exported "invariant_make_varls_typed" "invariant_make_varls";
val _ = emit_exported "keep_glob_alloc_typed" "keep_glob_alloc";
val _ = emit_exported "list_to_v_v_rel_typed" "list_to_v_v_rel";
val _ = capture "lookup_build_rec_env_lem_typed" "lookup_build_rec_env_lem";
val _ = emit_exported "make_varls_esgc_free_typed" "make_varls_esgc_free";
val _ = emit_exported "mapi_map_typed" "mapi_map";
val _ = emit_exported "match_result_rel_def_typed" "match_result_rel_def";
val _ = emit_exported "match_result_rel_imp_typed" "match_result_rel_imp";
val _ = emit_exported "maybe_all_list_SOME_typed" "maybe_all_list_SOME";
val _ = capture "mem_size_lemma_typed" "mem_size_lemma";
val _ = emit_exported "monotonic_globals_state_co_compile_typed" "monotonic_globals_state_co_compile";
val _ = capture "not_abort_IMP_cases_typed" "not_abort_IMP_cases";
val _ = emit_exported "nsAll_extend_env_typed" "nsAll_extend_env";
val _ = capture "nsAppend_bind_locals_typed" "nsAppend_bind_locals";
val _ = capture "nsAppend_foldl_typed" "nsAppend_foldl";
val _ = capture "nsAppend_foldl_prime_typed" "nsAppend_foldl'";
val _ = capture "nsBindList_pat_tups_bind_locals_typed" "nsBindList_pat_tups_bind_locals";
val _ = emit_exported "nsLookup_nsBind_If_typed" "nsLookup_nsBind_If";
val _ = emit_exported "num_bindings_def_typed" "num_bindings_def";
val _ = emit_exported "op_gbag_astOp_to_flatOp_typed" "op_gbag_astOp_to_flatOp";
val _ = capture "opt_bind_lem_typed" "opt_bind_lem";
val _ = capture "opt_case_bool_eq_typed" "opt_case_bool_eq";
val _ = emit_exported "orac_config_envs_subspt_def_typed" "orac_config_envs_subspt_def";
val _ = emit_exported "orac_config_envs_subspt_refl_typed" "orac_config_envs_subspt_refl";
val _ = emit_exported "orac_config_envs_subspt_trans_typed" "orac_config_envs_subspt_trans";
val _ = emit_exported "orac_forward_rel_def_typed" "orac_forward_rel_def";
val _ = emit_exported "orac_forward_rel_refl_typed" "orac_forward_rel_refl";
val _ = emit_exported "orac_forward_rel_trans_typed" "orac_forward_rel_trans";
val _ = emit_exported "orac_rel_SOME_eval_typed" "orac_rel_SOME_eval";
val _ = emit_exported "orac_rel_def_typed" "orac_rel_def";
val _ = emit_exported "orac_rel_inner_def_typed" "orac_rel_inner_def";
val _ = emit_exported "pat_bindings_compile_pat_typed" "pat_bindings_compile_pat";
val _ = capture "pmatch_typed" "pmatch";
val _ = emit_exported "pmatch_invariant_typed" "pmatch_invariant";
val _ = capture "pmatch_rows_drop_4_typed" "pmatch_rows_drop_4";
val _ = emit_exported "precondition1_change_clock_typed" "precondition1_change_clock";
val _ = emit_exported "precondition1_def_typed" "precondition1_def";
val _ = emit_exported "precondition_def_typed" "precondition_def";
val _ = capture "precondition_stamp_helper_typed" "precondition_stamp_helper";
val _ = emit_exported "result_rel_typed" "result_rel_rules";
val _ = capture "result_rel_eqns_typed" "result_rel_eqns";
val _ = emit_exported "s_rel_typed" "s_rel_rules";
val _ = capture "sem_env_eq_lemma_typed" "sem_env_eq_lemma";
val _ = emit_exported "set_globals_make_varls_typed" "set_globals_make_varls";
val _ = emit_exported "some_f_inj_eq_typed" "some_f_inj_eq";
val _ = emit_exported "src_orac_env_invs_def_typed" "src_orac_env_invs_def";
val _ = emit_exported "src_orac_env_invs_lookup_env_typed" "src_orac_env_invs_lookup_env";
val _ = emit_exported "src_orac_gen_inv_def_typed" "src_orac_gen_inv_def";
val _ = emit_exported "src_orac_invs_def_typed" "src_orac_invs_def";
val _ = emit_exported "src_orac_invs_weak_typed" "src_orac_invs_weak";
val _ = emit_exported "src_orac_next_cfg_def_typed" "src_orac_next_cfg_def";
val _ = emit_exported "src_orac_next_cfg_inner_def_typed" "src_orac_next_cfg_inner_def";
val _ = emit_exported "src_orac_step_invs_def_typed" "src_orac_step_invs_def";
val _ = capture "step_1_typed" "step_1";
val _ = emit_exported "subglobals_NONE_typed" "subglobals_NONE";
val _ = emit_exported "subglobals_add_NONE_typed" "subglobals_add_NONE";
val _ = emit_exported "subglobals_def_typed" "subglobals_def";
val _ = capture "subglobals_refl_typed" "subglobals_refl";
val _ = capture "subglobals_refl_append_typed" "subglobals_refl_append";
val _ = capture "subglobals_trans_typed" "subglobals_trans";
val _ = emit_exported "submap_distinct_fupdate_flookup_typed" "submap_distinct_fupdate_flookup";
val _ = emit_exported "submap_fupdate_flookup_typed" "submap_fupdate_flookup";
val _ = emit_exported "sv_rel_typed" "sv_rel_rules";
val _ = capture "sv_rel_weak_typed" "sv_rel_weak";
val _ = emit_exported "v_rel_typed" "v_rel_rules";
val _ = emit_exported "v_rel_Bool_eqn_typed" "v_rel_Bool_eqn";
val _ = emit_exported "v_rel_cases_typed" "v_rel_cases";
val _ = emit_exported "v_rel_check_type_typed" "v_rel_check_type";
val _ = emit_exported "v_rel_global_eqn_typed" "v_rel_global_eqn";
val _ = emit_exported "v_rel_ind_typed" "v_rel_ind";
val _ = capture "v_rel_lems_typed" "v_rel_lems";
val _ = emit_exported "v_rel_more_eqns_typed" "v_rel_more_eqns";
val _ = emit_exported "v_rel_weak_typed" "v_rel_weak";
val _ = capture "v_rel_weakening_typed" "v_rel_weakening";
val _ = capture "v_rel_weakening2_typed" "v_rel_weakening2";
val _ = capture "v_to_char_list_typed" "v_to_char_list";
val _ = capture "v_to_list_typed" "v_to_list";
val _ = emit_exported "v_to_word64_list_rel_typed" "v_to_word64_list_rel";
val _ = emit_exported "v_to_word8_list_rel_typed" "v_to_word8_list_rel";
val _ = capture "vs_to_string_typed" "vs_to_string";

(* Derived local theorems, replayed exactly as the source derives them. *)
val local_v_rel_eqns =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
    ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
    ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
    ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ;
val _ = emit_as "compile_flat_BAG_ALL_DISTINCT_typed"
  (MATCH_MP (fetch_other ("bag","BAG_ALL_DISTINCT_SUB_BAG")
      |> REWRITE_RULE [GSYM AND_IMP_INTRO])
    (fetch_other ("source_to_flatProof","compile_flat_sub_bag")));
val _ = emit_as "v_rel_eqns_typed" local_v_rel_eqns;
val _ = emit_as "v_rel_eqns_non_global_typed"
  (local_v_rel_eqns
  |> BODY_CONJUNCTS
  |> filter (null o find_terms (can (match_term ``global_env_inv``)) o concl)
  |> map GEN_ALL
  |> LIST_CONJ);
