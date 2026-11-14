(* Typed captures for the pan_globalsProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   123 names: 99 exported (fetched from the theory DB), 24 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 0 derived local theorems captured through
   their base statement, 0 datatypes.
*)
load "preamble";
load "pan_globalsProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pan_globalsProofTheory;
open panSemTheory pan_globalsTheory panPropsTheory panLangTheory stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pan_globalsProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

fun emit_as label th = emit label th;

fun fetch_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => th;

fun emit_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => emit (name ^ "_typed") th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_globalsProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;

fun after_prefix pre s =
  case Substring.position pre (Substring.full s) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);

fun statement_of name =
  let
    val header = after_prefix ("\nTheorem " ^ name) source_text
    val rest = after_prefix ":\n" header
    val (stmt, _) = Substring.position "\nProof" (Substring.full rest)
  in Substring.string stmt end;

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

fun capture_dt label (thy,ctor) =
  let
    val ty = type_of (prim_mk_const {Thy=thy,Name=ctor})
    val cs = TypeBase.constructors_of ty
  in
    print (label ^ "=");
    print (String.concatWith "; "
      (map (fn c => let val (n,t) = dest_const c
         in n ^ ":" ^ type_to_string t end) cs));
    print "\n"
  end;

val _ = emit_exported "ALL_DISTINCT_compile_top_typed" "ALL_DISTINCT_compile_top";
val _ = emit_exported "ALL_DISTINCT_fperm_decs_typed" "ALL_DISTINCT_fperm_decs";
val _ = emit_exported "DISJOINT_addresses_lemma_typed" "DISJOINT_addresses_lemma";
val _ = emit_exported "FILTER_decs_fperm_decs_typed" "FILTER_decs_fperm_decs";
val _ = emit_exported "FLOOKUP_fperm_code_typed" "FLOOKUP_fperm_code";
val _ = emit_exported "FLOOKUP_fperm_code_prime_typed" "FLOOKUP_fperm_code'";
val _ = emit_exported "FLOOKUP_globals_val_state_rel_typed" "FLOOKUP_globals_val_state_rel";
val _ = emit_exported "OPT_MMAP_eval_correct_typed" "OPT_MMAP_eval_correct";
val _ = emit_exported "OPT_MMAP_eval_fresh_var_typed" "OPT_MMAP_eval_fresh_var";
val _ = emit_exported "OPT_MMAP_eval_two_fresh_vars_typed" "OPT_MMAP_eval_two_fresh_vars";
val _ = emit_exported "byte_aligned_bytes_in_word_mul_typed" "byte_aligned_bytes_in_word_mul";
val _ = emit_exported "byte_aligned_mul_bytes_in_word_typed" "byte_aligned_mul_bytes_in_word";
val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = emit_exported "compile_decls_append_typed" "compile_decls_append";
val _ = emit_exported "compile_decs_EVERY_typed" "compile_decs_EVERY";
val _ = emit_exported "compile_decs_EVERY_is_function_typed" "compile_decs_EVERY_is_function";
val _ = emit_exported "compile_decs_FILTER_decs_typed" "compile_decs_FILTER_decs";
val _ = emit_exported "compile_decs_decls_thm_typed" "compile_decs_decls_thm";
val _ = emit_exported "compile_decs_exns_are_exns_typed" "compile_decs_exns_are_exns";
val _ = emit_exported "compile_decs_functions_thm_typed" "compile_decs_functions_thm";
val _ = emit_exported "compile_decs_localised_typed" "compile_decs_localised";
val _ = emit_exported "compile_decs_localised_prime_typed" "compile_decs_localised'";
val _ = emit_exported "compile_decs_localised_main_typed" "compile_decs_localised_main";
val _ = emit_exported "compile_decs_preserve_functions_typed" "compile_decs_preserve_functions";
val _ = emit_exported "compile_exp_correct_typed" "compile_exp_correct";
val _ = emit_exported "compile_exp_localised_typed" "compile_exp_localised";
val _ = emit_exported "compile_localised_typed" "compile_localised";
val _ = emit_exported "compile_top_localised_typed" "compile_top_localised";
val _ = emit_exported "compile_top_only_functions_or_exns_typed" "compile_top_only_functions_or_exns";
val _ = emit_exported "compile_top_semantics_decls_typed" "compile_top_semantics_decls";
val _ = emit_exported "dec_shapes_FILTER_typed" "dec_shapes_FILTER";
val _ = emit_exported "dec_shapes_append_typed" "dec_shapes_append";
val _ = emit_exported "dec_shapes_fperm_decs_typed" "dec_shapes_fperm_decs";
val _ = emit_exported "dec_shapes_functions_typed" "dec_shapes_functions";
val _ = emit_exported "dec_shapes_resort_decls_def_typed" "dec_shapes_resort_decls_def";
val _ = emit_exported "decl_distinct_typed" "decl_distinct";
val _ = emit_exported "disjoint_globals_def_typed" "disjoint_globals_def";
val _ = emit_exported "eval_shape_val_NONE_typed" "eval_shape_val_NONE";
val _ = emit_exported "eval_shape_val_thm_typed" "eval_shape_val_thm";
val _ = emit_exported "eval_upd_code_eta_typed" "eval_upd_code_eta";
val _ = emit_exported "evaluate_decls_compile_top_typed" "evaluate_decls_compile_top";
val _ = emit_exported "evaluate_decls_fperm_typed" "evaluate_decls_fperm";
val _ = emit_exported "evaluate_decls_init_globals_lemma_typed" "evaluate_decls_init_globals_lemma";
val _ = emit_exported "evaluate_fperm_typed" "evaluate_fperm";
val _ = emit_exported "evaluate_fperm_prime_typed" "evaluate_fperm'";
val _ = emit_exported "evaluate_fresh_local_typed" "evaluate_fresh_local";
val _ = emit_exported "evaluate_unchanged_local_typed" "evaluate_unchanged_local";
val _ = emit_exported "exceptions_FILTER_is_function_typed" "exceptions_FILTER_is_function";
val _ = emit_exported "exceptions_append_typed" "exceptions_append";
val _ = emit_exported "exceptions_compile_top_typed" "exceptions_compile_top";
val _ = emit_exported "fperm_code_FEMPTY_typed" "fperm_code_FEMPTY";
val _ = emit_exported "fperm_code_FUPDATE_LIST_functions_typed" "fperm_code_FUPDATE_LIST_functions";
val _ = emit_exported "fperm_code_def_typed" "fperm_code_def";
val _ = emit_exported "fperm_decs_FILTER_is_function_typed" "fperm_decs_FILTER_is_function";
val _ = emit_exported "fperm_decs_append_typed" "fperm_decs_append";
val _ = emit_exported "fperm_decs_decls_typed" "fperm_decs_decls";
val _ = emit_exported "fperm_name_cancel_typed" "fperm_name_cancel";
val _ = emit_exported "fperm_name_cong_typed" "fperm_name_cong";
val _ = emit_exported "fresh_name_correct_typed" "fresh_name_correct";
val _ = emit_exported "fresh_name_correct_prime_typed" "fresh_name_correct'";
val _ = emit_exported "functions_FILTER_exn_decl_typed" "functions_FILTER_exn_decl";
val _ = emit_exported "functions_FILTER_is_name_typed" "functions_FILTER_is_name";
val _ = emit_exported "functions_fperm_decs_typed" "functions_fperm_decs";
val _ = emit_exported "good_dimindex_w2n_add_typed" "good_dimindex_w2n_add";
val _ = emit_exported "good_res_def_typed" "good_res_def";
val _ = emit_exported "localised_exp_shape_val_typed" "localised_exp_shape_val";
val _ = emit_exported "lookup_code_fperm_code_typed" "lookup_code_fperm_code";
val _ = emit_exported "mem_load_disjoint_typed" "mem_load_disjoint";
val _ = emit_exported "mem_load_mem_store_typed" "mem_load_mem_store";
val _ = emit_exported "mem_stores_addrs_IS_SOME_typed" "mem_stores_addrs_IS_SOME";
val _ = emit_exported "mem_stores_append_typed" "mem_stores_append";
val _ = emit_exported "mem_stores_bounded_length_typed" "mem_stores_bounded_length";
val _ = emit_exported "mem_stores_load_disjoint_typed" "mem_stores_load_disjoint";
val _ = emit_exported "mem_stores_lookup_typed" "mem_stores_lookup";
val _ = emit_exported "mem_stores_mem_load_back_typed" "mem_stores_mem_load_back";
val _ = emit_exported "mem_stores_memory_swap_typed" "mem_stores_memory_swap";
val _ = emit_exported "nested_seqs_localised_typed" "nested_seqs_localised";
val _ = emit_exported "new_main_name_correct_typed" "new_main_name_correct";
val _ = emit_exported "not_is_function_typed" "not_is_function";
val _ = emit_exported "res_var_FEMPTY_typed" "res_var_FEMPTY";
val _ = emit_exported "resort_decls_evaluate_typed" "resort_decls_evaluate";
val _ = emit_exported "resort_decls_preserve_functions_typed" "resort_decls_preserve_functions";
val _ = emit_exported "semantics_empty_locals_typed" "semantics_empty_locals";
val _ = emit_exported "semantics_fperm_typed" "semantics_fperm";
val _ = emit_exported "semantics_init_call_typed" "semantics_init_call";
val _ = emit_exported "semantics_init_call_prime_typed" "semantics_init_call'";
val _ = emit_exported "state_rel_change_ffi_typed" "state_rel_change_ffi";
val _ = emit_exported "state_rel_change_locals_typed" "state_rel_change_locals";
val _ = emit_exported "state_rel_def_typed" "state_rel_def";
val _ = emit_exported "state_rel_empty_locals_typed" "state_rel_empty_locals";
val _ = emit_exported "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit_exported "state_rel_lookup_code_typed" "state_rel_lookup_code";
val _ = emit_exported "state_rel_mem_load_typed" "state_rel_mem_load";
val _ = emit_exported "state_rel_mem_store_byte_typed" "state_rel_mem_store_byte";
val _ = emit_exported "state_rel_memory_update_typed" "state_rel_memory_update";
val _ = emit_exported "state_rel_read_bytearray_typed" "state_rel_read_bytearray";
val _ = emit_exported "state_rel_set_var_typed" "state_rel_set_var";
val _ = emit_exported "state_rel_write_bytearray_typed" "state_rel_write_bytearray";
val _ = emit_exported "w2n_add_alt_typed" "w2n_add_alt";
val _ = capture "EVERY_fperm_decs_typed" "EVERY_fperm_decs";
val _ = capture "LESS_MULT_MONO_prime_typed" "LESS_MULT_MONO'";
val _ = capture "LUB_IMAGE_SUC_typed" "LUB_IMAGE_SUC";
val _ = capture "MEM_functions_typed" "MEM_functions";
val _ = capture "compile_decls_append_IMP_typed" "compile_decls_append_IMP";
val _ = capture "compile_top_shape_wf_typed" "compile_top_shape_wf";
val _ = capture "compile_top_shape_wf_nil_typed" "compile_top_shape_wf_nil";
val _ = capture "eval_state_rel_is_wf_shape_typed" "eval_state_rel_is_wf_shape";
val _ = capture "evaluate_decls_functions_wf_typed" "evaluate_decls_functions_wf";
val _ = capture "evaluate_decls_one_fun_last_typed" "evaluate_decls_one_fun_last";
val _ = capture "evaluate_decls_only_functions_SOME_typed" "evaluate_decls_only_functions_SOME";
val _ = capture "evaluate_decls_only_functions_and_exns_SOME_typed" "evaluate_decls_only_functions_and_exns_SOME";
val _ = capture "evaluate_two_typed" "evaluate_two";
val _ = capture "evaluate_two_fresh_locals_typed" "evaluate_two_fresh_locals";
val _ = capture "functions_filter_nil_typed" "functions_filter_nil";
val _ = capture "map_pick_up_first_typed" "map_pick_up_first";
val _ = capture "num_cases_lemma_typed" "num_cases_lemma";
val _ = capture "resort_decls_evaluate_IMP_typed" "resort_decls_evaluate_IMP";
val _ = capture "state_rel_dec_clock_typed" "state_rel_dec_clock";
val _ = capture "state_rel_globals_wf_typed" "state_rel_globals_wf";
val _ = capture "state_rel_res_var_typed" "state_rel_res_var";
val _ = capture "state_rel_structs_typed" "state_rel_structs";
val _ = capture "tuple_4_o_typed" "tuple_4_o";
val _ = capture "v_neq_v_prime_typed" "v_neq_v'";
