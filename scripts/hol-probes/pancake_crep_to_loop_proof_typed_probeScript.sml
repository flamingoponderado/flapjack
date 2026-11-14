(* Typed captures for the crep_to_loopProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   93 names: 71 exported (fetched from the theory DB), 18 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 3 derived local theorems captured through
   their base statement, 1 datatypes.
*)
load "preamble";
load "crep_to_loopProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open crep_to_loopProofTheory;
open listRangeTheory rich_listTheory crepPropsTheory loopPropsTheory pan_commonPropsTheory loop_liveProofTheory crepSemTheory loopLangTheory loopSemTheory pan_commonTheory crep_arithProofTheory crep_to_loopTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="crep_to_loopProof",Name=name} of
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
  (OS.Path.concat (source_cake, "pancake/proofs/crep_to_loopProofScript.sml"));
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

val _ = emit_exported "all_distinct_ctxt_lookup_all_distinct_typed" "all_distinct_ctxt_lookup_all_distinct";
val _ = emit_exported "assigned_vars_MAPi_Assign_typed" "assigned_vars_MAPi_Assign";
val _ = emit_exported "assigned_vars_nested_seq_assign_typed" "assigned_vars_nested_seq_assign";
val _ = emit_exported "call_preserve_state_code_locals_rel_typed" "call_preserve_state_code_locals_rel";
val _ = emit_exported "code_rel2_def_typed" "code_rel2_def";
val _ = emit_exported "code_rel_def_typed" "code_rel_def";
val _ = emit_exported "code_rel_evaluate_call_correct_typed" "code_rel_evaluate_call_correct";
val _ = emit_exported "code_rel_intro_typed" "code_rel_intro";
val _ = emit_exported "comp_exp_assigned_vars_tmp_bound_typed" "comp_exp_assigned_vars_tmp_bound";
val _ = emit_exported "comp_exp_assigned_vars_tmp_bound_cases_typed" "comp_exp_assigned_vars_tmp_bound_cases";
val _ = emit_exported "comp_exp_preserves_eval_typed" "comp_exp_preserves_eval";
val _ = emit_exported "comp_exps_assigned_vars_tmp_bound_typed" "comp_exps_assigned_vars_tmp_bound";
val _ = emit_exported "comp_exps_preserves_eval_typed" "comp_exps_preserves_eval";
val _ = emit_exported "compile_exp_le_tmp_domain_typed" "compile_exp_le_tmp_domain";
val _ = emit_exported "compile_exp_le_tmp_domain_cases_typed" "compile_exp_le_tmp_domain_cases";
val _ = emit_exported "compile_exp_out_rel_typed" "compile_exp_out_rel";
val _ = emit_exported "compile_exp_out_rel_cases_typed" "compile_exp_out_rel_cases";
val _ = emit_exported "compile_exps_alt_typed" "compile_exps_alt";
val _ = emit_exported "compile_exps_le_tmp_domain_typed" "compile_exps_le_tmp_domain";
val _ = emit_exported "compile_exps_out_rel_typed" "compile_exps_out_rel";
val _ = emit_exported "compile_prog_distinct_params_typed" "compile_prog_distinct_params";
val _ = emit_exported "crep_sem_is_wrapper_typed" "crep_sem_is_wrapper";
val _ = emit_exported "crep_to_loop_compile_prog_lab_min_typed" "crep_to_loop_compile_prog_lab_min";
val _ = emit_exported "ctxt_fc_def_typed" "ctxt_fc_def";
val _ = emit_exported "ctxt_max_def_typed" "ctxt_max_def";
val _ = emit_exported "cut_sets_MAPi_Assign_typed" "cut_sets_MAPi_Assign";
val _ = emit_exported "distinct_funcs_def_typed" "distinct_funcs_def";
val _ = emit_exported "distinct_make_funcs_typed" "distinct_make_funcs";
val _ = emit_exported "distinct_vars_def_typed" "distinct_vars_def";
val _ = emit_exported "evaluate_comb_seq_typed" "evaluate_comb_seq";
val _ = emit_exported "evaluate_nested_seq_append_first_typed" "evaluate_nested_seq_append_first";
val _ = emit_exported "evaluate_none_nested_seq_append_typed" "evaluate_none_nested_seq_append";
val _ = emit_exported "evaluate_not_none_nested_seq_append_typed" "evaluate_not_none_nested_seq_append";
val _ = emit_exported "first_compile_prog_all_distinct_typed" "first_compile_prog_all_distinct";
val _ = emit_exported "globals_rel_def_typed" "globals_rel_def";
val _ = emit_exported "globals_rel_intro_typed" "globals_rel_intro";
val _ = emit_exported "initial_prog_make_funcs_el_typed" "initial_prog_make_funcs_el";
val _ = emit_exported "insert_insert_eq_typed" "insert_insert_eq";
val _ = emit_exported "list_insert_SNOC_typed" "list_insert_SNOC";
val _ = emit_exported "list_insert_append_typed" "list_insert_append";
val _ = emit_exported "list_insert_insert_typed" "list_insert_insert";
val _ = emit_exported "locals_rel_cutset_prop_typed" "locals_rel_cutset_prop";
val _ = emit_exported "locals_rel_def_typed" "locals_rel_def";
val _ = emit_exported "locals_rel_insert_gt_vmax_typed" "locals_rel_insert_gt_vmax";
val _ = emit_exported "locals_rel_intro_typed" "locals_rel_intro";
val _ = emit_exported "loop_sem_is_wrapper_typed" "loop_sem_is_wrapper";
val _ = emit_exported "make_funcs_domain_compile_prog_typed" "make_funcs_domain_compile_prog";
val _ = emit_exported "map_map2_fst_typed" "map_map2_fst";
val _ = emit_exported "mem_lookup_fromalist_some_typed" "mem_lookup_fromalist_some";
val _ = emit_exported "mem_rel_def_typed" "mem_rel_def";
val _ = emit_exported "mem_rel_intro_typed" "mem_rel_intro";
val _ = emit_exported "member_cutset_survives_comp_exp_typed" "member_cutset_survives_comp_exp";
val _ = emit_exported "member_cutset_survives_comp_exp_cases_typed" "member_cutset_survives_comp_exp_cases";
val _ = emit_exported "member_cutset_survives_comp_exps_typed" "member_cutset_survives_comp_exps";
val _ = emit_exported "member_cutset_survives_comp_prog_typed" "member_cutset_survives_comp_prog";
val _ = emit_exported "mk_ctxt_code_imp_code_rel2_typed" "mk_ctxt_code_imp_code_rel2";
val _ = emit_exported "ncompile_correct_typed" "ncompile_correct";
val _ = emit_exported "not_mem_assigned_mem_gt_comp_exp_typed" "not_mem_assigned_mem_gt_comp_exp";
val _ = emit_exported "not_mem_assigned_mem_gt_comp_exp_cases_typed" "not_mem_assigned_mem_gt_comp_exp_cases";
val _ = emit_exported "not_mem_assigned_mem_gt_comp_exps_typed" "not_mem_assigned_mem_gt_comp_exps";
val _ = emit_exported "not_mem_context_assigned_mem_gt_typed" "not_mem_context_assigned_mem_gt";
val _ = emit_exported "ocompile_correct_typed" "ocompile_correct";
val _ = emit_exported "semantics_wrapper_def_typed" "semantics_wrapper_def";
val _ = emit_exported "semantics_wrapper_eq_typed" "semantics_wrapper_eq";
val _ = emit_exported "state_rel_clock_add_zero_typed" "state_rel_clock_add_zero";
val _ = emit_exported "state_rel_def_typed" "state_rel_def";
val _ = emit_exported "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit_exported "state_rel_intro_typed" "state_rel_intro";
val _ = emit_exported "survives_MAPi_Assign_typed" "survives_MAPi_Assign";
val _ = emit_exported "wlab_wloc_def_typed" "wlab_wloc_def";
val _ = emit_exported "write_bytearray_mem_rel_typed" "write_bytearray_mem_rel";
val _ = capture "ALOOKUP_EQ_EL_typed" "ALOOKUP_EQ_EL";
val _ = capture "OPT_MMAP_APPEND_typed" "OPT_MMAP_APPEND";
val _ = capture "PAIR_MAP_EQ_UNCURRY_typed" "PAIR_MAP_EQ_UNCURRY";
val _ = capture "UNCURRY_eq_case_typed" "UNCURRY_eq_case";
val _ = capture "case_le_typed" "case_le";
val _ = capture "crep_eval_upd_clock_typed" "crep_eval_upd_clock";
val _ = capture "crep_primop_loop_primop_typed" "crep_primop_loop_primop";
val _ = capture "evaluate_Seq_Skip_typed" "evaluate_Seq_Skip";
val _ = capture "evaluate_less_clock_cases_typed" "evaluate_less_clock_cases";
val _ = capture "evaluate_none_nested_seq_append_eq_typed" "evaluate_none_nested_seq_append_eq";
val _ = capture "evaluate_twice_cases_typed" "evaluate_twice_cases";
val _ = capture "find_code_collapse_cases_typed" "find_code_collapse_cases";
val _ = capture "locals_rel_inter_helper_typed" "locals_rel_inter_helper";
val _ = capture "locals_rel_lookup_same_typed" "locals_rel_lookup_same";
val _ = capture "loop_eval_upd_clock_typed" "loop_eval_upd_clock";
val _ = capture "not_mem_nlhss_lemma_typed" "not_mem_nlhss_lemma";
val _ = capture "opt_mmap_lhss_locals_rel_typed" "opt_mmap_lhss_locals_rel";
val _ = capture "opt_mmap_rhss_locals_rel_typed" "opt_mmap_rhss_locals_rel";
val _ = capture_dt "semantics_run_res_typed" ("crep_to_loopProof","RunError");

(* Derived local theorems: the base statement is captured typed under
   the derived theorem name; the derivation is named in each comment,
   so the carriers are the base statement carriers. *)
(* evaluate_io_mono_rephrases: LIST_CONJ of the two specialised io-mono statements *)
val _ = emit_as "evaluate_io_mono_rephrases_typed" (fetch_other ("crepProps","evaluate_add_clock_io_events_mono"));
val _ = emit_as "evaluate_add_clock_io_events_mono_loop_typed" (fetch_other ("loopProps","evaluate_add_clock_io_events_mono"));
(* member_cutset_survives_comp_exp_flip: ONCE_REWRITE_RULE [CONJ_COMM] *)
val _ = emit_as "member_cutset_survives_comp_exp_flip_typed" (fetch_other ("crep_to_loopProof","member_cutset_survives_comp_exp"));
(* member_cutset_survives_comp_exps_flip: ONCE_REWRITE_RULE [CONJ_COMM] *)
val _ = emit_as "member_cutset_survives_comp_exps_flip_typed" (fetch_other ("crep_to_loopProof","member_cutset_survives_comp_exps"));
