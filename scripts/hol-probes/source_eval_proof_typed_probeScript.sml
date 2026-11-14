load "preamble";
load "source_evalProofTheory";
load "semanticsTheory";
load "semanticPrimitivesTheory";
load "namespaceTheory";
load "namespacePropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open source_evalProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="source_evalProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/source_evalProofScript.sml";

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

val _ = emit_exported "oracle_semantics_prog_typed" "oracle_semantics_prog";
val _ = emit_exported "evaluate_prog_with_clock_put_oracle_typed" "evaluate_prog_with_clock_put_oracle";
val _ = emit_exported "get_oracle_props_typed" "get_oracle_props";
val _ = emit_exported "extract_oracle_agrees_typed" "extract_oracle_agrees";
val _ = emit_exported "evaluate_decs_clock_record_common_prefix_typed" "evaluate_decs_clock_record_common_prefix";
val _ = emit_exported "evaluate_record_suffix_typed" "evaluate_record_suffix";
val _ = emit_exported "insert_oracle_correct_typed" "insert_oracle_correct";
val _ = emit_exported "evaluate_is_record_forward_typed" "evaluate_is_record_forward";
val _ = emit_exported "check_dup_ctors_thm_typed" "check_dup_ctors_thm";
val _ = emit_exported "eval_simulation_typed" "eval_simulation";
val _ = emit_exported "abort_def_typed" "abort_def";
val _ = emit_exported "abort_simps_typed" "abort_simps";
val _ = emit_exported "do_eval_sim_typed" "do_eval_sim";
val _ = emit_exported "do_app_sim_typed" "do_app_sim";
val _ = emit_exported "declare_env_sim_typed" "declare_env_sim";
val _ = emit_exported "env_rel_nsLift_typed" "env_rel_nsLift";
val _ = emit_exported "env_rel_nsAppend_typed" "env_rel_nsAppend";
val _ = emit_exported "env_rel_extend_dec_env_typed" "env_rel_extend_dec_env";
val _ = emit_exported "env_rel_add_nsBind_typed" "env_rel_add_nsBind";
val _ = emit_exported "env_rel_add_nsBindList_typed" "env_rel_add_nsBindList";
val _ = emit_exported "env_rel_nsLookup_v_typed" "env_rel_nsLookup_v";
val _ = emit_exported "pairarg_to_pair_map_typed" "pairarg_to_pair_map";
val _ = emit_exported "s_rel_clock_typed" "s_rel_clock";
val _ = emit_exported "concrete_v_rel_typed" "concrete_v_rel";
val _ = emit_exported "v_rel_list_to_v_typed" "v_rel_list_to_v";
val _ = emit_exported "v_to_list_typed" "v_to_list";
val _ = emit_exported "v_to_char_list_typed" "v_to_char_list";
val _ = emit_exported "vs_to_string_typed" "vs_to_string";
val _ = emit_exported "store_assign_typed" "store_assign";
val _ = emit_exported "store_lookup_typed" "store_lookup";
val _ = emit_exported "Num_11_typed" "Num_11";
val _ = emit_exported "do_eq_typed" "do_eq";
val _ = emit_exported "can_pmatch_all_typed" "can_pmatch_all";
val _ = emit_exported "pmatch_typed" "pmatch";
val _ = emit_exported "es_stack_forward_def_typed" "es_stack_forward_def";
val _ = emit_exported "es_stack_forward_refl_typed" "es_stack_forward_refl";
val _ = emit_exported "es_stack_forward_trans_typed" "es_stack_forward_trans";
val _ = emit_exported "match_result_rel_def_typed" "match_result_rel_def";
val _ = emit_exported "store_lookup_rel_typed" "store_lookup_rel";
val _ = emit_exported "s_rel_store_lookup_typed" "s_rel_store_lookup";
val _ = emit_exported "forward_rules_typed" "forward_rules";
val _ = emit_exported "s_rel_def_typed" "s_rel_def";
val _ = emit_exported "es_forward_def_typed" "es_forward_def";
val _ = emit_exported "es_forward_refl_typed" "es_forward_refl";
val _ = emit_exported "es_forward_trans_typed" "es_forward_trans";
val _ = emit_exported "v_rel_forward_typed" "v_rel_forward";
val _ = emit_exported "v_rel_Boolv_typed" "v_rel_Boolv";
val _ = emit_exported "env_rel_concrete_v_typed" "env_rel_concrete_v";
(* Inductive v_rel: captured through its rules theorem. *)
val _ = emit_exported "v_rel_typed" "v_rel_rules";
val _ = emit_exported "v_rel_concrete_v_typed" "v_rel_concrete_v";
val _ = emit_exported "env_rel_def_typed" "env_rel_def";
val _ = emit_exported "env_rel_mono_rel_typed" "env_rel_mono_rel";
val _ = emit_exported "adjust_oracle_evaluate_typed" "adjust_oracle_evaluate";
val _ = emit_exported "result_rel_IMP_cases_typed" "result_rel_IMP_cases";
val _ = emit_exported "adjust_oracle_semantics_prog_typed" "adjust_oracle_semantics_prog";
val _ = emit_exported "recorded_orac_wf_def_typed" "recorded_orac_wf_def";
val _ = emit_exported "orac_s_def_typed" "orac_s_def";
val _ = emit_exported "extract_oracle_def_typed" "extract_oracle_def";
val _ = emit_exported "get_oracle_def_typed" "get_oracle_def";
val _ = emit_exported "put_oracle_def_typed" "put_oracle_def";
val _ = emit_exported "precond_eval_state_def_typed" "precond_eval_state_def";
val _ = emit_exported "orac_agrees_def_typed" "orac_agrees_def";
val _ = emit_exported "orac_extended_wf_def_typed" "orac_extended_wf_def";
val _ = emit_exported "record_forward_def_typed" "record_forward_def";
val _ = emit_exported "record_forward_refl_typed" "record_forward_refl";
val _ = emit_exported "record_forward_trans_typed" "record_forward_trans";
val _ = emit_exported "orac_agrees_backward_typed" "orac_agrees_backward";
val _ = emit_exported "recorded_orac_wf_step_typed" "recorded_orac_wf_step";
val _ = emit_exported "reset_env_generation_orac_eqs_typed" "reset_env_generation_orac_eqs";
val _ = emit_exported "insert_declare_env_typed" "insert_declare_env";
val _ = emit_exported "insert_do_eval_typed" "insert_do_eval";
val _ = emit_exported "v_to_list_concrete_typed" "v_to_list_concrete";
val _ = emit_exported "maybe_all_list_SOME_typed" "maybe_all_list_SOME";
val _ = emit_exported "maybe_all_list_EVERY_typed" "maybe_all_list_EVERY";
val _ = emit_exported "v_to_word8_list_concrete_typed" "v_to_word8_list_concrete";
val _ = emit_exported "v_to_word64_list_concrete_typed" "v_to_word64_list_concrete";
val _ = emit_exported "compiler_agrees_typed" "compiler_agrees";
val _ = emit_exported "v_to_nat_def_typed" "v_to_nat_def";
val _ = emit_exported "v_to_env_id_def_typed" "v_to_env_id_def";
val _ = emit_exported "v_to_nat_SOME_typed" "v_to_nat_SOME";
val _ = emit_exported "v_to_env_id_SOME_typed" "v_to_env_id_SOME";
val _ = emit_exported "do_eval_record_def_typed" "do_eval_record_def";
val _ = emit_exported "is_record_def_typed" "is_record_def";
val _ = emit_exported "is_record_IMP_typed" "is_record_IMP";
val _ = emit_exported "v_rel_abs_typed" "v_rel_abs";
val _ = emit_exported "mk_compiler_fun_from_ci_def_typed" "mk_compiler_fun_from_ci_def";
val _ = emit_exported "mk_init_eval_state_def_typed" "mk_init_eval_state_def";
val _ = emit_exported "insert_gen_oracle_def_typed" "insert_gen_oracle_def";
val _ = emit_exported "adjust_oracle_def_typed" "adjust_oracle_def";
val _ = emit_exported "is_insert_oracle_def_typed" "is_insert_oracle_def";
val _ = emit_exported "adjust_oracle_insert_gen_oracle_typed" "adjust_oracle_insert_gen_oracle";
val _ = emit_exported "do_eval_oracle_def_typed" "do_eval_oracle_def";
val _ = emit_exported "env_rel_nsEmpty_typed" "env_rel_nsEmpty";
val _ = emit_exported "sv_rel_l_cases_typed" "sv_rel_l_cases";
val _ = emit_exported "v_rel_l_simps_typed" "v_rel_l_simps";
val _ = capture "extract_oracle_SUC_st_typed" "extract_oracle_SUC_st";
val _ = capture "extract_oracle_0_st_typed" "extract_oracle_0_st";
val _ = capture "neq_IMP_to_cases_typed" "neq_IMP_to_cases";
val _ = capture "env_rel_nsLookup_c_typed" "env_rel_nsLookup_c";
val _ = capture "pair_CASE_eq_pairarg_typed" "pair_CASE_eq_pairarg";
val _ = capture "less_sub_1_cases_typed" "less_sub_1_cases";
val _ = capture "abort_imp_intro_typed" "abort_imp_intro";
val _ = capture "env_rel_imp_c_typed" "env_rel_imp_c";
val _ = capture "s_rel_clock2_typed" "s_rel_clock2";
val _ = capture "orac_agrees_s_rel_IMP_typed" "orac_agrees_s_rel_IMP";
val _ = capture "v_rel_check_type_typed" "v_rel_check_type";
val _ = capture "LIST_REL_v_rel_check_type_typed" "LIST_REL_v_rel_check_type";
val _ = capture "pmatch_drule_form_typed" "pmatch_drule_form";
val _ = capture "is_insert_decs_typed" "is_insert_decs";
val _ = capture "declare_env_adjust_typed" "declare_env_adjust";
val _ = capture "adjust_oracle_reset_typed" "adjust_oracle_reset";
val _ = capture "is_insert_related_typed" "is_insert_related";
val _ = capture "is_insert_reset_typed" "is_insert_reset";
val _ = capture "declare_env_is_insert_typed" "declare_env_is_insert";
val _ = capture "do_eval_adjust_typed" "do_eval_adjust";
val _ = capture "recorded_orac_wf_defined_typed" "recorded_orac_wf_defined";
val _ = capture "extract_oracle_SOME_SUC_typed" "extract_oracle_SOME_SUC";

(* Generated relation theorems and the compiler_instance record datatype. *)
val _ = emit_exported "v_rel_ind_typed" "v_rel_ind";
val _ = emit_exported "v_rel_cases_typed" "v_rel_cases";
val _ = capture_dt "compiler_instance_typed"
  (mk_type ("compiler_instance", [mk_vartype "'config"]));

(* Derived local theorems, replayed exactly as the source derives them. *)
val _ = emit_as "alist_to_ns_to_bind2_typed"
  (Q.SPEC `nsEmpty` (GEN_ALL (fetch_other ("namespaceProps","nsAppend_to_nsBindList")))
    |> REWRITE_RULE [fetch_other ("namespaceProps","nsAppend_nsEmpty")]);
val _ = emit_as "nsSing_eq_bind_typed"
  (fetch_other ("namespace","nsSing_def")
    |> REWRITE_RULE [GSYM (fetch_other ("namespace","nsBind_def")),
         GSYM (fetch_other ("namespace","nsEmpty_def"))]);
val _ = emit_as "record_forward_trans_sym_typed"
  (REWRITE_RULE [Once CONJ_COMM] (fetch_other ("source_evalProof","record_forward_trans")));
val _ = emit_as "adjust_oracle_ev_decs_typed"
  (fetch_other ("source_evalProof","adjust_oracle_evaluate")
    |> UNDISCH |> CONJUNCTS |> List.last |> DISCH_ALL
    |> SIMP_RULE bool_ss [PULL_FORALL]
    |> Q.SPEC `s with clock := k`
    |> SIMP_RULE (srw_ss ()) []);
