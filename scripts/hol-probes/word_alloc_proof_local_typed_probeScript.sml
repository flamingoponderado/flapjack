(* Typed captures for the word_allocProof reviewed rows that earlier probes did not
   cover (task 178). The theory is built in a private copy of the pinned CakeML
   tree (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path. Exported theorems and definitions are
   fetched from the theory DB; `[local]` theorems are parsed from the pinned
   source text with SML antiquotation splices expanded; derived theorems and
   `val ... = Q.prove(...)` lemmas are captured through the statement named in
   each comment. *)
load "preamble";
load "word_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open word_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;


fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="word_allocProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

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

val source_text = source_text_of "compiler/backend/proofs/word_allocProofScript.sml";

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

(* `val name = Q.prove(`stmt`, ...)` : capture the quoted statement itself. *)
fun qprove_term_of name =
  let
    val whole = String.concatWith "\n" source_lines
    fun find prefix i = if i + String.size prefix > String.size whole then raise Fail ("no qprove " ^ name)
      else if String.substring (whole,i,String.size prefix) = prefix then i
      else find prefix (i+1)
    val prefix = "val " ^ name ^ " = Q.prove("
    val k = find prefix 0
    val rest = String.extract (whole, k + String.size prefix, NONE)
    fun first_tick i = if i >= String.size rest then raise Fail ("no quote " ^ name)
      else if String.sub (rest,i) = #"`" then i else first_tick (i+1)
    val i = first_tick 0
    fun end_tick j = if j >= String.size rest then raise Fail ("no closing quote " ^ name)
      else if String.sub (rest,j) = #"`" then j else end_tick (j+1)
    val j = end_tick (i+1)
  in
    String.substring (rest, i+1, j-(i+1))
  end;

fun capture_qprove label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (qprove_term_of name))]
  in (print (label ^ "="); print_term tm; print "\n") end;

(* `Theorem name = Q.prove(`stmt`, ...)` : same quoted statement. *)
fun theorem_qprove_term_of name =
  let
    val whole = String.concatWith "\n" source_lines
    fun find prefix i = if i + String.size prefix > String.size whole then raise Fail ("no theorem qprove " ^ name)
      else if String.substring (whole,i,String.size prefix) = prefix then i
      else find prefix (i+1)
    val prefix = "Theorem " ^ name
    val k = find prefix 0
    val rest = String.extract (whole, k + String.size prefix, NONE)
    fun first_tick i = if i >= String.size rest then raise Fail ("no quote " ^ name)
      else if String.sub (rest,i) = #"`" then i else first_tick (i+1)
    val i = first_tick 0
    fun end_tick j = if j >= String.size rest then raise Fail ("no closing quote " ^ name)
      else if String.sub (rest,j) = #"`" then j else end_tick (j+1)
    val j = end_tick (i+1)
  in
    String.substring (rest, i+1, j-(i+1))
  end;

fun capture_theorem_qprove label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (theorem_qprove_term_of name))]
  in (print (label ^ "="); print_term tm; print "\n") end;


val _ = capture "EVERY_get_forced_typed" "EVERY_get_forced";
val _ = capture "INJ_IMP_IMAGE_DIFF_typed" "INJ_IMP_IMAGE_DIFF";
val _ = capture "INJ_IMP_IMAGE_DIFF_single_typed" "INJ_IMP_IMAGE_DIFF_single";
val _ = capture "INJ_UNION_typed" "INJ_UNION";
val _ = capture "LENGTH_list_rerrange_typed" "LENGTH_list_rerrange";
val _ = capture "MAP_FST_keys_SORT_typed" "MAP_FST_keys_SORT";
val _ = capture "alookup_zip_map_option_lookup_none_typed" "alookup_zip_map_option_lookup_none";
val _ = capture "alookup_zip_map_some_typed" "alookup_zip_map_some";
val _ = capture "apply_colour_exp_lemma_typed" "apply_colour_exp_lemma";
val _ = capture "apply_nummap_key_domain_typed" "apply_nummap_key_domain";
val _ = capture "call_arg_convention_preservation_typed" "call_arg_convention_preservation";
val _ = capture "cut_env_fromAList_LN_typed" "cut_env_fromAList_LN";
val _ = capture "domain_big_union_subset_typed" "domain_big_union_subset";
val _ = capture "domain_insert_eq_union_typed" "domain_insert_eq_union";
val _ = capture "domain_numset_list_insert_eq_union_typed" "domain_numset_list_insert_eq_union";
val _ = capture "env_to_list_keys_typed" "env_to_list_keys";
val _ = capture "env_to_list_perm_typed" "env_to_list_perm";
val _ = capture "evaluate_apply_colour_Loop_helper_typed" "evaluate_apply_colour_Loop_helper";
val _ = capture "evaluate_fake_const_chain_typed" "evaluate_fake_const_chain";
val _ = capture "evaluate_fake_const_chain_locals_typed" "evaluate_fake_const_chain_locals";
val _ = capture "evaluate_remove_dead_Loop_helper_typed" "evaluate_remove_dead_Loop_helper";
val _ = capture "evaluate_seq_collapse_typed" "evaluate_seq_collapse";
val _ = capture "evaluate_ssa_reconcile_typed" "evaluate_ssa_reconcile";
val _ = capture "every_apply_nummap_key_helper_typed" "every_apply_nummap_key_helper";
val _ = capture "every_var_T_typed" "every_var_T";
val _ = capture "every_var_exp_get_live_exp_typed" "every_var_exp_get_live_exp";
val _ = capture "every_var_exp_get_reads_exp_typed" "every_var_exp_get_reads_exp";
val _ = capture "every_var_in_get_clash_tree_typed" "every_var_in_get_clash_tree";
val _ = capture "every_var_is_phy_var_total_colour_typed" "every_var_is_phy_var_total_colour";
val _ = capture "exp_to_addr_ShareInst_typed" "exp_to_addr_ShareInst";
val _ = capture "fake_moves_conventions_typed" "fake_moves_conventions";
val _ = capture "fake_moves_conventions2_typed" "fake_moves_conventions2";
val _ = capture "fake_moves_correctL_typed" "fake_moves_correctL";
val _ = capture "fake_moves_correctR_typed" "fake_moves_correctR";
val _ = capture "fake_moves_distinct_tar_reg_typed" "fake_moves_distinct_tar_reg";
val _ = capture "fake_moves_frame_typed" "fake_moves_frame";
val _ = capture "fake_moves_frame2_typed" "fake_moves_frame2";
val _ = capture "fake_moves_frame3_typed" "fake_moves_frame3";
val _ = capture "fake_seq_every_inst_distinct_tar_reg_typed" "fake_seq_every_inst_distinct_tar_reg";
val _ = capture "fake_seq_full_inst_ok_less_typed" "fake_seq_full_inst_ok_less";
val _ = capture "fake_seq_pre_alloc_conventions_typed" "fake_seq_pre_alloc_conventions";
val _ = capture "fix_inconsistencies_conventions_typed" "fix_inconsistencies_conventions";
val _ = capture "fix_inconsistencies_correctL_typed" "fix_inconsistencies_correctL";
val _ = capture "fix_inconsistencies_correctR_typed" "fix_inconsistencies_correctR";
val _ = capture "fix_inconsistencies_props_typed" "fix_inconsistencies_props";
val _ = capture "flip_rw_typed" "flip_rw";
val _ = capture "foldr_insert_const_swap_typed" "foldr_insert_const_swap";
val _ = capture "forced_distinct_col_typed" "forced_distinct_col";
val _ = capture "get_forced_in_get_clash_tree_typed" "get_forced_in_get_clash_tree";
val _ = capture "get_forced_pairwise_distinct_typed" "get_forced_pairwise_distinct";
val _ = capture "get_forced_tail_split_typed" "get_forced_tail_split";
val _ = capture "get_reads_exp_get_live_exp_typed" "get_reads_exp_get_live_exp";
val _ = capture "get_vars_eq_typed" "get_vars_eq";
val _ = capture "get_vars_exists_typed" "get_vars_exists";
val _ = capture "get_vars_list_insert_eq_gen_typed" "get_vars_list_insert_eq_gen";
val _ = capture "get_vars_set_vars_eq_typed" "get_vars_set_vars_eq";
val _ = capture "is_alloc_var_add_typed" "is_alloc_var_add";
val _ = capture "is_alloc_var_flip_typed" "is_alloc_var_flip";
val _ = capture "is_stack_var_add_typed" "is_stack_var_add";
val _ = capture "is_stack_var_flip_typed" "is_stack_var_flip";
val _ = capture "limit_var_props_typed" "limit_var_props";
val _ = capture "list_next_var_rename_lemma_1_typed" "list_next_var_rename_lemma_1";
val _ = capture "list_next_var_rename_lemma_2_typed" "list_next_var_rename_lemma_2";
val _ = capture "list_next_var_rename_lemma_2_prime_typed" "list_next_var_rename_lemma_2'";
val _ = capture "list_next_var_rename_move_preserve_typed" "list_next_var_rename_move_preserve";
val _ = capture "list_next_var_rename_move_preserve_weak_typed" "list_next_var_rename_move_preserve_weak";
val _ = capture "list_next_var_rename_move_props_typed" "list_next_var_rename_move_props";
val _ = capture "list_next_var_rename_move_props_2_typed" "list_next_var_rename_move_props_2";
val _ = capture "list_next_var_rename_props_typed" "list_next_var_rename_props";
(* list_next_var_rename_props_2: derived from list_next_var_rename_props; the base statement carries the carriers *)
val _ = capture "list_next_var_rename_props_2_typed" "list_next_var_rename_props";
val _ = capture "list_rearrange_perm_typed" "list_rearrange_perm";
val _ = capture "live_store_rel_NIL_typed" "live_store_rel_NIL";
val _ = capture "live_store_rel_refl_typed" "live_store_rel_refl";
val _ = capture "lookup_numset_list_insert_typed" "lookup_numset_list_insert";
val _ = capture "loop_setup_correct_typed" "loop_setup_correct";
val _ = capture "loop_setup_every_inst_distinct_tar_reg_typed" "loop_setup_every_inst_distinct_tar_reg";
val _ = capture "loop_setup_full_inst_ok_less_typed" "loop_setup_full_inst_ok_less";
val _ = capture "loop_setup_pre_alloc_conventions_typed" "loop_setup_pre_alloc_conventions";
val _ = capture "loop_setup_props_local_typed" "loop_setup_props_local";
val _ = capture "max3_eq_typed" "max3_eq";
val _ = capture "max_var_exp_max_typed" "max_var_exp_max";
val _ = capture "max_var_inst_max_typed" "max_var_inst_max";
val _ = capture "merge_moves_correctL_typed" "merge_moves_correctL";
val _ = capture "merge_moves_correctR_typed" "merge_moves_correctR";
val _ = capture "merge_moves_frame_typed" "merge_moves_frame";
val _ = capture "merge_moves_frame2_typed" "merge_moves_frame2";
val _ = capture "merge_moves_frame3_typed" "merge_moves_frame3";
val _ = capture "merge_moves_fst_typed" "merge_moves_fst";
val _ = capture "mov_eval_head_typed" "mov_eval_head";
val _ = capture "next_var_rename_props_typed" "next_var_rename_props";
val _ = capture "nummaps_to_nummap_typed" "nummaps_to_nummap";
val _ = capture "numset_list_delete_swap_typed" "numset_list_delete_swap";
val _ = capture "numset_list_insert_eq_UNION_typed" "numset_list_insert_eq_UNION";
val _ = capture "numset_list_insert_swap_typed" "numset_list_insert_swap";
val _ = capture "option_lookup_subset_helper_typed" "option_lookup_subset_helper";
val _ = capture "oracle_colour_ok_conventions_typed" "oracle_colour_ok_conventions";
val _ = capture "setup_ssa_props_typed" "setup_ssa_props";
val _ = capture "setup_ssa_props_2_typed" "setup_ssa_props_2";
val _ = capture "ssa_cc_trans_Loop_helper_typed" "ssa_cc_trans_Loop_helper";
val _ = capture "ssa_cc_trans_exp_correct_typed" "ssa_cc_trans_exp_correct";
val _ = capture "ssa_cc_trans_inst_props_typed" "ssa_cc_trans_inst_props";
val _ = capture "ssa_eq_rel_swap_typed" "ssa_eq_rel_swap";
val _ = capture "ssa_locals_rel_get_var_typed" "ssa_locals_rel_get_var";
val _ = capture "ssa_locals_rel_get_vars_typed" "ssa_locals_rel_get_vars";
val _ = capture "ssa_locals_rel_ignore_insert_typed" "ssa_locals_rel_ignore_insert";
val _ = capture "ssa_locals_rel_ignore_list_insert_typed" "ssa_locals_rel_ignore_list_insert";
val _ = capture "ssa_locals_rel_ignore_set_var_typed" "ssa_locals_rel_ignore_set_var";
val _ = capture "ssa_locals_rel_insert_typed" "ssa_locals_rel_insert";
val _ = capture "ssa_locals_rel_list_next_var_rename_typed" "ssa_locals_rel_list_next_var_rename";
val _ = capture "ssa_locals_rel_more_typed" "ssa_locals_rel_more";
val _ = capture "ssa_locals_rel_set_var_typed" "ssa_locals_rel_set_var";
val _ = capture "ssa_map_ok_extend_typed" "ssa_map_ok_extend";
val _ = capture "ssa_map_ok_inter_typed" "ssa_map_ok_inter";
val _ = capture "ssa_map_ok_lem_typed" "ssa_map_ok_lem";
val _ = capture "ssa_map_ok_more_typed" "ssa_map_ok_more";
val _ = capture "ssa_reconcile_filtered_all_distinct_typed" "ssa_reconcile_filtered_all_distinct";
val _ = capture "ssa_reconcile_get_vars_lemma_typed" "ssa_reconcile_get_vars_lemma";
val _ = capture "ssa_reconcile_moves_eq_typed" "ssa_reconcile_moves_eq";
val _ = capture "st_eq_typed" "st_eq";
val _ = capture "strong_locals_rel_I_cut_env_typed" "strong_locals_rel_I_cut_env";
val _ = capture "strong_locals_rel_I_cut_envs_typed" "strong_locals_rel_I_cut_envs";
val _ = capture "strong_locals_rel_I_get_var_typed" "strong_locals_rel_I_get_var";
val _ = capture "strong_locals_rel_I_get_var_prime_typed" "strong_locals_rel_I_get_var'";
val _ = capture "strong_locals_rel_I_get_vars_prime_typed" "strong_locals_rel_I_get_vars'";
val _ = capture "strong_locals_rel_I_insert_insert_typed" "strong_locals_rel_I_insert_insert";
val _ = capture "strong_locals_rel_I_word_exp_typed" "strong_locals_rel_I_word_exp";
val _ = capture "strong_locals_rel_extend_aux_typed" "strong_locals_rel_extend_aux";
val _ = capture "strong_locals_rel_get_var_typed" "strong_locals_rel_get_var";
val _ = capture "strong_locals_rel_get_var_imm_typed" "strong_locals_rel_get_var_imm";
val _ = capture "strong_locals_rel_get_vars_typed" "strong_locals_rel_get_vars";
val _ = capture "strong_locals_rel_insert_notin_typed" "strong_locals_rel_insert_notin";
val _ = capture "strong_locals_rel_subset_typed" "strong_locals_rel_subset";
val _ = capture "strong_locals_rel_subset_domain_typed" "strong_locals_rel_subset_domain";
val _ = capture "union_apply_nummaps_key_typed" "union_apply_nummaps_key";
val _ = capture "wf_delete_swap_typed" "wf_delete_swap";
val _ = capture "wf_get_live_exp_typed" "wf_get_live_exp";
val _ = capture "wf_insert_swap_typed" "wf_insert_swap";
val _ = capture "wf_numset_list_delete_eq_typed" "wf_numset_list_delete_eq";
val _ = capture "with_same_locals_typed" "with_same_locals";
val _ = capture "with_same_store_typed" "with_same_store";
val _ = capture "word_alloc_full_inst_ok_less_lem_typed" "word_alloc_full_inst_ok_less_lem";
