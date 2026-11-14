(* Typed captures for the word_to_stackProof reviewed rows that earlier probes did not
   cover (task 178). The theory is built in a private copy of the pinned CakeML
   tree (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path. Exported theorems and definitions are
   fetched from the theory DB; `[local]` theorems are parsed from the pinned
   source text with SML antiquotation splices expanded; derived theorems and
   `val ... = Q.prove(...)` lemmas are captured through the statement named in
   each comment. *)
load "preamble";
load "word_to_stackProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;


fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="word_to_stackProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/word_to_stackProofScript.sml";

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


val _ = capture "ALL_DISTINCT_MEM_toAList_fromAList_typed" "ALL_DISTINCT_MEM_toAList_fromAList";
val _ = capture "APPEND_LEMMA_typed" "APPEND_LEMMA";
val _ = capture "DIV_ADD_1_typed" "DIV_ADD_1";
val _ = capture "DROP_LUPDATE_lemma1_typed" "DROP_LUPDATE_lemma1";
val _ = capture "DROP_LUPDATE_lemma2_typed" "DROP_LUPDATE_lemma2";
val _ = capture "DROP_TAKE_NIL_typed" "DROP_TAKE_NIL";
val _ = capture "DROP_list_LUPDATE_typed" "DROP_list_LUPDATE";
val _ = capture "DROP_list_LUPDATE_IGNORE_typed" "DROP_list_LUPDATE_IGNORE";
(* DROP_list_LUPDATE_lemma: derived from DROP_list_LUPDATE; the base statement carries the carriers *)
val _ = capture "DROP_list_LUPDATE_lemma_typed" "DROP_list_LUPDATE";
val _ = capture "EVEN_GT_typed" "EVEN_GT";
val _ = capture "EVERY_IMP_EVERY_LASTN_typed" "EVERY_IMP_EVERY_LASTN";
val _ = capture "GENLIST_bits_to_word_typed" "GENLIST_bits_to_word";
val _ = capture "GENLIST_bits_to_word_alt_typed" "GENLIST_bits_to_word_alt";
val _ = capture "Halt_EQ_compile_result_typed" "Halt_EQ_compile_result";
val _ = capture "IMP_enc_stack_typed" "IMP_enc_stack";
val _ = capture "LASTN_CONS_ID_typed" "LASTN_CONS_ID";
val _ = capture "LASTN_DROP2_typed" "LASTN_DROP2";
val _ = capture "LASTN_LENGTH_BOUNDS_typed" "LASTN_LENGTH_BOUNDS";
val _ = capture "LASTN_LENGTH_ID2_typed" "LASTN_LENGTH_ID2";
val _ = capture "LASTN_LESS_typed" "LASTN_LESS";
val _ = capture "LASTN_MORE_typed" "LASTN_MORE";
val _ = capture "LAST_GENLIST_evens_typed" "LAST_GENLIST_evens";
val _ = capture "LENGTH_word_list_lemma_typed" "LENGTH_word_list_lemma";
val _ = capture "LIST_REL_abs_frame_eq_handler_val_typed" "LIST_REL_abs_frame_eq_handler_val";
val _ = capture "LLOOKUP_cons_SUC_typed" "LLOOKUP_cons_SUC";
val _ = capture "LLOOKUP_list_LUPDATE_IGNORE_typed" "LLOOKUP_list_LUPDATE_IGNORE";
val _ = capture "LUPDATE_TAKE_LEMMA_typed" "LUPDATE_TAKE_LEMMA";
val _ = capture "MAP_SND_MAP_FST_typed" "MAP_SND_MAP_FST";
val _ = capture "MEM_index_list_EL_typed" "MEM_index_list_EL";
val _ = capture "MEM_index_list_LIM_typed" "MEM_index_list_LIM";
val _ = capture "MEM_toAList_fromAList_typed" "MEM_toAList_fromAList";
val _ = capture "MIN_ADD_typed" "MIN_ADD";
val _ = capture "PopHandler_no_shmemop_typed" "PopHandler_no_shmemop";
val _ = capture "PushHandler_no_shmemop_typed" "PushHandler_no_shmemop";
val _ = capture "SORTED_CONS_IMP_typed" "SORTED_CONS_IMP";
val _ = capture "SORTED_FST_LESS_IMP_typed" "SORTED_FST_LESS_IMP";
val _ = capture "SORTED_FST_PERM_IMP_ALIST_EQ_typed" "SORTED_FST_PERM_IMP_ALIST_EQ";
val _ = capture "SORTED_IMP_ALL_DISTINCT_LEMMA_typed" "SORTED_IMP_ALL_DISTINCT_LEMMA";
val _ = capture "SORTED_IMP_EQ_LISTS_typed" "SORTED_IMP_EQ_LISTS";
val _ = capture "SORTED_weaken2_typed" "SORTED_weaken2";
val _ = capture "StackHandlerArgs_no_shmemop_typed" "StackHandlerArgs_no_shmemop";
val _ = capture "TAKE_DROP_EQ_typed" "TAKE_DROP_EQ";
val _ = capture "TAKE_TAKE_MIN_typed" "TAKE_TAKE_MIN";
val _ = capture "TIMES2_DIV2_lemma_typed" "TIMES2_DIV2_lemma";
val _ = capture "abs_stack_IMP_LENGTH_typed" "abs_stack_IMP_LENGTH";
val _ = capture "abs_stack_empty_typed" "abs_stack_empty";
val _ = emit_exported "abs_stack_empty_prime_typed" "abs_stack_empty'";
val _ = capture "abs_stack_len_typed" "abs_stack_len";
val _ = capture "abs_stack_prefix_drop_typed" "abs_stack_prefix_drop";
val _ = capture "abs_stack_to_stack_LENGTH_typed" "abs_stack_to_stack_LENGTH";
val _ = capture "alloc_IMP_alloc_typed" "alloc_IMP_alloc";
val _ = capture "alloc_IMP_alloc2_typed" "alloc_IMP_alloc2";
val _ = capture "alloc_alt_typed" "alloc_alt";
val _ = capture "alloc_arg_copy_ret_typed" "alloc_arg_copy_ret";
val _ = capture "alloc_arg_copy_ret_aux_typed" "alloc_arg_copy_ret_aux";
val _ = capture "bit_length_bits_to_word_typed" "bit_length_bits_to_word";
val _ = capture "bits_to_word_SNOC_typed" "bits_to_word_SNOC";
val _ = capture "bits_to_word_miss_typed" "bits_to_word_miss";
val _ = capture "call_dest_lemma_typed" "call_dest_lemma";
val _ = capture "call_dest_stack_asm_name_typed" "call_dest_stack_asm_name";
val _ = capture "call_dest_stack_asm_remove_typed" "call_dest_stack_asm_remove";
val _ = capture "compile_prog_isPREFIX_typed" "compile_prog_isPREFIX";
val _ = capture "compile_result_NOT_2_typed" "compile_result_NOT_2";
val _ = capture "compile_word_to_stack_IMP_ALOOKUP_typed" "compile_word_to_stack_IMP_ALOOKUP";
val _ = capture "copy_ret_aux_call_args_typed" "copy_ret_aux_call_args";
val _ = capture "copy_ret_aux_no_install_typed" "copy_ret_aux_no_install";
val _ = capture "copy_ret_aux_no_shmemop_typed" "copy_ret_aux_no_shmemop";
val _ = capture "copy_ret_aux_reg_bound_typed" "copy_ret_aux_reg_bound";
val _ = capture "copy_ret_aux_stack_asm_name_typed" "copy_ret_aux_stack_asm_name";
val _ = capture "copy_ret_aux_stack_asm_remove_typed" "copy_ret_aux_stack_asm_remove";
val _ = capture "copy_ret_aux_thm_typed" "copy_ret_aux_thm";
val _ = capture "copy_ret_call_args_typed" "copy_ret_call_args";
val _ = capture "copy_ret_no_install_typed" "copy_ret_no_install";
val _ = capture "copy_ret_no_shmemop_typed" "copy_ret_no_shmemop";
val _ = capture "copy_ret_reg_bound_typed" "copy_ret_reg_bound";
val _ = capture "copy_ret_stack_asm_name_typed" "copy_ret_stack_asm_name";
val _ = capture "copy_ret_stack_asm_remove_typed" "copy_ret_stack_asm_remove";
val _ = capture "dec_stack_lemma_typed" "dec_stack_lemma";
val _ = capture "dec_stack_lemma1_typed" "dec_stack_lemma1";
val _ = capture "dec_stack_stack_size_typed" "dec_stack_stack_size";
val _ = capture "enc_stack_lemma_typed" "enc_stack_lemma";
val _ = capture "env_to_list_K_I_IMP_typed" "env_to_list_K_I_IMP";
val _ = capture "evaluate_PushHandler_typed" "evaluate_PushHandler";
val _ = capture "evaluate_PushHandler_clock_typed" "evaluate_PushHandler_clock";
val _ = capture "evaluate_call_dest_clock_typed" "evaluate_call_dest_clock";
val _ = capture "evaluate_const_inst_typed" "evaluate_const_inst";
val _ = capture "evaluate_const_inst_clock_typed" "evaluate_const_inst_clock";
val _ = capture "evaluate_cont_loop_handler_typed" "evaluate_cont_loop_handler";
val _ = capture "evaluate_stack_move_typed" "evaluate_stack_move";
(* evaluate_stack_move_clock: val ... = Q.prove(...) *)
val _ = capture_qprove "evaluate_stack_move_clock_typed" "evaluate_stack_move_clock";
val _ = capture "evaluate_stack_move_seq_typed" "evaluate_stack_move_seq";
val _ = capture "evaluate_wLive_typed" "evaluate_wLive";
val _ = capture "evaluate_wLive_clock_typed" "evaluate_wLive_clock";
val _ = capture "evaluate_wStackLoad_clock_typed" "evaluate_wStackLoad_clock";
val _ = capture "evaluate_wStackLoad_wReg1_typed" "evaluate_wStackLoad_wReg1";
val _ = capture "evaluate_wStackLoad_wReg1_with_const_typed" "evaluate_wStackLoad_wReg1_with_const";
val _ = capture "evaluate_wStackLoad_wReg2_typed" "evaluate_wStackLoad_wReg2";
val _ = capture "evaluate_wStackStore_wReg1_typed" "evaluate_wStackStore_wReg1";
val _ = capture "evaluate_wStackStore_wReg1_0_typed" "evaluate_wStackStore_wReg1_0";
val _ = capture "evaluate_wStackStore_wReg2_new_typed" "evaluate_wStackStore_wReg2_new";
val _ = capture "extract_labels_copy_ret_typed" "extract_labels_copy_ret";
val _ = capture "extract_labels_copy_ret_aux_typed" "extract_labels_copy_ret_aux";
val _ = capture "extract_labels_stack_move_StackAlloc_typed" "extract_labels_stack_move_StackAlloc";
val _ = capture "extract_labels_wStackLoad_Skip_typed" "extract_labels_wStackLoad_Skip";
val _ = capture "gc_state_rel_typed" "gc_state_rel";
val _ = capture "get_code_handler_labels_copy_ret_typed" "get_code_handler_labels_copy_ret";
val _ = capture "get_code_handler_labels_copy_ret_aux_typed" "get_code_handler_labels_copy_ret_aux";
val _ = capture "get_code_handler_labels_wStackLoad_typed" "get_code_handler_labels_wStackLoad";
(* get_code_labels_wReg: val ... = Q.prove(...) *)
val _ = capture_qprove "get_code_labels_wReg_typed" "get_code_labels_wReg";
val _ = capture "get_vars_eq_typed" "get_vars_eq";
val _ = capture "get_vars_fromList2_eq_typed" "get_vars_fromList2_eq";
val _ = capture "get_vars_fromList2_eq_cons_typed" "get_vars_fromList2_eq_cons";
val _ = capture "handler_bitmap_props_typed" "handler_bitmap_props";
val _ = capture "init_state_ok_IMP_state_rel_typed" "init_state_ok_IMP_state_rel";
val _ = capture "inter_eq_empty_2_typed" "inter_eq_empty_2";
val _ = capture "list_LUPDATE_write_bitmap_NOT_NIL_typed" "list_LUPDATE_write_bitmap_NOT_NIL";
val _ = capture "lookup_fromList2_prefix_typed" "lookup_fromList2_prefix";
val _ = capture "map_bitmap_more_typed" "map_bitmap_more";
val _ = capture "map_bitmap_more_simp_typed" "map_bitmap_more_simp";
val _ = capture "map_bitmap_success_typed" "map_bitmap_success";
val _ = capture "n2w_lsr_1_typed" "n2w_lsr_1";
val _ = capture "parsem_parmove_DIV2_lemma_typed" "parsem_parmove_DIV2_lemma";
val _ = capture "perf_call_prefix_no_shmemop_typed" "perf_call_prefix_no_shmemop";
val _ = capture "perf_call_suffix_no_shmemop_typed" "perf_call_suffix_no_shmemop";
val _ = capture "pop_env_ffi_typed" "pop_env_ffi";
val _ = capture "push_env_set_store_typed" "push_env_set_store";
val _ = capture "read_bitmap_not_empty_typed" "read_bitmap_not_empty";
val _ = capture "read_bitmap_word_list_typed" "read_bitmap_word_list";
val _ = capture "shift_shift_lemma_typed" "shift_shift_lemma";
val _ = capture "sorted_env_zip_typed" "sorted_env_zip";
val _ = capture "stack_Call_NONE_not_Break_Continue_typed" "stack_Call_NONE_not_Break_Continue";
val _ = capture "stack_move_code_labels_typed" "stack_move_code_labels";
val _ = capture "stack_move_no_labs_typed" "stack_move_no_labs";
val _ = capture "stack_move_stack_asm_name_typed" "stack_move_stack_asm_name";
val _ = capture "stack_move_stack_asm_remove_typed" "stack_move_stack_asm_remove";
val _ = capture "stack_rel_DROP_NONE_typed" "stack_rel_DROP_NONE";
val _ = capture "stack_rel_DROP_SOME_typed" "stack_rel_DROP_SOME";
val _ = capture "stack_rel_cons_LEN_NONE_typed" "stack_rel_cons_LEN_NONE";
val _ = capture "stack_rel_cons_LEN_SOME_typed" "stack_rel_cons_LEN_SOME";
val _ = capture "stack_rel_raise_typed" "stack_rel_raise";
val _ = capture "state_rel_IMP_LENGTH_typed" "state_rel_IMP_LENGTH";
val _ = capture "state_rel_code_domain_typed" "state_rel_code_domain";
val _ = capture "state_rel_cut_state_typed" "state_rel_cut_state";
val _ = emit_exported "state_rel_get_var_imp_prime_typed" "state_rel_get_var_imp'";
val _ = capture "state_rel_set_store_0_typed" "state_rel_set_store_0";
val _ = capture "transitive_GT_typed" "transitive_GT";
val _ = capture "wLive_code_labels_typed" "wLive_code_labels";
val _ = capture "wLive_stack_asm_name_typed" "wLive_stack_asm_name";
val _ = capture "wLive_stack_asm_remove_typed" "wLive_stack_asm_remove";
val _ = capture "wf_fromList2_typed" "wf_fromList2";
val _ = capture "word_Call_NONE_not_Break_Continue_typed" "word_Call_NONE_not_Break_Continue";
val _ = capture "word_gc_empty_frame_typed" "word_gc_empty_frame";
val _ = capture "word_stack_dec_stack_shape_typed" "word_stack_dec_stack_shape";
val _ = capture "word_stack_dec_stack_sorted_typed" "word_stack_dec_stack_sorted";
