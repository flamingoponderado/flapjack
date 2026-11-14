load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open lab_to_targetProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;


fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="lab_to_targetProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/lab_to_targetProofScript.sml";

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

(* Overloads: capture the typed abbreviation term from the source line. *)
fun overload_term_of name =
  let
    fun scan [] = raise Fail ("missing overload " ^ name)
      | scan (l :: rest) =
          (case decl_head l name "Overload" of
             NONE => scan rest
           | SOME rest' => rest')
    val body = scan source_lines
    fun first_tick i = if i >= String.size body then raise Fail ("no quote " ^ name)
      else if String.sub (body,i) = #"`" then i else first_tick (i+1)
    val i = first_tick 0
    fun end_tick j = if j >= String.size body then raise Fail ("no closing quote " ^ name)
      else if String.sub (body,j) = #"`" then j else end_tick (j+1)
    val j = end_tick (i+2)
  in
    String.substring (body, i+2, j-(i+2))
  end;

fun capture_overload label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (overload_term_of name))]
  in (print (label ^ "="); print_without_macros tm; print "\n") end;

(* val x = Q.prove(`stmt`, ...) |> GSYM : capture the symmetric statement. *)
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

fun capture_sym label name =
  let
    val tm = Parse.Term [QUOTE (strip_antiquote (qprove_term_of name))]
    val (vars, eq) = strip_forall tm
    val (lhs, rhs) = dest_eq eq
    val swapped = list_mk_forall (vars, mk_eq (rhs, lhs))
  in
    (print (label ^ "="); print_term swapped; print "\n")
  end;


val _ = capture "CallFFI_bytearray_lemma_typed" "CallFFI_bytearray_lemma";
val _ = capture "EVERY_label_zero_add_nop_typed" "EVERY_label_zero_add_nop";
val _ = capture "IMP_bytes_in_memory_typed" "IMP_bytes_in_memory";
val _ = capture "IMP_bytes_in_memory_Call_typed" "IMP_bytes_in_memory_Call";
val _ = capture "IMP_bytes_in_memory_CallFFI_typed" "IMP_bytes_in_memory_CallFFI";
val _ = capture "IMP_bytes_in_memory_Cbw_typed" "IMP_bytes_in_memory_Cbw";
val _ = capture "IMP_bytes_in_memory_Halt_typed" "IMP_bytes_in_memory_Halt";
val _ = capture "IMP_bytes_in_memory_Inst_typed" "IMP_bytes_in_memory_Inst";
val _ = capture "IMP_bytes_in_memory_Install_typed" "IMP_bytes_in_memory_Install";
val _ = capture "IMP_bytes_in_memory_Jump_typed" "IMP_bytes_in_memory_Jump";
val _ = capture "IMP_bytes_in_memory_JumpCmp_typed" "IMP_bytes_in_memory_JumpCmp";
val _ = capture "IMP_bytes_in_memory_JumpCmp_1_typed" "IMP_bytes_in_memory_JumpCmp_1";
val _ = capture "IMP_bytes_in_memory_JumpReg_typed" "IMP_bytes_in_memory_JumpReg";
val _ = capture "IMP_bytes_in_memory_LocValue_typed" "IMP_bytes_in_memory_LocValue";
val _ = capture "IMP_has_io_name_typed" "IMP_has_io_name";
val _ = capture "LIST_REL_enc_line_typed" "LIST_REL_enc_line";
val _ = capture "MOD4_CASES_typed" "MOD4_CASES";
val _ = capture "MOD8_CASES_typed" "MOD8_CASES";
val _ = capture "MULT_ADD_LESS_MULT_typed" "MULT_ADD_LESS_MULT";
val _ = capture "add_nop_sec_label_ok_typed" "add_nop_sec_label_ok";
val _ = capture "aligned_IMP_ADD_LESS_dimword_typed" "aligned_IMP_ADD_LESS_dimword";
val _ = capture "all_enc_ok_even_typed" "all_enc_ok_even";
val _ = capture "all_enc_ok_lab_lookup_even_typed" "all_enc_ok_lab_lookup_even";
val _ = capture "all_enc_ok_pre_enc_sec_list_typed" "all_enc_ok_pre_enc_sec_list";
val _ = capture "all_enc_ok_pre_filter_skip_typed" "all_enc_ok_pre_filter_skip";
val _ = capture "all_enc_ok_pre_lines_upd_lab_len_typed" "all_enc_ok_pre_lines_upd_lab_len";
val _ = capture "all_enc_ok_pre_pad_code_typed" "all_enc_ok_pre_pad_code";
val _ = capture "all_enc_ok_pre_upd_lab_len_typed" "all_enc_ok_pre_upd_lab_len";
val _ = capture "all_enc_ok_prog_to_bytes_EVEN_typed" "all_enc_ok_prog_to_bytes_EVEN";
val _ = capture "all_enc_ok_split_typed" "all_enc_ok_split";
val _ = capture_overload "all_encd0_typed" "all_encd0";
val _ = capture_overload "all_labs_exist_typed" "all_labs_exist";
val _ = capture_overload "all_length_leq_typed" "all_length_leq";
val _ = capture "arith_upd_lemma_typed" "arith_upd_lemma";
val _ = capture "byte_align_32_CASES_typed" "byte_align_32_CASES";
val _ = capture "byte_align_32_IMP_typed" "byte_align_32_IMP";
val _ = capture "byte_align_32_eq_typed" "byte_align_32_eq";
val _ = capture "byte_align_64_CASES_typed" "byte_align_64_CASES";
val _ = capture "byte_align_64_IMP_typed" "byte_align_64_IMP";
val _ = capture "byte_align_64_eq_typed" "byte_align_64_eq";
val _ = capture "bytes_in_mem_APPEND_typed" "bytes_in_mem_APPEND";
val _ = capture "bytes_in_mem_IMP_memory_typed" "bytes_in_mem_IMP_memory";
val _ = capture "bytes_in_mem_asm_write_bytearray_typed" "bytes_in_mem_asm_write_bytearray";
val _ = capture "bytes_in_mem_asm_write_bytearray_lemma_typed" "bytes_in_mem_asm_write_bytearray_lemma";
val _ = capture "dimword_eq_32_imp_or_bytes_typed" "dimword_eq_32_imp_or_bytes";
val _ = capture "dimword_eq_64_imp_or_bytes_typed" "dimword_eq_64_imp_or_bytes";
val _ = capture "enc_lines_again_IMP_similar_typed" "enc_lines_again_IMP_similar";
val _ = capture "enc_lines_again_all_enc_ok_pre_typed" "enc_lines_again_all_enc_ok_pre";
val _ = capture "enc_lines_again_sec_labels_ok_typed" "enc_lines_again_sec_labels_ok";
val _ = capture "enc_lines_again_simp_EQ_typed" "enc_lines_again_simp_EQ";
val _ = capture "enc_secs_again_all_enc_ok_pre_typed" "enc_secs_again_all_enc_ok_pre";
val _ = capture "enc_with_nop_thm_typed" "enc_with_nop_thm";
val _ = capture "evaluate_ignore_clocks_typed" "evaluate_ignore_clocks";
val _ = capture "evaluate_nop_steps_typed" "evaluate_nop_steps";
val _ = capture "find_ffi_names_append_typed" "find_ffi_names_append";
val _ = capture "find_index_MAP_w2n_typed" "find_index_MAP_w2n";
val _ = capture "find_index_append_typed" "find_index_append";
val _ = capture "fp_upd_lemma_typed" "fp_upd_lemma";
val _ = capture "get_zero_labs_acc_eq_get_zero_labels_typed" "get_zero_labs_acc_eq_get_zero_labels";
val _ = capture "has_io_name_find_index_typed" "has_io_name_find_index";
val _ = capture "lab_lookup_IMP_typed" "lab_lookup_IMP";
val _ = capture "lab_lookup_compute_labels_test_typed" "lab_lookup_compute_labels_test";
val _ = capture_overload "len_no_lab_typed" "len_no_lab";
val _ = capture "line_get_zero_labs_acc_eq_line_get_zero_labels_typed" "line_get_zero_labs_acc_eq_line_get_zero_labels";
val _ = capture "line_length_MOD_0_typed" "line_length_MOD_0";
val _ = capture "line_ok_pre_add_nop_typed" "line_ok_pre_add_nop";
val _ = capture "line_ok_pre_pad_section_typed" "line_ok_pre_pad_section";
val _ = capture "line_similar_add_nop_typed" "line_similar_add_nop";
val _ = capture "line_similar_lines_upd_lab_len_typed" "line_similar_lines_upd_lab_len";
val _ = capture "line_similar_trans_typed" "line_similar_trans";
val _ = capture_sym "lines_upd_lab_len_AUX_typed" "lines_upd_lab_len_AUX";
val _ = capture "lines_upd_lab_len_sec_label_ok_typed" "lines_upd_lab_len_sec_label_ok";
val _ = capture "list_add_if_fresh_simp_typed" "list_add_if_fresh_simp";
val _ = capture "loc_to_pc_append_typed" "loc_to_pc_append";
val _ = capture "not_not_skip_IMP_Skip_typed" "not_not_skip_IMP_Skip";
val _ = capture "pad_section_sec_label_ok_typed" "pad_section_sec_label_ok";
val _ = capture "pos_val_thm0_typed" "pos_val_thm0";
val _ = capture "prog_to_bytes_lemma_typed" "prog_to_bytes_lemma";
val _ = capture "read_bytearray_state_rel_typed" "read_bytearray_state_rel";
val _ = capture "remove_labels_loop_thm_typed" "remove_labels_loop_thm";
val _ = capture "sec_get_zero_labs_acc_eq_sec_get_zero_labels_typed" "sec_get_zero_labs_acc_eq_sec_get_zero_labels";
(* `semantics_compile_lemma` is derived in the source from
   `semantics_compile_lemma'` by CONJ_ASSOC, MATCH_MP implements_intro_gen and
   GSYM CONJ_ASSOC; rebuild that statement at term level: the antecedent's
   conjuncts except the final `semantics ... <> Fail`, implying
   `implements' T (machine_sem mc_conf ffi ms) {semantics ...}`. *)
val _ = (
  let
    val tm = Parse.Term [QUOTE (strip_antiquote (statement_of "semantics_compile_lemma'"))]
    val (vars, body) = strip_forall tm
    val (ante, conseq) = dest_imp body
    val conjs = strip_conj ante
    val b = list_mk_conj (List.take (conjs, List.length conjs - 1))
    val lastc = List.last conjs
    val eq = dest_neg lastc
    val (s, _) = dest_eq eq
    val (y, _) = dest_eq conseq
    val impl = list_mk_comb (``implements'``, [``T``, y, ``{^s}``])
    val stmt = list_mk_forall (vars, mk_imp (b, impl))
  in
    print ("semantics_compile_lemma_typed="); print_term stmt; print "\n"
  end);
val _ = capture "semantics_compile_lemma_prime_typed" "semantics_compile_lemma'";
val _ = capture "shift_interfer_0_typed" "shift_interfer_0";
val _ = capture "upd_pc_with_pc_typed" "upd_pc_with_pc";
val _ = capture "word_cmp_lemma_typed" "word_cmp_lemma";
val _ = capture "write_bytearray_NOT_Loc_typed" "write_bytearray_NOT_Loc";
val _ = capture "zero_labs_acc_of_eq_zero_labs_of_typed" "zero_labs_acc_of_eq_zero_labs_of";
