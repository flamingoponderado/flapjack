(* Typed captures for the remaining rows of data_to_word_gcProofScript.sml.
   Built like data_to_word_bignum_typed_probeScript.sml (see
   scripts/hol-probes/README.md); exported theorems are fetched from the theory
   DB and `[local]` theorems are parsed from the pinned source text. *)
load "preamble";
load "data_to_word_gcProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open data_to_word_gcProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;



fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "
")
  end;

fun emit_exported label name =
  case DB.lookup {Thy="data_to_word_gcProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => raise Fail "CAKEML is required";

fun source_text_of relpath =
  let
    val stream = TextIO.openIn (OS.Path.concat (source_cake, relpath))
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in text end;

val source_text = source_text_of "compiler/backend/proofs/data_to_word_gcProofScript.sml";

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


fun type_rhs_text rest0 =
  let
    fun trimEnd str =
      let fun go [] = [] | go (c :: cs) = if c = #" " orelse c = #"	" then go cs else c :: cs
      in String.implode (List.rev (go (List.rev (String.explode str)))) end
    val s = trimEnd (Substring.string (Substring.dropl
      (fn c => c = #" " orelse c = #"	") (Substring.full rest0)))
    val n = String.size s
    fun byte i = Char.ord (String.sub (s, i))
    val curlyOpen = n >= 3 andalso byte 0 = 226 andalso byte 1 = 128 andalso byte 2 = 156
    val backOpen = n >= 2 andalso String.sub (s, 0) = #"`" andalso String.sub (s, 1) = #"`"
    val openLen = if curlyOpen then 3 else if backOpen then 2
      else raise Fail "no type quote"
    val curlyClose = n >= 3 andalso byte (n - 3) = 226 andalso byte (n - 2) = 128
      andalso byte (n - 1) = 157
    val backClose = n >= 2 andalso String.sub (s, n - 2) = #"`"
      andalso String.sub (s, n - 1) = #"`"
    val closeLen = if curlyClose then 3 else if backClose then 2
      else raise Fail "no closing type quote"
  in String.substring (s, openLen, n - openLen - closeLen) end;

fun multi_line_type_rhs s0 =
  let
    fun dropLeading str =
      let fun go [] = [] | go (c :: cs) = if c = #" " orelse c = #"	" orelse c = #"
" then go cs else c :: cs
      in String.implode (go (String.explode str)) end
    val s = dropLeading s0
    val n = String.size s
    fun byte i = Char.ord (String.sub (s, i))
    val curlyOpen = n >= 3 andalso byte 0 = 226 andalso byte 1 = 128 andalso byte 2 = 156
    val backOpen = n >= 2 andalso String.sub (s, 0) = #"`" andalso String.sub (s, 1) = #"`"
    val openLen = if curlyOpen then 3 else if backOpen then 2
      else raise Fail "no type quote"
    fun closing i =
      if i + openLen > n then raise Fail "no closing type quote"
      else if curlyOpen andalso byte i = 226 andalso byte (i+1) = 128 andalso byte (i+2) = 157 then i
      else if (not curlyOpen) andalso String.sub (s, i) = #"`" andalso String.sub (s, i+1) = #"`" then i
      else closing (i + 1)
    val j = closing openLen
  in String.substring (s, openLen, j - openLen) end;

fun type_label label thy name =
  let
    fun scan [] = raise Fail ("missing type abbreviation " ^ name)
      | scan (l :: ls) =
          let val t = strip_leading l in
            if not (String.isPrefix "Type " t) then scan ls
            else
              let
                val rest = String.extract (t, 5, NONE)
                val nm = Substring.string (Substring.takel
                  (fn c => Char.isAlphaNum c orelse c = #"_") (Substring.full (strip_leading rest)))
              in
                if nm <> name then scan ls
                else
                  let
                    val after0 = strip_leading (String.extract (rest, String.size nm, NONE))
                    val after = String.extract (after0, 1, NONE)
                    val joined = String.concatWith "
" (after :: ls)
                    val body = multi_line_type_rhs joined
                    val rhs = Parse.Type [QUOTE body]
                  in
                    print (label ^ "=Type " ^ name ^ " = " ^ type_to_string rhs ^ "\n")
                  end
              end
          end
  in scan source_lines end;

fun term_label label tm =
  (print (label ^ "="); print_term tm; print "
");

fun overload_term label name =
  let
    val prefix = "Overload " ^ name ^ " = "
    val line = List.find (fn l => String.isPrefix prefix (strip_leading l)) source_lines
    val line = case line of NONE => raise Fail ("missing overload " ^ name) | SOME l => l
    val rest = String.extract (strip_leading line, String.size prefix, NONE)
    (* The source delimits the term with curly double quotes (UTF-8 E2 80 9C /
       E2 80 9D) or ASCII double backticks; both end in byte 0x9C or 0x60. *)
    val n = String.size rest
    fun byte i = Char.ord (String.sub (rest, i))
    val curlyOpen = n >= 3 andalso byte 0 = 226 andalso byte 1 = 128 andalso byte 2 = 156
    val openLen = if curlyOpen then 3 else 2
    val body = Substring.string (Substring.slice (Substring.full rest, openLen, SOME (n - 2 * openLen)))
  in
    (Parse.clear_overloads_on name;
     print (label ^ "="); print_term (Parse.Term [QUOTE (strip_antiquote body)]); print "
")
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
    val prefix = "val " ^ name ^ " ="
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

(* `val name = ... ``stmt`` ...` : capture the first antiquotation quote after
   the binding, e.g. a blastLib.BBLAST_PROVE statement. *)
fun val_quote_term_of name =
  let
    val whole = String.concatWith "
" source_lines
    fun find prefix i = if i + String.size prefix > String.size whole then raise Fail ("no val " ^ name)
      else if String.substring (whole,i,String.size prefix) = prefix then i
      else find prefix (i+1)
    val prefix = "val " ^ name ^ " ="
    val k = find prefix 0
    val rest = String.extract (whole, k + String.size prefix, NONE)
    fun findOpen i = if i + 2 > String.size rest then raise Fail ("no quote " ^ name)
      else if String.substring (rest,i,2) = "``" then i else findOpen (i+1)
    val i = findOpen 0
    fun findClose j = if j + 2 > String.size rest then raise Fail ("no closing quote " ^ name)
      else if String.substring (rest,j,2) = "``" then j else findClose (j+1)
    val j = findClose (i+2)
  in
    String.substring (rest, i+2, j-(i+2))
  end;

fun capture_val_quote label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (val_quote_term_of name))]
  in (print (label ^ "="); print_term tm; print "
") end;



val _ = emit_exported "gcport_LESS_EQ_IMP_APPEND_ALT_typed" "LESS_EQ_IMP_APPEND_ALT";
val _ = emit_exported "gcport_word_asr_dimindex_typed" "word_asr_dimindex";
val _ = emit_exported "gcport_WORD_MUL_BIT0_typed" "WORD_MUL_BIT0";
val _ = emit_exported "gcport_word_lsl_index_typed" "word_lsl_index";
val _ = emit_exported "gcport_word_lsr_index_typed" "word_lsr_index";
val _ = emit_exported "gcport_word_index_test_typed" "word_index_test";
val _ = emit_exported "gcport_word_and_one_eq_0_iff_typed" "word_and_one_eq_0_iff";
val _ = emit_exported "gcport_word_index_0_typed" "word_index_0";
val _ = emit_exported "gcport_ABS_w2n_typed" "ABS_w2n";
val _ = emit_exported "gcport_n2mw_w2n_typed" "n2mw_w2n";
val _ = emit_exported "gcport_get_var_set_var_typed" "get_var_set_var";
val _ = emit_exported "gcport_set_var_set_var_typed" "set_var_set_var";
val _ = emit_exported "gcport_toAList_LN_typed" "toAList_LN";
val _ = emit_exported "gcport_adjust_set_LN_typed" "adjust_set_LN";
val _ = emit_exported "gcport_push_env_termdep_typed" "push_env_termdep";
val _ = emit_exported "gcport_ALOOKUP_SKIP_LEMMA_typed" "ALOOKUP_SKIP_LEMMA";
val _ = emit_exported "gcport_LAST_EQ_typed" "LAST_EQ";
val _ = emit_exported "gcport_NOT_NIL_IMP_LAST_typed" "NOT_NIL_IMP_LAST";
val _ = emit_exported "gcport_IS_SOME_IF_typed" "IS_SOME_IF";
val _ = emit_exported "gcport_IS_SOME_ALOOKUP_EQ_typed" "IS_SOME_ALOOKUP_EQ";
val _ = emit_exported "gcport_MEM_IMP_IS_SOME_ALOOKUP_typed" "MEM_IMP_IS_SOME_ALOOKUP";
val _ = emit_exported "gcport_SUBSET_INSERT_EQ_SUBSET_typed" "SUBSET_INSERT_EQ_SUBSET";
val _ = emit_exported "gcport_EVERY2_IMP_EL_typed" "EVERY2_IMP_EL";
val _ = emit_exported "gcport_FST_PAIR_EQ_typed" "FST_PAIR_EQ";
val _ = emit_exported "gcport_EVERY2_APPEND_IMP_typed" "EVERY2_APPEND_IMP";
val _ = emit_exported "gcport_ZIP_ID_typed" "ZIP_ID";
val _ = emit_exported "gcport_adjust_var_DIV_2_typed" "adjust_var_DIV_2";
val _ = emit_exported "gcport_adjust_var_DIV_2_ANY_typed" "adjust_var_DIV_2_ANY";
val _ = emit_exported "gcport_EVEN_adjust_var_typed" "EVEN_adjust_var";
val _ = emit_exported "gcport_adjust_var_eq_numeral_typed" "adjust_var_eq_numeral";
val _ = emit_exported "gcport_adjust_var_NEQ_0_typed" "adjust_var_NEQ_0";
val _ = emit_exported "gcport_adjust_var_NEQ_1_typed" "adjust_var_NEQ_1";
val _ = emit_exported "gcport_adjust_var_NEQ_typed" "adjust_var_NEQ";
val _ = emit_exported "gcport_unit_opt_eq_typed" "unit_opt_eq";
val _ = emit_exported "gcport_adjust_var_11_typed" "adjust_var_11";
val _ = emit_exported "gcport_none_opt_eq_typed" "none_opt_eq";
val _ = emit_exported "gcport_lookup_adjust_var_adjust_set_NONE_typed" "lookup_adjust_var_adjust_set_NONE";
val _ = emit_exported "gcport_lookup_adjust_var_adjust_set_SOME_UNIT_typed" "lookup_adjust_var_adjust_set_SOME_UNIT";
val _ = emit_exported "gcport_IMP_adjust_var_typed" "IMP_adjust_var";
val _ = emit_exported "gcport_unit_some_eq_IS_SOME_typed" "unit_some_eq_IS_SOME";
val _ = emit_exported "gcport_IS_SOME_lookup_domain_typed" "IS_SOME_lookup_domain";
val _ = emit_exported "gcport_one_and_or_1_typed" "one_and_or_1";
val _ = emit_exported "gcport_one_and_or_3_typed" "one_and_or_3";
val _ = emit_exported "gcport_ODD_not_zero_typed" "ODD_not_zero";
val _ = emit_exported "gcport_three_not_0_typed" "three_not_0";
val _ = emit_exported "gcport_three_and_shift_2_typed" "three_and_shift_2";
val _ = emit_exported "gcport_shift_to_zero_typed" "shift_to_zero";
val _ = emit_exported "gcport_shift_around_under_big_shift_typed" "shift_around_under_big_shift";
val _ = emit_exported "gcport_select_shift_out_typed" "select_shift_out";
val _ = emit_exported "gcport_shift_length_NOT_ZERO_typed" "shift_length_NOT_ZERO";
val _ = emit_exported "gcport_one_lsr_shift_length_typed" "one_lsr_shift_length";
val _ = emit_exported "gcport_is_fws_ptr_OR_3_typed" "is_fws_ptr_OR_3";
val _ = emit_exported "gcport_is_fws_ptr_OR_15_typed" "is_fws_ptr_OR_15";
val _ = emit_exported "gcport_is_fws_ptr_OR_10111_typed" "is_fws_ptr_OR_10111";
val _ = emit_exported "gcport_is_fws_ptr_OR_7_typed" "is_fws_ptr_OR_7";
val _ = emit_exported "gcport_select_get_lowerbits_typed" "select_get_lowerbits";
val _ = emit_exported "gcport_LE_DIV_LT_IMP_typed" "LE_DIV_LT_IMP";
val _ = emit_exported "gcport_word_bits_eq_slice_shift_typed" "word_bits_eq_slice_shift";
val _ = emit_exported "gcport_word_slice_or_typed" "word_slice_or";
val _ = emit_exported "gcport_word_slice_lsl_eq_0_typed" "word_slice_lsl_eq_0";
val _ = emit_exported "gcport_word_slice_2_3_eq_0_typed" "word_slice_2_3_eq_0";
val _ = emit_exported "gcport_can_select_def_typed" "can_select_def";
val _ = emit_exported "gcport_read_length_lemma_typed" "read_length_lemma";
val _ = emit_exported "gcport_LESS_EQ_IMP_APPEND_typed" "LESS_EQ_IMP_APPEND";
val _ = emit_exported "gcport_LIST_REL_EQ_MAP_typed" "LIST_REL_EQ_MAP";
val _ = emit_exported "gcport_gc_move_with_NIL_LEMMA_typed" "gc_move_with_NIL_LEMMA";
val _ = capture "gcport_gc_move_list_ok_irr0_typed" "gc_move_list_ok_irr0";
val _ = emit_exported "gcport_gc_move_list_ok_irr_typed" "gc_move_list_ok_irr";
val _ = emit_exported "gcport_gc_partial_move_ok_irr_typed" "gc_partial_move_ok_irr";
val _ = emit_exported "gcport_gc_partial_move_list_ok_irr_typed" "gc_partial_move_list_ok_irr";
val _ = emit_exported "gcport_gc_partial_move_list_ok_irr'_typed" "gc_partial_move_list_ok_irr'";
val _ = emit_exported "gcport_gc_partial_move_ref_list_ok_irr_typed" "gc_partial_move_ref_list_ok_irr";
val _ = emit_exported "gcport_gc_partial_move_with_NIL_LEMMA_typed" "gc_partial_move_with_NIL_LEMMA";
val _ = capture "gcport_gc_move_ref_list_IMP_typed" "gc_move_ref_list_IMP";
val _ = emit_exported "gcport_heap_length_LENGTH_typed" "heap_length_LENGTH";
val _ = emit_exported "gcport_gen_starts_in_store_IMP_SOME_Word_typed" "gen_starts_in_store_IMP_SOME_Word";
val _ = emit_exported "gcport_glob_real_inv_typed" "glob_real_inv";
val _ = emit_exported "gcport_heap_segment_IMP_split_typed" "heap_segment_IMP_split";
val _ = emit_exported "gcport_heap_split_IMP_heap_length_typed" "heap_split_IMP_heap_length";
val _ = emit_exported "gcport_heap_split_APPEND_EQ_typed" "heap_split_APPEND_EQ";
val _ = emit_exported "gcport_heap_split_IMP_APPEND_typed" "heap_split_IMP_APPEND";
val _ = emit_exported "gcport_heap_length_nil_typed" "heap_length_nil";
val _ = emit_exported "gcport_abs_ml_inv_GenState_IMP_heap_length_FILTER_typed" "abs_ml_inv_GenState_IMP_heap_length_FILTER";
val _ = capture "gcport_new_trig_ok_typed" "new_trig_ok";
val _ = emit_exported "gcport_byte_aligned_IMP_bytes_in_word_typed" "byte_aligned_IMP_bytes_in_word";
val _ = emit_exported "gcport_MULT_bytes_in_word_LESS_EQ_IMP_typed" "MULT_bytes_in_word_LESS_EQ_IMP";
val _ = capture "gcport_new_trig_LESS_EQ_typed" "new_trig_LESS_EQ";
val _ = emit_exported "gcport_word_gc_fun_lemma_typed" "word_gc_fun_lemma";
val _ = capture "gcport_abs_ml_inv_ADD_typed" "abs_ml_inv_ADD";
val _ = emit_exported "gcport_code_oracle_rel_NextFree_typed" "code_oracle_rel_NextFree";
val _ = emit_exported "gcport_state_rel_def_typed" "state_rel_def";
val _ = emit_exported "gcport_flat_NIL_typed" "flat_NIL";
val _ = capture "gcport_blocks_unique_empty_typed" "blocks_unique_empty";
val _ = emit_exported "gcport_state_rel_init_typed" "state_rel_init";
val _ = emit_exported "gcport_adjust_var_NOT_0_typed" "adjust_var_NOT_0";
val _ = emit_exported "gcport_LASTN_ADD1_typed" "LASTN_ADD1";
val _ = capture "gcport_is_some_lookup_union_typed" "is_some_lookup_union";
val _ = emit_exported "gcport_evaluate_IMP_inc_clock_typed" "evaluate_IMP_inc_clock";
val _ = emit_exported "gcport_evaluate_IMP_inc_clock_Ex_typed" "evaluate_IMP_inc_clock_Ex";
val _ = emit_exported "gcport_cut_env_adjust_sets_ODD_typed" "cut_env_adjust_sets_ODD";
val _ = emit_exported "gcport_cut_envs_adjust_sets_ODD_typed" "cut_envs_adjust_sets_ODD";
val _ = emit_exported "gcport_insert_insert_3_1_typed" "insert_insert_3_1";
val _ = emit_exported "gcport_shift_lsl_typed" "shift_lsl";
val _ = emit_exported "gcport_word_exp_rw_typed" "word_exp_rw";
val _ = emit_exported "gcport_get_var_set_var_thm_typed" "get_var_set_var_thm";
val _ = emit_exported "gcport_domain_adjust_set_EVEN_typed" "domain_adjust_set_EVEN";
val _ = emit_exported "gcport_cut_envs_adjust_sets_insert_ODD_typed" "cut_envs_adjust_sets_insert_ODD";
val _ = emit_exported "gcport_alloc_store_typed" "alloc_store";
val _ = emit_exported "gcport_cut_names_imp_wf_typed" "cut_names_imp_wf";
val _ = emit_exported "gcport_AllocVar_thm_typed" "AllocVar_thm";
val _ = emit_exported "gcport_state_rel_with_clock_0_typed" "state_rel_with_clock_0";
val _ = emit_exported "gcport_word_heap_non_empty_limit_typed" "word_heap_non_empty_limit";
val _ = emit_exported "gcport_small_int_0_typed" "small_int_0";
val _ = emit_exported "gcport_state_rel_imp_clock_typed" "state_rel_imp_clock";
val _ = emit "gcport_word_bits_def_typed" wordsTheory.word_bits_def;
