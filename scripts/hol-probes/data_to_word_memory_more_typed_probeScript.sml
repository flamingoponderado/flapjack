(* Typed captures for the data_to_word_memoryProofScript.sml declarations
   ported on the cakeml-memproof branch. Built like
   data_to_word_bignum_typed_probeScript.sml (see scripts/hol-probes/README.md):
   exported theorems and definitions are fetched from the theory DB and
   `[local]` theorems are parsed from the pinned source text. *)
load "preamble";
load "data_to_word_memoryProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open data_to_word_memoryProofTheory;
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
  case DB.lookup {Thy="data_to_word_memoryProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/data_to_word_memoryProofScript.sml";

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




val _ = print "dtw_memory_more_begin=1\n";
val _ = emit_exported "word_eq_typed" "word_eq";
val _ = emit_exported "ZIP_REPLICATE_typed" "ZIP_REPLICATE";
val _ = emit_exported "MEM_EL_APPEND_MID_typed" "MEM_EL_APPEND_MID";
val _ = emit_exported "MAX_LIST_sum_bound_typed" "MAX_LIST_sum_bound";
val _ = emit_exported "MAX_LIST_bounded_elements_typed" "MAX_LIST_bounded_elements";
val _ = emit_exported "MAX_LIST_MAP_typed" "MAX_LIST_MAP";
val _ = emit_exported "w2i_i2w_IMP_typed" "w2i_i2w_IMP";
val _ = emit_exported "word_i2w_sub_typed" "word_i2w_sub";
val _ = emit_exported "ThunkBlock_11_typed" "ThunkBlock_11";
val _ = emit_exported "MOD_EQ_0_0_typed" "MOD_EQ_0_0";
val _ = emit_exported "EVERY2_IMP_EVERY_typed" "EVERY2_IMP_EVERY";
val _ = emit_exported "EVERY2_IMP_EVERY2_typed" "EVERY2_IMP_EVERY2";
val _ = emit_exported "MEM_EVERY2_IMP_typed" "MEM_EVERY2_IMP";
val _ = emit_exported "EVERY2_APPEND_CONS_typed" "EVERY2_APPEND_CONS";
val _ = emit_exported "EVERY2_SWAP_typed" "EVERY2_SWAP";
val _ = emit_exported "EVERY2_APPEND_IMP_APPEND_typed" "EVERY2_APPEND_IMP_APPEND";
val _ = capture "EVERY2_MAP_FST_SND_typed" "EVERY2_MAP_FST_SND";
val _ = capture "heap_lookup_APPEND1_typed" "heap_lookup_APPEND1";
val _ = capture "heap_lookup_APPEND2_typed" "heap_lookup_APPEND2";
val _ = emit_exported "heap_lookup_APPEND_typed" "heap_lookup_APPEND";
val _ = capture "LENGTH_ADDR_MAP_typed" "LENGTH_ADDR_MAP";
val _ = capture "EL_ADDR_MAP_typed" "EL_ADDR_MAP";
val _ = emit_exported "dest_evaluated_thunk_rel_rules_typed" "dest_evaluated_thunk_rel_rules";
val _ = emit_exported "dest_evaluated_thunk_rel_cases_typed" "dest_evaluated_thunk_rel_cases";
val _ = emit_exported "evaluated_thunk_ptr_def_typed" "evaluated_thunk_ptr_def";
val _ = emit "MAX_LIST_def_typed" (DB.fetch "rich_list" "MAX_LIST_def");
val _ = emit "f_o_f_DEF_typed" (DB.fetch "finite_map" "f_o_f_DEF");
val _ = capture "v_inv_related_lemma_typed" "v_inv_related_lemma";
val _ = capture "v_inv_related_typed" "v_inv_related";
val _ = capture "EVERY2_ADDR_MAP_typed" "EVERY2_ADDR_MAP";
val _ = capture "bc_ref_inv_related_typed" "bc_ref_inv_related";
val _ = emit_exported "gc_inline_rel_rules_typed" "gc_inline_rel_rules";
val _ = emit_exported "gc_inline_rel_cases_typed" "gc_inline_rel_cases";
val _ = emit_exported "gc_heap_inline_rel_rules_typed" "gc_heap_inline_rel_rules";
val _ = emit_exported "gc_heap_inline_rel_cases_typed" "gc_heap_inline_rel_cases";
val _ = emit_exported "gc_inline_def_typed" "gc_inline_def";
val _ = emit_exported "gc_related_roots_heap_def_typed" "gc_related_roots_heap_def";
val _ = emit_exported "gc_inline_related_def_typed" "gc_inline_related_def";
val _ = capture "gc_heap_inline_rel_heap_lookup_typed" "gc_heap_inline_rel_heap_lookup";
val _ = capture "ThunkBlock_not_EQ_typed" "ThunkBlock_not_EQ";
val _ = capture "LIST_REL_gc_heap_inline_DataElement_typed" "LIST_REL_gc_heap_inline_DataElement";
val _ = capture "gc_heap_inline_rel_v_inv_lemma_typed" "gc_heap_inline_rel_v_inv_lemma";
val _ = capture "gc_heap_inline_rel_v_inv_typed" "gc_heap_inline_rel_v_inv";
val _ = capture "bc_stack_ref_inv_gc_inline_typed" "bc_stack_ref_inv_gc_inline";
val _ = capture "bc_stack_ref_inv_gc_related_roots_heap_typed" "bc_stack_ref_inv_gc_related_roots_heap";
val _ = capture "bc_stack_ref_inv_related_typed" "bc_stack_ref_inv_related";
val _ = emit_exported "data_up_to_APPEND_typed" "data_up_to_APPEND";
val _ = capture "gc_move_data_refs_split_typed" "gc_move_data_refs_split";
val _ = capture "gc_move_list_data_refs_split_typed" "gc_move_list_data_refs_split";
val _ = capture "gc_move_refs_data_refs_split_typed" "gc_move_refs_data_refs_split";
val _ = capture "gc_move_data_data_refs_split_typed" "gc_move_data_data_refs_split";
val _ = capture "gc_move_loop_data_refs_split_typed" "gc_move_loop_data_refs_split";
val _ = emit_exported "heap_expand_not_isRef_typed" "heap_expand_not_isRef";
val _ = emit_exported "gen_state_ok_reset_typed" "gen_state_ok_reset";
val _ = emit_exported "heap_split_heap_split_typed" "heap_split_heap_split";
val _ = emit_exported "heap_split_LESS_EQ_typed" "heap_split_LESS_EQ";
val _ = capture "isRef_heap_expand_typed" "isRef_heap_expand";
val _ = emit_exported "isUnused_def_typed" "isUnused_def";
val _ = emit_exported "isSomeUnused_def_typed" "isSomeUnused_def";
val _ = emit_exported "isDataElement_lemmas_typed" "isDataElement_lemmas";
val _ = emit_exported "list_to_BlockReps_def_typed" "list_to_BlockReps_def";
val _ = emit_exported "list_to_BlockReps_heap_length_typed" "list_to_BlockReps_heap_length";
val _ = emit_exported "heap_lookup_heap_length_typed" "heap_lookup_heap_length";
val _ = emit_exported "list_to_BlockReps_heap_lookup_0_typed" "list_to_BlockReps_heap_lookup_0";
val _ = emit_exported "list_to_BlockReps_isDataElement_typed" "list_to_BlockReps_isDataElement";
val _ = capture "list_to_BlockReps_data_up_to_lem_typed" "list_to_BlockReps_data_up_to_lem";
val _ = emit_exported "list_to_BlockReps_data_up_to_typed" "list_to_BlockReps_data_up_to";
val _ = emit_exported "list_to_BlockReps_ForwardPointer_typed" "list_to_BlockReps_ForwardPointer";
val _ = emit_exported "list_to_BlockReps_Ref_typed" "list_to_BlockReps_Ref";
val _ = emit_exported "list_to_BlockReps_NULL_typed" "list_to_BlockReps_NULL";
val _ = emit_exported "list_to_BlockReps_MEM_typed" "list_to_BlockReps_MEM";
val _ = capture "list_to_BlockReps_Pointer_lem_typed" "list_to_BlockReps_Pointer_lem";
val _ = emit_exported "list_to_BlockReps_Pointer_typed" "list_to_BlockReps_Pointer";
val _ = emit_exported "list_to_v_get_refs_typed" "list_to_v_get_refs";
val _ = emit_exported "all_ts_cons_typed" "all_ts_cons";
val _ = emit_exported "all_ts_in_no_block_typed" "all_ts_in_no_block";
val _ = emit_exported "all_ts_append_typed" "all_ts_append";
val _ = emit_exported "all_ts_head_typed" "all_ts_head";
val _ = capture "v_inv_SUBMAP_lemma_typed" "v_inv_SUBMAP_lemma";
val _ = capture "v_inv_lemma_2448_typed" "v_inv_lemma";
val _ = emit_exported "v_inv_lemma_2504_typed" "v_inv_lemma";
val _ = emit_exported "v_inv_LIST_REL_typed" "v_inv_LIST_REL";
val _ = emit_exported "bind_each_def_typed" "bind_each_def";
val _ = emit_exported "bind_each_MONO_typed" "bind_each_MONO";
val _ = emit_exported "bind_each_SUBMAP_typed" "bind_each_SUBMAP";
val _ = emit_exported "v_all_vs_MEM_typed" "v_all_vs_MEM";
val _ = emit_exported "v_in_all_vs_typed" "v_in_all_vs";
val _ = emit_exported "v_all_vs_trans_typed" "v_all_vs_trans";
val _ = emit_exported "MEM_in_all_vs_typed" "MEM_in_all_vs";
val _ = emit_exported "v_inv_tf_update_thm_lemma_typed" "v_inv_tf_update_thm_lemma";
val _ = emit_exported "v_inv_tf_update_thm_typed" "v_inv_tf_update_thm";
val _ = emit_exported "MEM_v_all_vs_split_typed" "MEM_v_all_vs_split";
val _ = emit_exported "MEM_v_all_vs_split2_typed" "MEM_v_all_vs_split2";
val _ = emit_exported "MEM_v_all_vs_extend_tl_typed" "MEM_v_all_vs_extend_tl";
val _ = emit_exported "MEM_v_all_vs_extend_hd_typed" "MEM_v_all_vs_extend_hd";
val _ = emit_exported "MEM_v_all_vs_extend_append_typed" "MEM_v_all_vs_extend_append";
val _ = emit_exported "MEM_v_all_vs_EL_typed" "MEM_v_all_vs_EL";
val _ = emit_exported "MEM_v_all_vs_LUPDATE_typed" "MEM_v_all_vs_LUPDATE";
val _ = emit_exported "all_vs_Block_typed" "all_vs_Block";
val _ = emit_exported "blocks_unique_cons_thm_typed" "blocks_unique_cons_thm";
val _ = capture "ref_edge_ValueArray_typed" "ref_edge_ValueArray";
val _ = capture "ref_edge_Thunk_typed" "ref_edge_Thunk";
val _ = capture "reachable_refs_UPDATE_typed" "reachable_refs_UPDATE";
val _ = capture "reachable_refs_Thunk_UPDATE_typed" "reachable_refs_Thunk_UPDATE";
val _ = capture "reachable_refs_UPDATE1_typed" "reachable_refs_UPDATE1";
val _ = emit_exported "v_inv_ByteArray_insert_lemma_typed" "v_inv_ByteArray_insert_lemma";
val _ = capture "heap_lookup_RefBlock_lemma_typed" "heap_lookup_RefBlock_lemma";
val _ = capture "heap_store_RefBlock_typed" "heap_store_RefBlock";
val _ = capture "NOT_isRefBlock_typed" "NOT_isRefBlock";
val _ = capture "v_inv_Ref_lemma_typed" "v_inv_Ref_lemma";
val _ = capture "v_inv_Ref_typed" "v_inv_Ref";
val _ = emit_exported "v_inv_ValueArray_insert_lemma_typed" "v_inv_ValueArray_insert_lemma";
val _ = emit_exported "v_inv_MutBlock_insert_lemma_typed" "v_inv_MutBlock_insert_lemma";
val _ = emit_exported "v_inv_MutBlock_insert_typed" "v_inv_MutBlock_insert";
val _ = capture "v_inv_MutBlock_fin_lemma_typed" "v_inv_MutBlock_fin_lemma";
val _ = emit_exported "v_inv_MutBlock_fin_typed" "v_inv_MutBlock_fin";
val _ = capture "all_ts_SUBSET_gen_typed" "all_ts_SUBSET_gen";
val _ = capture "all_ts_SUBSET_ts_typed" "all_ts_SUBSET_ts";
val _ = capture "all_ts_mutcons_typed" "all_ts_mutcons";
val _ = capture "blocks_unique_mutcons_typed" "blocks_unique_mutcons";
val _ = capture "ref_edge_MutBlock_typed" "ref_edge_MutBlock";
val _ = capture "reachable_refs_MutCons_lemma_typed" "reachable_refs_MutCons_lemma";
val _ = capture "reachable_refs_MutCons_typed" "reachable_refs_MutCons";
val _ = capture "take_el_drop_typed" "take_el_drop";
val _ = capture "dest_thunk_insert_fresh_typed" "dest_thunk_insert_fresh";
val _ = emit_exported "heap_store_ThunkBlock_thm_typed" "heap_store_ThunkBlock_thm";
val _ = capture "heap_lookup_ThunkBlock_lemma_typed" "heap_lookup_ThunkBlock_lemma";
val _ = capture "heap_store_ThunkBlock_typed" "heap_store_ThunkBlock";
val _ = emit_exported "INJ_NEQ_typed" "INJ_NEQ";
val _ = capture "heap_lookup_heap_split_typed" "heap_lookup_heap_split";
val _ = emit_exported "heap_store_heap_lookup_typed" "heap_store_heap_lookup";
val _ = capture "data_up_to_alt_typed" "data_up_to_alt";
val _ = emit_exported "data_up_to_heap_store_typed" "data_up_to_heap_store";
val _ = emit_exported "blocks_unique_update_thunk_typed" "blocks_unique_update_thunk";
val _ = emit_exported "thunk_deref_def_typed" "thunk_deref_def";
val _ = capture "heap_store_BlockRep_thm_typed" "heap_store_BlockRep_thm";
val _ = capture "heap_lookup_BlockRep_lemma_typed" "heap_lookup_BlockRep_lemma";
val _ = capture "heap_store_BlockRep_typed" "heap_store_BlockRep";
val _ = capture "v_inv_MutBlock_hole_lemma_typed" "v_inv_MutBlock_hole_lemma";
val _ = capture "v_inv_MutBlock_hole_typed" "v_inv_MutBlock_hole";
val _ = capture "blocks_unique_update_mutblock_typed" "blocks_unique_update_mutblock";
val _ = capture "ref_edge_MutBlock_UPDATE_typed" "ref_edge_MutBlock_UPDATE";
val _ = capture "reachable_refs_MutBlock_UPDATE_typed" "reachable_refs_MutBlock_UPDATE";
val _ = capture "LIST_REL_IMP_LIST_REL_typed" "LIST_REL_IMP_LIST_REL";
val _ = capture "v_inv_IMP_lemma_typed" "v_inv_IMP_lemma";
val _ = capture "v_inv_IMP_typed" "v_inv_IMP";
val _ = capture "gen_state_ok_update_byte_typed" "gen_state_ok_update_byte";
val _ = emit_exported "heap_length_Bytes_typed" "heap_length_Bytes";
val _ = capture "unused_space_inv_byte_update_typed" "unused_space_inv_byte_update";
val _ = emit_exported "blocks_unique_deref1_typed" "blocks_unique_deref1";
val _ = emit_exported "blocks_unique_deref2_typed" "blocks_unique_deref2";
val _ = emit_exported "small_int_IMP_MIN_MAX_typed" "small_int_IMP_MIN_MAX";
val _ = emit_exported "all_ts_permute_typed" "all_ts_permute";
val _ = emit_exported "pointer_bits_def_typed" "pointer_bits_def";
val _ = emit_exported "is_all_ones_def_typed" "is_all_ones_def";
val _ = emit_exported "decode_maxout_def_typed" "decode_maxout_def";
val _ = emit_exported "decode_addr_def_typed" "decode_addr_def";
val _ = emit_exported "heap_el_def_typed" "heap_el_def";
val _ = print "dtw_memory_more_end=1\n";
