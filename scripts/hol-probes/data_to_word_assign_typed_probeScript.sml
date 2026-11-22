(* Typed captures for the data_to_word_assignProof reviewed rows that earlier probes did not
   cover (task 184). The theory is built in a private copy of the pinned CakeML
   tree (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path. Exported theorems and definitions are
   fetched from the theory DB; `[local]` theorems are parsed from the pinned
   source text with SML antiquotation splices expanded; derived theorems and
   `val ... = Q.prove(...)` lemmas are captured through the statement named in
   each comment. *)
load "preamble";
load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open data_to_word_assignProofTheory;
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
  case DB.lookup {Thy="data_to_word_assignProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/data_to_word_assignProofScript.sml";

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


val _ = emit_exported "size_of_seen_SUBSET_typed" "size_of_seen_SUBSET";
val _ = emit_exported "size_of_seen_Block_typed" "size_of_seen_Block";
val _ = emit_exported "IMP_read_bytearray_GENLIST_typed" "IMP_read_bytearray_GENLIST";
val _ = print ("state_rel_get_var_Number_IMP_alt_hypotheses=" ^
  Int.toString (length (hyp state_rel_get_var_Number_IMP_alt)) ^ "\n");
val _ = emit_exported "state_rel_get_var_Number_IMP_alt_typed" "state_rel_get_var_Number_IMP_alt";
val _ = print ("state_rel_IMP_tstamps_hypotheses=" ^
  Int.toString (length (hyp state_rel_IMP_tstamps)) ^ "\n");
val _ = emit_exported "state_rel_IMP_tstamps_typed" "state_rel_IMP_tstamps";
val _ = print ("INT_EQ_NUM_LEMMA_hypotheses=" ^
  Int.toString (length (hyp INT_EQ_NUM_LEMMA)) ^ "\n");
val _ = emit_exported "INT_EQ_NUM_LEMMA_typed" "INT_EQ_NUM_LEMMA";
val _ = print ("evaluate_Maxout_bits_code_hypotheses=" ^
  Int.toString (length (hyp evaluate_Maxout_bits_code)) ^ "\n");
val _ = emit_exported "evaluate_Maxout_bits_code_typed" "evaluate_Maxout_bits_code";
val _ = print ("Make_ptr_bits_thm_hypotheses=" ^
  Int.toString (length (hyp Make_ptr_bits_thm)) ^ "\n");
val _ = emit_exported "Make_ptr_bits_thm_typed" "Make_ptr_bits_thm";
val _ = print ("assign_ConsExtend_hypotheses=" ^
  Int.toString (length (hyp assign_ConsExtend)) ^ "\n");
val _ = emit_exported "assign_ConsExtend_typed" "assign_ConsExtend";
val _ = print ("assign_Cons_hypotheses=" ^
  Int.toString (length (hyp assign_Cons)) ^ "\n");
val _ = emit_exported "assign_Cons_typed" "assign_Cons";
val _ = print ("assign_Build_hypotheses=" ^
  Int.toString (length (hyp assign_Build)) ^ "\n");
val _ = emit_exported "assign_Build_typed" "assign_Build";
val _ = print ("assign_WordTest_hypotheses=" ^
  Int.toString (length (hyp assign_WordTest)) ^ "\n");
val _ = emit_exported "assign_WordTest_typed" "assign_WordTest";
val _ = print ("assign_LessConstSmall_hypotheses=" ^
  Int.toString (length (hyp assign_LessConstSmall)) ^ "\n");
val _ = emit_exported "assign_LessConstSmall_typed" "assign_LessConstSmall";
val _ = print ("assign_LessSmallConst_hypotheses=" ^
  Int.toString (length (hyp assign_LessSmallConst)) ^ "\n");
val _ = emit_exported "assign_LessSmallConst_typed" "assign_LessSmallConst";
val _ = print ("state_rel_upd_safe_pkheap_hypotheses=" ^
  Int.toString (length (hyp state_rel_upd_safe_pkheap)) ^ "\n");
val _ = emit_exported "state_rel_upd_safe_pkheap_typed" "state_rel_upd_safe_pkheap";
val _ = print ("state_rel_ignore_safe_for_space_hypotheses=" ^
  Int.toString (length (hyp state_rel_ignore_safe_for_space)) ^ "\n");
val _ = emit_exported "state_rel_ignore_safe_for_space_typed" "state_rel_ignore_safe_for_space";
val _ = print ("state_rel_peak_heap_length_hypotheses=" ^
  Int.toString (length (hyp state_rel_peak_heap_length)) ^ "\n");
val _ = emit_exported "state_rel_peak_heap_length_typed" "state_rel_peak_heap_length";
val _ = print ("opt_map_plus_zero_id_hypotheses=" ^
  Int.toString (length (hyp opt_map_plus_zero_id)) ^ "\n");
val _ = emit_exported "opt_map_plus_zero_id_typed" "opt_map_plus_zero_id";
val _ = print ("small_num_small_int_hypotheses=" ^
  Int.toString (length (hyp small_num_small_int)) ^ "\n");
val _ = emit_exported "small_num_small_int_typed" "small_num_small_int";
val _ = print ("memory_rel_small_int_hypotheses=" ^
  Int.toString (length (hyp memory_rel_small_int)) ^ "\n");
val _ = emit_exported "memory_rel_small_int_typed" "memory_rel_small_int";
val _ = print ("small_int_Smallnum_add_hypotheses=" ^
  Int.toString (length (hyp small_int_Smallnum_add)) ^ "\n");
val _ = emit_exported "small_int_Smallnum_add_typed" "small_int_Smallnum_add";
val _ = print ("small_int_INT_MIN_MAX_hypotheses=" ^
  Int.toString (length (hyp small_int_INT_MIN_MAX)) ^ "\n");
val _ = emit_exported "small_int_INT_MIN_MAX_typed" "small_int_INT_MIN_MAX";
val _ = print ("small_int_w2i_Smallnum_add_hypotheses=" ^
  Int.toString (length (hyp small_int_w2i_Smallnum_add)) ^ "\n");
val _ = emit_exported "small_int_w2i_Smallnum_add_typed" "small_int_w2i_Smallnum_add";
val _ = print ("state_rel_IMP_arch_64_bit_hypotheses=" ^
  Int.toString (length (hyp state_rel_IMP_arch_64_bit)) ^ "\n");
val _ = emit_exported "state_rel_IMP_arch_64_bit_typed" "state_rel_IMP_arch_64_bit";
val _ = print ("cut_state_opt_twice_hypotheses=" ^
  Int.toString (length (hyp cut_state_opt_twice)) ^ "\n");
val _ = emit_exported "cut_state_opt_twice_typed" "cut_state_opt_twice";
val _ = print ("cut_state_opt_extra_const_hypotheses=" ^
  Int.toString (length (hyp cut_state_opt_extra_const)) ^ "\n");
val _ = emit_exported "cut_state_opt_extra_const_typed" "cut_state_opt_extra_const";
val _ = print ("small_int_Smallnum_sub_hypotheses=" ^
  Int.toString (length (hyp small_int_Smallnum_sub)) ^ "\n");
val _ = emit_exported "small_int_Smallnum_sub_typed" "small_int_Smallnum_sub";
val _ = print ("small_int_w2i_Smallnum_sub_hypotheses=" ^
  Int.toString (length (hyp small_int_w2i_Smallnum_sub)) ^ "\n");
val _ = emit_exported "small_int_w2i_Smallnum_sub_typed" "small_int_w2i_Smallnum_sub";
val _ = print ("cut_state_opt_IMP_ffi_hypotheses=" ^
  Int.toString (length (hyp cut_state_opt_IMP_ffi)) ^ "\n");
val _ = emit_exported "cut_state_opt_IMP_ffi_typed" "cut_state_opt_IMP_ffi";
val _ = print ("quad_times_div_half_double_hypotheses=" ^
  Int.toString (length (hyp quad_times_div_half_double)) ^ "\n");
val _ = emit_exported "quad_times_div_half_double_typed" "quad_times_div_half_double";
val _ = print ("w2n_mul_less_hypotheses=" ^
  Int.toString (length (hyp w2n_mul_less)) ^ "\n");
val _ = emit_exported "w2n_mul_less_typed" "w2n_mul_less";
val _ = capture "word_bit_0_sub_lemma_typed" "word_bit_0_sub_lemma";
val _ = print ("word_bit_lsr_dimindex_1_hypotheses=" ^
  Int.toString (length (hyp word_bit_lsr_dimindex_1)) ^ "\n");
val _ = emit_exported "word_bit_lsr_dimindex_1_typed" "word_bit_lsr_dimindex_1";
val _ = print ("state_rel_Number_IMP_hypotheses=" ^
  Int.toString (length (hyp state_rel_Number_IMP)) ^ "\n");
val _ = emit_exported "state_rel_Number_IMP_typed" "state_rel_Number_IMP";
val _ = print ("option_le_add_comm_hypotheses=" ^
  Int.toString (length (hyp option_le_add_comm)) ^ "\n");
val _ = emit_exported "option_le_add_comm_typed" "option_le_add_comm";
val _ = print ("IN_adjust_set_IN_hypotheses=" ^
  Int.toString (length (hyp IN_adjust_set_IN)) ^ "\n");
val _ = emit_exported "IN_adjust_set_IN_typed" "IN_adjust_set_IN";
val _ = print ("assign_LengthByte_hypotheses=" ^
  Int.toString (length (hyp assign_LengthByte)) ^ "\n");
val _ = emit_exported "assign_LengthByte_typed" "assign_LengthByte";
val _ = print ("assign_Length_hypotheses=" ^
  Int.toString (length (hyp assign_Length)) ^ "\n");
val _ = emit_exported "assign_Length_typed" "assign_Length";
val _ = print ("assign_LengthBlock_hypotheses=" ^
  Int.toString (length (hyp assign_LengthBlock)) ^ "\n");
val _ = emit_exported "assign_LengthBlock_typed" "assign_LengthBlock";
val _ = capture "assign_BoundsCheckBlock_equation_typed" "assign_BoundsCheckBlock";
val _ = print ("assign_BoundsCheckBlock_hypotheses=" ^
  Int.toString (length (hyp assign_BoundsCheckBlock)) ^ "\n");
val _ = emit_exported "assign_BoundsCheckBlock_typed" "assign_BoundsCheckBlock";
val _ = capture "assign_BoundsCheckArray_equation_typed" "assign_BoundsCheckArray";
val _ = print ("assign_BoundsCheckArray_hypotheses=" ^
  Int.toString (length (hyp assign_BoundsCheckArray)) ^ "\n");
val _ = emit_exported "assign_BoundsCheckArray_typed" "assign_BoundsCheckArray";
val _ = capture "assign_BoundsCheckByte_equation_typed" "assign_BoundsCheckByte";
val _ = print ("assign_BoundsCheckByte_hypotheses=" ^
  Int.toString (length (hyp assign_BoundsCheckByte)) ^ "\n");
val _ = emit_exported "assign_BoundsCheckByte_typed" "assign_BoundsCheckByte";
val _ = capture "parts_to_words_NONE_typed" "parts_to_words_NONE";
(* Sweep batch A: remaining small lemmas of data_to_word_assignProof. Exported
   theorems from the theory DB, [local] ones parsed from the pinned source;
   ADD4DIV4/ADD8DIV8 rebuilt by the source's rule from ADD_DIV_ADD_DIV. *)
fun cap label name =
  case DB.lookup {Thy="data_to_word_assignProof",Name=name} of
    SOME (th,_) => emit label th
  | NONE => capture label name;
val _ = cap "get_vars_SING_typed" "get_vars_SING";
val _ = cap "push_if_typed" "push_if";
val _ = cap "split_if_typed" "split_if";
val _ = cap "cut_env_IMP_domain_typed" "cut_env_IMP_domain";
val _ = cap "domain_list_insert_thm_typed" "domain_list_insert_thm";
val _ = cap "word_less_lemma1_typed" "word_less_lemma1";
val _ = cap "get_vars_2_imp_typed" "get_vars_2_imp";
val _ = cap "get_vars_1_imp_typed" "get_vars_1_imp";
val _ = cap "LESS_DIV_16_IMP_typed" "LESS_DIV_16_IMP";
val _ = cap "encode_header_IMP_BIT0_typed" "encode_header_IMP_BIT0";
val _ = cap "lookup_IMP_insert_EQ_typed" "lookup_IMP_insert_EQ";
val _ = cap "set_vars_sing_typed" "set_vars_sing";
val _ = cap "NONNEG_INT_typed" "NONNEG_INT";
val _ = cap "BIT_X_1_typed" "BIT_X_1";
val _ = cap "minus_2_word_and_id_typed" "minus_2_word_and_id";
val _ = cap "FOUR_MUL_LSL_typed" "FOUR_MUL_LSL";
val _ = cap "EXISTS_NOT_IN_spt_DOMAIN_typed" "EXISTS_NOT_IN_spt_DOMAIN";
val _ = cap "LEAST_NOTIN_spt_DOMAIN_typed" "LEAST_NOTIN_spt_DOMAIN";
val _ = cap "option_le_add_indv_typed" "option_le_add_indv";
val _ = cap "option_le_add_drop_right_typed" "option_le_add_drop_right";
val _ = cap "byte_aligned_bytes_in_word_typed" "byte_aligned_bytes_in_word";
val _ = cap "is_env_def_typed" "is_env_def";
val _ = emit "ADD4DIV4_typed" (arithmeticTheory.ADD_DIV_ADD_DIV |> Q.SPEC `4` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[] |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM]);
val _ = emit "ADD8DIV8_typed" (arithmeticTheory.ADD_DIV_ADD_DIV |> Q.SPEC `8` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[] |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM]);
val _ = cap "EXP_LEMMA1_typed" "EXP_LEMMA1";
val _ = cap "Num_ABS_AND_typed" "Num_ABS_AND";
val _ = cap "word_bit_test_0_typed" "word_bit_test_0";
val _ = cap "MAP_Number_11_w2n_word8_typed" "MAP_Number_11_w2n_word8";
val _ = cap "MAP_Word64_11_typed" "MAP_Word64_11";
val _ = cap "v_to_list_EQ_SOME_NIL_typed" "v_to_list_EQ_SOME_NIL";
val _ = cap "LENGTH_EQ_4_typed" "LENGTH_EQ_4";

(* Batch A2: further small lemmas of data_to_word_assignProof and the w2w_upper definition. *)
val _ = cap "Word64Rep_inj_typed" "Word64Rep_inj";
val _ = cap "get_addr_inj_typed" "get_addr_inj";
val _ = cap "word_exp_SmallLsr_typed" "word_exp_SmallLsr";
val _ = cap "w2w_shift_shift_typed" "w2w_shift_shift";
val _ = cap "size_of_Number_head_typed" "size_of_Number_head";
val _ = cap "MAP_FST_MAP_compile_part_typed" "MAP_FST_MAP_compile_part";
val _ = cap "compile_part_loc_IMP_typed" "compile_part_loc_IMP";
val _ = cap "LENGTH_EQ_5_typed" "LENGTH_EQ_5";
val _ = cap "IN_domain_adjust_set_inter_typed" "IN_domain_adjust_set_inter";
val _ = cap "good_dimindex_w2w_byte_typed" "good_dimindex_w2w_byte";
val _ = cap "set_var_consts_typed" "set_var_consts";
val _ = cap "get_var_consts_typed" "get_var_consts";
val _ = cap "not_less_zero_int_eq_typed" "not_less_zero_int_eq";
val _ = cap "IS_SOME_lookup_typed" "IS_SOME_lookup";
val _ = cap "OPTION_MAP2_NONE_THM_typed" "OPTION_MAP2_NONE_THM";
val _ = cap "OPTION_MAP2_NONE_typed" "OPTION_MAP2_NONE";
val _ = cap "option_le_flip_neg_typed" "option_le_flip_neg";
val _ = cap "the_F_not_option_le_typed" "the_F_not_option_le";
val _ = cap "not_the_F_option_le_typed" "not_the_F_option_le";
val _ = cap "lookup_set_var_typed" "lookup_set_var";
val _ = cap "TWO_POW_LEMMA_typed" "TWO_POW_LEMMA";
val _ = cap "w2w_upper_def_typed" "w2w_upper_def";
val _ = cap "w2w_upper_upper_w2w_typed" "w2w_upper_upper_w2w";
val _ = cap "cut_names_adjust_set_insert_1_typed" "cut_names_adjust_set_insert_1";
val _ = cap "cut_names_adjust_set_insert_3_typed" "cut_names_adjust_set_insert_3";
val _ = cap "cut_names_adjust_set_insert_5_typed" "cut_names_adjust_set_insert_5";
val _ = cap "push_env_tstamps_typed" "push_env_tstamps";
val _ = cap "dec_clock_tstamps_typed" "dec_clock_tstamps";
val _ = cap "cut_state_refs_same_typed" "cut_state_refs_same";
(* lookup_2_call_env is [local]; its source proof uses
   wordSemTheory.call_env_def and lookup_fromList2, so at its source position
   `call_env` is wordSem's. The probe's final grammar resolves the bare name
   to dataSem's call_env instead, so the source statement is parsed with that
   one identifier qualified as wordSem$call_env. *)
fun subst_str (pat, rep) str =
  let
    val n = String.size pat
    fun go i acc =
      if i + n > String.size str then String.concat (rev (String.extract (str, i, NONE) :: acc))
      else if String.substring (str, i, n) = pat then go (i + n) (rep :: acc)
      else go (i + 1) (String.str (String.sub (str, i)) :: acc)
  in go 0 [] end;
val _ = let
    val stmt = subst_str ("call_env", "wordSem$call_env")
      (strip_antiquote (statement_of "lookup_2_call_env"))
    val tm = Parse.Term [QUOTE stmt]
  in (print "lookup_2_call_env_typed="; print_term tm; print "\n") end;
val _ = cap "toList_delete_split_typed" "toList_delete_split";
val _ = cap "wf_FOLDR_delete_typed" "wf_FOLDR_delete";
val _ = cap "lookup_FOLDR_delete_typed" "lookup_FOLDR_delete";
val _ = cap "v_to_list_block_drop_typed" "v_to_list_block_drop";
val _ = cap "push_env_store_typed" "push_env_store";
val _ = cap "cut_env_envs_lookup_lookup_typed" "cut_env_envs_lookup_lookup";
val _ = cap "cut_envs_domain_IN_typed" "cut_envs_domain_IN";
val _ = cap "consume_space_stack_max_typed" "consume_space_stack_max";
val _ = cap "lookup_loc_lemma_typed" "lookup_loc_lemma";
val _ = cap "LESS_IMP_NOT_BIT_typed" "LESS_IMP_NOT_BIT";
val _ = cap "Smallnum_alt_typed" "Smallnum_alt";
val _ = cap "BIT_lemma_typed" "BIT_lemma";
val _ = cap "BIT_Lemma2_typed" "BIT_Lemma2";
val _ = cap "MULT_TWO_EXP_LESS_dimword_typed" "MULT_TWO_EXP_LESS_dimword";
val _ = cap "explode_less_32_typed" "explode_less_32";
val _ = cap "WordFromInt_DIV_LEMMA_typed" "WordFromInt_DIV_LEMMA";
val _ = cap "LENGTH_n2mw_1_typed" "LENGTH_n2mw_1";
val _ = cap "all_ones_get_addr_typed" "all_ones_get_addr";
val _ = cap "maxout_bits_eq_typed" "maxout_bits_eq";
val _ = cap "word_or_eq_word_or_split_typed" "word_or_eq_word_or_split";
val _ = cap "ptr_bits_eq_ptr_bits_typed" "ptr_bits_eq_ptr_bits";
val _ = cap "maxout_bits_0_typed" "maxout_bits_0";
val _ = cap "ptr_bits_eq_ptr_bits_len_only_typed" "ptr_bits_eq_ptr_bits_len_only";
val _ = cap "all_ones_and_1_typed" "all_ones_and_1";
val _ = cap "all_ones_and_ptr_bits_tag_0_typed" "all_ones_and_ptr_bits_tag_0";

(* Batch A3: call/push lifting, word_exp and push_env_loc lemmas. *)
val _ = cap "call_env_push_env_dec_clock_lift_typed" "call_env_push_env_dec_clock_lift";
val _ = cap "call_env_push_env_dec_clock_lift_locals_typed" "call_env_push_env_dec_clock_lift_locals";
val _ = cap "call_env_push_env_dec_clock_stack_max_typed" "call_env_push_env_dec_clock_stack_max";
val _ = cap "get_var_to_word_exp_typed" "get_var_to_word_exp";
val _ = cap "word_exp_set_typed" "word_exp_set";
val _ = cap "state_rel_push_env_loc_typed" "state_rel_push_env_loc";

(* Batch A4: heap-size, memory-relation and state-relation lemmas. *)
val _ = cap "option_le_stackmax_bridge_typed" "option_le_stackmax_bridge";
val _ = cap "size_of_app_Number_typed" "size_of_app_Number";
val _ = cap "size_of_heap_delete_Number_LE_typed" "size_of_heap_delete_Number_LE";
val _ = cap "size_of_heap_FOLDR_delete_Number_LE_typed" "size_of_heap_FOLDR_delete_Number_LE";
val _ = cap "evaluate_LoadWord64_typed" "evaluate_LoadWord64";
val _ = cap "memory_rel_ignore_buffers_typed" "memory_rel_ignore_buffers";
val _ = cap "memory_rel_get_num_typed" "memory_rel_get_num";
val _ = cap "state_rel_IMP_test_zero_typed" "state_rel_IMP_test_zero";

(* Batch A6: STOP_def, evaluate_MakeBytes and state_rel_get_var_Number_IMP,
   plus the compiler definitions MakeBytes_def, WriteLastByte_aux_def and
   WriteLastBytes_def from the data_to_word theory. *)
val _ = cap "STOP_def_typed" "STOP_def";
val _ = cap "evaluate_MakeBytes_typed" "evaluate_MakeBytes";
val _ = cap "state_rel_get_var_Number_IMP_typed" "state_rel_get_var_Number_IMP";
val _ = emit "MakeBytes_def_typed" (DB.fetch "data_to_word" "MakeBytes_def");
val _ = emit "WriteLastByte_aux_def_typed" (DB.fetch "data_to_word" "WriteLastByte_aux_def");
val _ = emit "WriteLastBytes_def_typed" (DB.fetch "data_to_word" "WriteLastBytes_def");

(* Batch A7: configGC heap-size bound and data do_app lemmas. *)
val _ = cap "configGC_size_of_heap_LE_typed" "configGC_size_of_heap_LE";
val _ = cap "do_app_FromList_stack_max_typed" "do_app_FromList_stack_max";
val _ = cap "do_app_FromList_eq_typed" "do_app_FromList_eq";
val _ = cap "do_app_AllocThunk_typed" "do_app_AllocThunk";

(* Batch A8: assign_FinaliseCons. *)
val _ = cap "assign_FinaliseCons_typed" "assign_FinaliseCons";

(* Batch A9: assign_MutCons. *)
val _ = cap "assign_MutCons_typed" "assign_MutCons";

(* Batch A10: assign_UpdateCons, assign_WordFromWord, assign_ConfigGC. *)
val _ = cap "assign_UpdateCons_typed" "assign_UpdateCons";
val _ = cap "assign_WordFromWord_typed" "assign_WordFromWord";
val _ = cap "assign_ConfigGC_typed" "assign_ConfigGC";
