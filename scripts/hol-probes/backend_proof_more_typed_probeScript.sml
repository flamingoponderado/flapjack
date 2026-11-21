(* Typed captures for the backendProofScript.sml declarations ported after the
   first backendProof batches (counterparts under
   Flapjack/Compiler/Backend/BackendProof/), plus their backendScript,
   data_to_word, bvl_to_bvi and mlstring prerequisite definitions. Needs
   CAKEML=/var/tmp/flapjack-cakeml-oracle, where backendProofTheory is built
   (pin 857f0d98d, HOL a390cbab); see scripts/hol-probes/README.md. Exported theorems and definitions are fetched
   from the theory DB; `[local]` theorems are parsed from the pinned source
   text with SML antiquotation splices expanded. *)
load "preamble";
load "backendProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open backendProofTheory;
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
  case DB.lookup {Thy="backendProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/backendProofScript.sml";

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


val _ = print "backend_proof_more_probe_begin=1\n";
val _ = print ("byte_aligned_mult_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "byte_aligned_mult"))) ^ "\n");
val _ = emit_exported "byte_aligned_mult_typed" "byte_aligned_mult";
val _ = print ("byte_aligned_MOD_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "byte_aligned_MOD"))) ^ "\n");
val _ = emit_exported "byte_aligned_MOD_typed" "byte_aligned_MOD";
val _ = print ("backend_config_ok_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_config_ok_def"))) ^ "\n");
val _ = emit_exported "backend_config_ok_def_typed" "backend_config_ok_def";
val _ = print ("backend_config_ok_with_bvl_conf_updated_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_config_ok_with_bvl_conf_updated"))) ^ "\n");
val _ = emit_exported "backend_config_ok_with_bvl_conf_updated_typed" "backend_config_ok_with_bvl_conf_updated";
val _ = print ("backend_config_ok_with_word_to_word_conf_updated_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_config_ok_with_word_to_word_conf_updated"))) ^ "\n");
val _ = emit_exported "backend_config_ok_with_word_to_word_conf_updated_typed" "backend_config_ok_with_word_to_word_conf_updated";
val _ = print ("backend_config_ok_call_empty_ffi_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_config_ok_call_empty_ffi"))) ^ "\n");
val _ = emit_exported "backend_config_ok_call_empty_ffi_typed" "backend_config_ok_call_empty_ffi";
val _ = print ("mc_init_ok_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "mc_init_ok_def"))) ^ "\n");
val _ = emit_exported "mc_init_ok_def_typed" "mc_init_ok_def";
val _ = print ("mc_init_ok_with_bvl_conf_updated_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "mc_init_ok_with_bvl_conf_updated"))) ^ "\n");
val _ = emit_exported "mc_init_ok_with_bvl_conf_updated_typed" "mc_init_ok_with_bvl_conf_updated";
val _ = print ("mc_init_ok_with_word_to_word_conf_updated_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "mc_init_ok_with_word_to_word_conf_updated"))) ^ "\n");
val _ = emit_exported "mc_init_ok_with_word_to_word_conf_updated_typed" "mc_init_ok_with_word_to_word_conf_updated";
val _ = print ("mc_init_ok_with_clos_conf_updated_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "mc_init_ok_with_clos_conf_updated"))) ^ "\n");
val _ = emit_exported "mc_init_ok_with_clos_conf_updated_typed" "mc_init_ok_with_clos_conf_updated";
val _ = print ("set_oracle_simp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "set_oracle_simp"))) ^ "\n");
val _ = emit_exported "set_oracle_simp_typed" "set_oracle_simp";
val _ = print ("mc_init_ok_call_empty_ffi_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "mc_init_ok_call_empty_ffi"))) ^ "\n");
val _ = emit_exported "mc_init_ok_call_empty_ffi_typed" "mc_init_ok_call_empty_ffi";
val _ = print ("heap_regs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "heap_regs_def"))) ^ "\n");
val _ = emit_exported "heap_regs_def_typed" "heap_regs_def";
val _ = print ("no_mti_IMP_obeys_max_app_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "no_mti_IMP_obeys_max_app"))) ^ "\n");
val _ = emit_exported "no_mti_IMP_obeys_max_app_typed" "no_mti_IMP_obeys_max_app";
val _ = print ("EVERY_no_mti_IMP_obeys_max_app_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "EVERY_no_mti_IMP_obeys_max_app"))) ^ "\n");
val _ = emit_exported "EVERY_no_mti_IMP_obeys_max_app_typed" "EVERY_no_mti_IMP_obeys_max_app";
val _ = print ("compile_common_syntax_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_common_syntax"))) ^ "\n");
val _ = emit_exported "compile_common_syntax_typed" "compile_common_syntax";
val _ = print ("word_list_exists_imp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "word_list_exists_imp"))) ^ "\n");
val _ = emit_exported "word_list_exists_imp_typed" "word_list_exists_imp";
val _ = print ("cake_configs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_configs_def"))) ^ "\n");
val _ = emit_exported "cake_configs_def_typed" "cake_configs_def";
val _ = print ("cake_orac_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_def"))) ^ "\n");
val _ = emit_exported "cake_orac_def_typed" "cake_orac_def";
val _ = print ("config_tuple2_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "config_tuple2_def"))) ^ "\n");
val _ = emit_exported "config_tuple2_def_typed" "config_tuple2_def";
val _ = print ("config_tuple1_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "config_tuple1_def"))) ^ "\n");
val _ = emit_exported "config_tuple1_def_typed" "config_tuple1_def";
val _ = print ("cake_configs_eq_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_configs_eq"))) ^ "\n");
val _ = emit_exported "cake_configs_eq_typed" "cake_configs_eq";
val _ = print ("PAIR_MAP_EQ_EQ_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "PAIR_MAP_EQ_EQ"))) ^ "\n");
val _ = emit_exported "PAIR_MAP_EQ_EQ_typed" "PAIR_MAP_EQ_EQ";
val _ = print ("known_compile_IS_SOME_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_compile_IS_SOME"))) ^ "\n");
val _ = emit_exported "known_compile_IS_SOME_typed" "known_compile_IS_SOME";
val _ = print ("attach_bitmaps_SOME_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "attach_bitmaps_SOME"))) ^ "\n");
val _ = emit_exported "attach_bitmaps_SOME_typed" "attach_bitmaps_SOME";
val _ = print ("known_compile_static_conf_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_compile_static_conf"))) ^ "\n");
val _ = emit_exported "known_compile_static_conf_typed" "known_compile_static_conf";
val _ = print ("known_option_upd_val_spt_eq_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_option_upd_val_spt_eq"))) ^ "\n");
val _ = emit_exported "known_option_upd_val_spt_eq_typed" "known_option_upd_val_spt_eq";
val _ = print ("source_compile_pattern_cfg_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "source_compile_pattern_cfg"))) ^ "\n");
val _ = emit_exported "source_compile_pattern_cfg_typed" "source_compile_pattern_cfg";
val _ = print ("cake_orac_config_eqs_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_config_eqs"))) ^ "\n");
val _ = emit_exported "cake_orac_config_eqs_typed" "cake_orac_config_eqs";
val _ = print ("decide_inline_reset_spt_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "decide_inline_reset_spt"))) ^ "\n");
val _ = emit_exported "decide_inline_reset_spt_typed" "decide_inline_reset_spt";
val _ = print ("known_reset_spt_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_reset_spt"))) ^ "\n");
val _ = emit_exported "known_reset_spt_typed" "known_reset_spt";
val _ = print ("known_reset_to_static_conf_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_reset_to_static_conf"))) ^ "\n");
val _ = emit_exported "known_reset_to_static_conf_typed" "known_reset_to_static_conf";
val _ = print ("known_co_eq_state_co_inc_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_co_eq_state_co_inc"))) ^ "\n");
val _ = emit_exported "known_co_eq_state_co_inc_typed" "known_co_eq_state_co_inc";
val _ = capture "keep_progs_T_typed" "keep_progs_T";
val _ = print ("cake_orac_eqs_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_eqs"))) ^ "\n");
val _ = emit_exported "cake_orac_eqs_typed" "cake_orac_eqs";
val _ = print ("cake_orac_0_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_0"))) ^ "\n");
val _ = emit_exported "cake_orac_0_typed" "cake_orac_0";
val _ = print ("cake_orac_SUC_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_SUC"))) ^ "\n");
val _ = emit_exported "cake_orac_SUC_typed" "cake_orac_SUC";
val _ = capture "compile_inc_progs_src_env_tup_typed" "compile_inc_progs_src_env_tup";
val _ = print ("cake_orac_SUC2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_SUC2"))) ^ "\n");
val _ = emit_exported "cake_orac_SUC2_typed" "cake_orac_SUC2";
val _ = print ("from_clos_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_clos_conf_EX"))) ^ "\n");
val _ = emit_exported "from_clos_conf_EX_typed" "from_clos_conf_EX";
val _ = print ("from_bvl_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_bvl_conf_EX"))) ^ "\n");
val _ = emit_exported "from_bvl_conf_EX_typed" "from_bvl_conf_EX";
val _ = print ("from_bvi_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_bvi_conf_EX"))) ^ "\n");
val _ = emit_exported "from_bvi_conf_EX_typed" "from_bvi_conf_EX";
val _ = print ("from_data_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_data_conf_EX"))) ^ "\n");
val _ = emit_exported "from_data_conf_EX_typed" "from_data_conf_EX";
val _ = print ("from_word_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_word_conf_EX"))) ^ "\n");
val _ = emit_exported "from_word_conf_EX_typed" "from_word_conf_EX";
val _ = print ("from_stack_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_stack_conf_EX"))) ^ "\n");
val _ = emit_exported "from_stack_conf_EX_typed" "from_stack_conf_EX";
val _ = print ("from_lab_conf_EX_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "from_lab_conf_EX"))) ^ "\n");
val _ = emit_exported "from_lab_conf_EX_typed" "from_lab_conf_EX";
val _ = print ("oracle_monotonic_globals_flat_to_clos_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_globals_flat_to_clos"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_globals_flat_to_clos_typed" "oracle_monotonic_globals_flat_to_clos";
val _ = print ("cake_orac_eq_I_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_eq_I"))) ^ "\n");
val _ = emit_exported "cake_orac_eq_I_typed" "cake_orac_eq_I";
val _ = print ("cake_orac_invariant_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_invariant"))) ^ "\n");
val _ = emit_exported "cake_orac_invariant_typed" "cake_orac_invariant";
val _ = print ("bvl_to_bvi_compile_semantics2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "bvl_to_bvi_compile_semantics2"))) ^ "\n");
val _ = emit_exported "bvl_to_bvi_compile_semantics2_typed" "bvl_to_bvi_compile_semantics2";
val _ = print ("compile_no_stubs_wrap_pure_co_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_no_stubs_wrap_pure_co"))) ^ "\n");
val _ = emit_exported "compile_no_stubs_wrap_pure_co_typed" "compile_no_stubs_wrap_pure_co";
val _ = print ("full_make_init_semantics2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "full_make_init_semantics2"))) ^ "\n");
val _ = emit_exported "full_make_init_semantics2_typed" "full_make_init_semantics2";
val _ = print ("data_num_stubs_LE_tailrec_compile_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "data_num_stubs_LE_tailrec_compile"))) ^ "\n");
val _ = emit_exported "data_num_stubs_LE_tailrec_compile_typed" "data_num_stubs_LE_tailrec_compile";
val _ = print ("data_num_stubs_LE_bvl_bvi_compile_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "data_num_stubs_LE_bvl_bvi_compile"))) ^ "\n");
val _ = emit_exported "data_num_stubs_LE_bvl_bvi_compile_typed" "data_num_stubs_LE_bvl_bvi_compile";
val _ = print ("configs_nn2_MULT_namespaces_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn2_MULT_namespaces"))) ^ "\n");
val _ = emit_exported "configs_nn2_MULT_namespaces_typed" "configs_nn2_MULT_namespaces";
val _ = print ("configs_nn2_MOD_namespaces_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn2_MOD_namespaces"))) ^ "\n");
val _ = emit_exported "configs_nn2_MOD_namespaces_typed" "configs_nn2_MOD_namespaces";
val _ = print ("configs_nn3_MULT_namespaces_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn3_MULT_namespaces"))) ^ "\n");
val _ = emit_exported "configs_nn3_MULT_namespaces_typed" "configs_nn3_MULT_namespaces";
val _ = print ("configs_nn3_MOD_namespaces_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn3_MOD_namespaces"))) ^ "\n");
val _ = emit_exported "configs_nn3_MOD_namespaces_typed" "configs_nn3_MOD_namespaces";
val _ = print ("configs_nn2_MOD_namespaces_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn2_MOD_namespaces_ok"))) ^ "\n");
val _ = emit_exported "configs_nn2_MOD_namespaces_ok_typed" "configs_nn2_MOD_namespaces_ok";
val _ = print ("configs_nn3_MOD_namespaces_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "configs_nn3_MOD_namespaces_ok"))) ^ "\n");
val _ = emit_exported "configs_nn3_MOD_namespaces_ok_typed" "configs_nn3_MOD_namespaces_ok";
val _ = print ("bvl_to_bvi_compile_inc_all_num_stubs_LE_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "bvl_to_bvi_compile_inc_all_num_stubs_LE"))) ^ "\n");
val _ = emit_exported "bvl_to_bvi_compile_inc_all_num_stubs_LE_typed" "bvl_to_bvi_compile_inc_all_num_stubs_LE";
val _ = print ("bvl_num_stubs_LE_bvi_prog_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "bvl_num_stubs_LE_bvi_prog"))) ^ "\n");
val _ = emit_exported "bvl_num_stubs_LE_bvi_prog_typed" "bvl_num_stubs_LE_bvi_prog";
val _ = print ("stack_to_lab_orac_eq_std_sym_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "stack_to_lab_orac_eq_std_sym"))) ^ "\n");
val _ = emit_exported "stack_to_lab_orac_eq_std_sym_typed" "stack_to_lab_orac_eq_std_sym";
val _ = print ("state_co_fun_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "state_co_fun_def"))) ^ "\n");
val _ = emit_exported "state_co_fun_def_typed" "state_co_fun_def";
val _ = print ("state_co_eq_comp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "state_co_eq_comp"))) ^ "\n");
val _ = emit_exported "state_co_eq_comp_typed" "state_co_eq_comp";
val _ = print ("is_state_oracle_cake_orac_comp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_state_oracle_cake_orac_comp"))) ^ "\n");
val _ = emit_exported "is_state_oracle_cake_orac_comp_typed" "is_state_oracle_cake_orac_comp";
val _ = print ("is_state_oracle_cake_orac_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_state_oracle_cake_orac"))) ^ "\n");
val _ = emit_exported "is_state_oracle_cake_orac_typed" "is_state_oracle_cake_orac";
val _ = print ("cake_orac_clos_is_state_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_clos_is_state"))) ^ "\n");
val _ = emit_exported "cake_orac_clos_is_state_typed" "cake_orac_clos_is_state";
val _ = print ("cake_orac_source_is_state_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_source_is_state"))) ^ "\n");
val _ = emit_exported "cake_orac_source_is_state_typed" "cake_orac_source_is_state";
val _ = print ("is_state_oracle_cake_orac_to_comp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_state_oracle_cake_orac_to_comp"))) ^ "\n");
val _ = emit_exported "is_state_oracle_cake_orac_to_comp_typed" "is_state_oracle_cake_orac_to_comp";
val _ = capture "BAG_ALL_DISTINCT_BAG_IMAGE_SUC_typed" "BAG_ALL_DISTINCT_BAG_IMAGE_SUC";
val _ = capture "BAG_ALL_DISTINCT_BAG_IMAGE_SUC_prime_typed" "BAG_ALL_DISTINCT_BAG_IMAGE_SUC'";
val _ = print ("cake_orac_clos_syntax_oracle_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_clos_syntax_oracle_ok"))) ^ "\n");
val _ = emit_exported "cake_orac_clos_syntax_oracle_ok_typed" "cake_orac_clos_syntax_oracle_ok";
val _ = print ("cake_orac_bvl_ALL_DISTINCT_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_bvl_ALL_DISTINCT"))) ^ "\n");
val _ = emit_exported "cake_orac_bvl_ALL_DISTINCT_typed" "cake_orac_bvl_ALL_DISTINCT";
val _ = print ("compile_lab_LENGTH_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_lab_LENGTH"))) ^ "\n");
val _ = emit_exported "compile_lab_LENGTH_typed" "compile_lab_LENGTH";
val _ = print ("bvl_to_bvi_compile_inc_all_DISTINCT_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "bvl_to_bvi_compile_inc_all_DISTINCT"))) ^ "\n");
val _ = emit_exported "bvl_to_bvi_compile_inc_all_DISTINCT_typed" "bvl_to_bvi_compile_inc_all_DISTINCT";
val _ = print ("cake_orac_stack_ALL_DISTINCT_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_stack_ALL_DISTINCT"))) ^ "\n");
val _ = emit_exported "cake_orac_stack_ALL_DISTINCT_typed" "cake_orac_stack_ALL_DISTINCT";
val _ = print ("MAP_full_compile_single_to_compile_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "MAP_full_compile_single_to_compile"))) ^ "\n");
val _ = emit_exported "MAP_full_compile_single_to_compile_typed" "MAP_full_compile_single_to_compile";
val _ = print ("compile_to_word_conventions2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_to_word_conventions2"))) ^ "\n");
val _ = emit_exported "compile_to_word_conventions2_typed" "compile_to_word_conventions2";
val _ = print ("sec_labels_ok_FST_code_labels_Section_num_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "sec_labels_ok_FST_code_labels_Section_num"))) ^ "\n");
val _ = emit_exported "sec_labels_ok_FST_code_labels_Section_num_typed" "sec_labels_ok_FST_code_labels_Section_num";
val _ = print ("stack_labels_ok_FST_code_labels_Section_num_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "stack_labels_ok_FST_code_labels_Section_num"))) ^ "\n");
val _ = emit_exported "stack_labels_ok_FST_code_labels_Section_num_typed" "stack_labels_ok_FST_code_labels_Section_num";
val _ = print ("lab_labels_ok_oracle_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "lab_labels_ok_oracle"))) ^ "\n");
val _ = emit_exported "lab_labels_ok_oracle_typed" "lab_labels_ok_oracle";
val _ = print ("compile_lab_domain_labels_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_lab_domain_labels"))) ^ "\n");
val _ = emit_exported "compile_lab_domain_labels_typed" "compile_lab_domain_labels";
val _ = print ("accum_lab_conf_labels_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "accum_lab_conf_labels"))) ^ "\n");
val _ = emit_exported "accum_lab_conf_labels_typed" "accum_lab_conf_labels";
val _ = print ("MAP_Section_num_stack_to_lab_SUBSET_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "MAP_Section_num_stack_to_lab_SUBSET"))) ^ "\n");
val _ = emit_exported "MAP_Section_num_stack_to_lab_SUBSET_typed" "MAP_Section_num_stack_to_lab_SUBSET";
val _ = print ("to_data_labels_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_data_labels_ok"))) ^ "\n");
val _ = emit_exported "to_data_labels_ok_typed" "to_data_labels_ok";
val _ = print ("data_to_word_stubs_above_store_consts_stub_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "data_to_word_stubs_above_store_consts_stub"))) ^ "\n");
val _ = emit_exported "data_to_word_stubs_above_store_consts_stub_typed" "data_to_word_stubs_above_store_consts_stub";
val _ = print ("to_word_labels_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_word_labels_ok"))) ^ "\n");
val _ = emit_exported "to_word_labels_ok_typed" "to_word_labels_ok";
val _ = print ("to_bvi_perf_calls_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_bvi_perf_calls"))) ^ "\n");
val _ = emit_exported "to_bvi_perf_calls_typed" "to_bvi_perf_calls";
val _ = print ("to_data_perf_calls_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_data_perf_calls"))) ^ "\n");
val _ = emit_exported "to_data_perf_calls_typed" "to_data_perf_calls";
val _ = print ("to_word_perf_calls_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_word_perf_calls"))) ^ "\n");
val _ = emit_exported "to_word_perf_calls_typed" "to_word_perf_calls";
val _ = print ("to_lab_labels_ok_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_lab_labels_ok"))) ^ "\n");
val _ = emit_exported "to_lab_labels_ok_typed" "to_lab_labels_ok";
val _ = print ("oracle_monotonic_slice_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_slice"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_slice_typed" "oracle_monotonic_slice";
val _ = print ("oracle_monotonic_rel_mono_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_rel_mono"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_rel_mono_typed" "oracle_monotonic_rel_mono";
val _ = print ("oracle_monotonic_state_with_inv_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_state_with_inv"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_state_with_inv_typed" "oracle_monotonic_state_with_inv";
val _ = print ("oracle_monotonic_bounded_state_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_bounded_state"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_bounded_state_typed" "oracle_monotonic_bounded_state";
val _ = print ("compile_prog_avoids_nss_2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_prog_avoids_nss_2"))) ^ "\n");
val _ = emit_exported "compile_prog_avoids_nss_2_typed" "compile_prog_avoids_nss_2";
val _ = print ("tailrec_compile_prog_MEM_not_nss_2_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "tailrec_compile_prog_MEM_not_nss_2"))) ^ "\n");
val _ = emit_exported "tailrec_compile_prog_MEM_not_nss_2_typed" "tailrec_compile_prog_MEM_not_nss_2";
val _ = print ("tmc_compile_prog_MEM_not_nss_3_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "tmc_compile_prog_MEM_not_nss_3"))) ^ "\n");
val _ = emit_exported "tmc_compile_prog_MEM_not_nss_3_typed" "tmc_compile_prog_MEM_not_nss_3";
val _ = print ("is_state_oracle_tailrec_cake_orac_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_state_oracle_tailrec_cake_orac"))) ^ "\n");
val _ = emit_exported "is_state_oracle_tailrec_cake_orac_typed" "is_state_oracle_tailrec_cake_orac";
val _ = print ("is_state_oracle_tmc_cake_orac_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_state_oracle_tmc_cake_orac"))) ^ "\n");
val _ = emit_exported "is_state_oracle_tmc_cake_orac_typed" "is_state_oracle_tmc_cake_orac";
val _ = print ("inline_compile_inc_names_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "inline_compile_inc_names"))) ^ "\n");
val _ = emit_exported "inline_compile_inc_names_typed" "inline_compile_inc_names";
val _ = print ("bvi_inline_state_co_MAP_FST_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "bvi_inline_state_co_MAP_FST"))) ^ "\n");
val _ = emit_exported "bvi_inline_state_co_MAP_FST_typed" "bvi_inline_state_co_MAP_FST";
val _ = print ("oracle_monotonic_bvi_inline_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_bvi_inline"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_bvi_inline_typed" "oracle_monotonic_bvi_inline";
val _ = print ("oracle_monotonic_bvi_inline_inter_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_bvi_inline_inter"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_bvi_inline_inter_typed" "oracle_monotonic_bvi_inline_inter";
val _ = print ("oracle_monotonic_subset_inject_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_subset_inject"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_subset_inject_typed" "oracle_monotonic_subset_inject";
val _ = print ("oracle_monotonic_handle_init_component_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_handle_init_component"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_handle_init_component_typed" "oracle_monotonic_handle_init_component";
val _ = print ("oracle_monotonic_cake_orac_to_I_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_monotonic_cake_orac_to_I"))) ^ "\n");
val _ = emit_exported "oracle_monotonic_cake_orac_to_I_typed" "oracle_monotonic_cake_orac_to_I";
val _ = print ("cake_orac_monotonic_bounded_state_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_monotonic_bounded_state"))) ^ "\n");
val _ = emit_exported "cake_orac_monotonic_bounded_state_typed" "cake_orac_monotonic_bounded_state";
val _ = print ("monotonic_DISJOINT_labels_lab_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "monotonic_DISJOINT_labels_lab"))) ^ "\n");
val _ = emit_exported "monotonic_DISJOINT_labels_lab_typed" "monotonic_DISJOINT_labels_lab";
val _ = print ("monotonic_labels_stack_to_lab_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "monotonic_labels_stack_to_lab"))) ^ "\n");
val _ = emit_exported "monotonic_labels_stack_to_lab_typed" "monotonic_labels_stack_to_lab";
val _ = print ("monotonic_labels_bvi_down_to_stack_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "monotonic_labels_bvi_down_to_stack"))) ^ "\n");
val _ = emit_exported "monotonic_labels_bvi_down_to_stack_typed" "monotonic_labels_bvi_down_to_stack";
val _ = print ("monotonic_labels_bvl_to_bvi_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "monotonic_labels_bvl_to_bvi"))) ^ "\n");
val _ = emit_exported "monotonic_labels_bvl_to_bvi_typed" "monotonic_labels_bvl_to_bvi";
val _ = print ("syntax_oracle_ok_start_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "syntax_oracle_ok_start"))) ^ "\n");
val _ = emit_exported "syntax_oracle_ok_start_typed" "syntax_oracle_ok_start";
val _ = print ("monotonic_labels_bvl_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "monotonic_labels_bvl"))) ^ "\n");
val _ = emit_exported "monotonic_labels_bvl_typed" "monotonic_labels_bvl";
val _ = print ("good_code_lab_oracle_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "good_code_lab_oracle"))) ^ "\n");
val _ = emit_exported "good_code_lab_oracle_typed" "good_code_lab_oracle";
val _ = print ("oracle_stack_good_code_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "oracle_stack_good_code"))) ^ "\n");
val _ = emit_exported "oracle_stack_good_code_typed" "oracle_stack_good_code";
val _ = print ("to_lab_good_code_lemma_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_lab_good_code_lemma"))) ^ "\n");
val _ = emit_exported "to_lab_good_code_lemma_typed" "to_lab_good_code_lemma";
val _ = print ("data_to_word_orac_eq_std_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "data_to_word_orac_eq_std"))) ^ "\n");
val _ = emit_exported "data_to_word_orac_eq_std_typed" "data_to_word_orac_eq_std";
val _ = print ("data_to_word_orac_eq_sym_std_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "data_to_word_orac_eq_sym_std"))) ^ "\n");
val _ = emit_exported "data_to_word_orac_eq_sym_std_typed" "data_to_word_orac_eq_sym_std";
val _ = print ("compute_stack_frame_sizes_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compute_stack_frame_sizes_def"))) ^ "\n");
val _ = emit_exported "compute_stack_frame_sizes_def_typed" "compute_stack_frame_sizes_def";
val _ = print ("compute_stack_frame_sizes_thm_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compute_stack_frame_sizes_thm"))) ^ "\n");
val _ = emit_exported "compute_stack_frame_sizes_thm_typed" "compute_stack_frame_sizes_thm";
val _ = print ("is_64_bits_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_64_bits_def"))) ^ "\n");
val _ = emit_exported "is_64_bits_def_typed" "is_64_bits_def";
val _ = print ("is_safe_for_space_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "is_safe_for_space_def"))) ^ "\n");
val _ = emit_exported "is_safe_for_space_def_typed" "is_safe_for_space_def";
val _ = print ("compile_word_conf_eq_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_word_conf_eq"))) ^ "\n");
val _ = emit_exported "compile_word_conf_eq_typed" "compile_word_conf_eq";
val _ = print ("to_word_lab_conf_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "to_word_lab_conf"))) ^ "\n");
val _ = emit_exported "to_word_lab_conf_typed" "to_word_lab_conf";
val _ = print ("PERM_toAList_fromAList_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "PERM_toAList_fromAList"))) ^ "\n");
val _ = emit_exported "PERM_toAList_fromAList_typed" "PERM_toAList_fromAList";
val _ = print ("compile_word_to_stack_sfs_aux_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_word_to_stack_sfs_aux"))) ^ "\n");
val _ = emit_exported "compile_word_to_stack_sfs_aux_typed" "compile_word_to_stack_sfs_aux";
val _ = print ("IMP_is_safe_for_space_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "IMP_is_safe_for_space"))) ^ "\n");
val _ = emit_exported "IMP_is_safe_for_space_typed" "IMP_is_safe_for_space";
val _ = print ("read_limits_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "read_limits_def"))) ^ "\n");
val _ = emit_exported "read_limits_def_typed" "read_limits_def";
val _ = capture "FST_SND_EQ_typed" "FST_SND_EQ";
val _ = capture "PERMUTE_IMP_LINV_typed" "PERMUTE_IMP_LINV";
val _ = print ("state_co_inc_compile_has_flat_comp_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "state_co_inc_compile_has_flat_comp"))) ^ "\n");
val _ = emit_exported "state_co_inc_compile_has_flat_comp_typed" "state_co_inc_compile_has_flat_comp";
val _ = print ("add_eval_state_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "add_eval_state_def"))) ^ "\n");
val _ = emit_exported "add_eval_state_def_typed" "add_eval_state_def";
val _ = print ("add_eval_state_ffi_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "add_eval_state_ffi"))) ^ "\n");
val _ = emit_exported "add_eval_state_ffi_typed" "add_eval_state_ffi";
val _ = print ("opt_eval_config_wf_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "opt_eval_config_wf_def"))) ^ "\n");
val _ = emit_exported "opt_eval_config_wf_def_typed" "opt_eval_config_wf_def";
val _ = print ("backend_from_data_tuple_cc_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_from_data_tuple_cc_def"))) ^ "\n");
val _ = emit_exported "backend_from_data_tuple_cc_def_typed" "backend_from_data_tuple_cc_def";
val _ = print ("backend_from_flat_tuple_cc_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_from_flat_tuple_cc_def"))) ^ "\n");
val _ = emit_exported "backend_from_flat_tuple_cc_def_typed" "backend_from_flat_tuple_cc_def";
val _ = print ("known_cc_eq_state_cc_inc_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_cc_eq_state_cc_inc"))) ^ "\n");
val _ = emit_exported "known_cc_eq_state_cc_inc_typed" "known_cc_eq_state_cc_inc";
val _ = print ("known_compile_inc_retreive_spt_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "known_compile_inc_retreive_spt"))) ^ "\n");
val _ = emit_exported "known_compile_inc_retreive_spt_typed" "known_compile_inc_retreive_spt";
val _ = print ("backend_from_flat_tuple_cc_eq_compile_inc_progs_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "backend_from_flat_tuple_cc_eq_compile_inc_progs"))) ^ "\n");
val _ = emit_exported "backend_from_flat_tuple_cc_eq_compile_inc_progs_typed" "backend_from_flat_tuple_cc_eq_compile_inc_progs";
val _ = capture "compile_inc_progs_src_env_typed" "compile_inc_progs_src_env";
val _ = print ("cake_orac_cfg_f_eq_I_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "cake_orac_cfg_f_eq_I"))) ^ "\n");
val _ = emit_exported "cake_orac_cfg_f_eq_I_typed" "cake_orac_cfg_f_eq_I";
val _ = print ("config_wf_abs_conc_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "config_wf_abs_conc"))) ^ "\n");
val _ = emit_exported "config_wf_abs_conc_typed" "config_wf_abs_conc";
val _ = capture "source_to_source_semantics_prog_equiv_typed" "source_to_source_semantics_prog_equiv";
val _ = capture "source_to_source_semantics_prog_intro_typed" "source_to_source_semantics_prog_intro";
val _ = capture "eval_oracle_semantics_prog_intro_typed" "eval_oracle_semantics_prog_intro";
val _ = capture "source_to_source_semantics_prog_oracle_intro_typed" "source_to_source_semantics_prog_oracle_intro";
val _ = print ("source_eval_to_flat_semantics_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "source_eval_to_flat_semantics"))) ^ "\n");
val _ = emit_exported "source_eval_to_flat_semantics_typed" "source_eval_to_flat_semantics";
val _ = print ("flat_semantics_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "flat_semantics"))) ^ "\n");
val _ = emit_exported "flat_semantics_typed" "flat_semantics";
val _ = print ("pad_code_no_share_mem_inst_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "pad_code_no_share_mem_inst"))) ^ "\n");
val _ = emit_exported "pad_code_no_share_mem_inst_typed" "pad_code_no_share_mem_inst";
val _ = print ("enc_sec_list_no_share_mem_inst_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "enc_sec_list_no_share_mem_inst"))) ^ "\n");
val _ = emit_exported "enc_sec_list_no_share_mem_inst_typed" "enc_sec_list_no_share_mem_inst";
val _ = print ("enc_secs_again_no_share_mem_inst_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "enc_secs_again_no_share_mem_inst"))) ^ "\n");
val _ = emit_exported "enc_secs_again_no_share_mem_inst_typed" "enc_secs_again_no_share_mem_inst";
val _ = print ("upd_lab_len_no_share_mem_inst_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "upd_lab_len_no_share_mem_inst"))) ^ "\n");
val _ = emit_exported "upd_lab_len_no_share_mem_inst_typed" "upd_lab_len_no_share_mem_inst";
val _ = print ("remove_labels_loop_no_share_mem_inst_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "remove_labels_loop_no_share_mem_inst"))) ^ "\n");
val _ = emit_exported "remove_labels_loop_no_share_mem_inst_typed" "remove_labels_loop_no_share_mem_inst";
val _ = print ("compile_lab_IMP_mmio_pcs_min_index_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_lab_IMP_mmio_pcs_min_index"))) ^ "\n");
val _ = emit_exported "compile_lab_IMP_mmio_pcs_min_index_typed" "compile_lab_IMP_mmio_pcs_min_index";
val _ = print ("compile_lab_no_share_mem_IMP_mmio_pcs_min_index_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_lab_no_share_mem_IMP_mmio_pcs_min_index"))) ^ "\n");
val _ = emit_exported "compile_lab_no_share_mem_IMP_mmio_pcs_min_index_typed" "compile_lab_no_share_mem_IMP_mmio_pcs_min_index";
val _ = print ("compile_correct_prime_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_correct'"))) ^ "\n");
val _ = emit_exported "compile_correct_prime_typed" "compile_correct'";
val _ = print ("compile_correct_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_correct"))) ^ "\n");
val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = print ("semantics_prog_sing_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "semantics_prog_sing"))) ^ "\n");
val _ = emit_exported "semantics_prog_sing_typed" "semantics_prog_sing";
val _ = print ("compile_correct_is_safe_for_space_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_correct_is_safe_for_space"))) ^ "\n");
val _ = emit_exported "compile_correct_is_safe_for_space_typed" "compile_correct_is_safe_for_space";
val _ = print ("the_EvalDecs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "the_EvalDecs_def"))) ^ "\n");
val _ = emit_exported "the_EvalDecs_def_typed" "the_EvalDecs_def";
val _ = print ("compile_correct_eval_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backendProof" "compile_correct_eval"))) ^ "\n");
val _ = emit_exported "compile_correct_eval_typed" "compile_correct_eval";
val _ = print ("set_oracle_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "set_oracle_def"))) ^ "\n");
val _ = emit "set_oracle_def_typed" (DB.fetch "backend" "set_oracle_def");
val _ = print ("empty_ffi_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "mlstring" "empty_ffi_def"))) ^ "\n");
val _ = emit "empty_ffi_def_typed" (DB.fetch "mlstring" "empty_ffi_def");
val _ = print ("data_to_word_compile_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "data_to_word" "compile_def"))) ^ "\n");
val _ = emit "data_to_word_compile_def_typed" (DB.fetch "data_to_word" "compile_def");
val _ = print ("data_to_word_compile_0_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "data_to_word" "compile_0_def"))) ^ "\n");
val _ = emit "data_to_word_compile_0_def_typed" (DB.fetch "data_to_word" "compile_0_def");
val _ = print ("bvl_to_bvi_compile_inc_all_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "bvl_to_bvi" "bvl_to_bvi_compile_inc_all_def"))) ^ "\n");
val _ = emit "bvl_to_bvi_compile_inc_all_def_typed" (DB.fetch "bvl_to_bvi" "bvl_to_bvi_compile_inc_all_def");
val _ = print ("backend_compile_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "compile_def"))) ^ "\n");
val _ = emit "backend_compile_def_typed" (DB.fetch "backend" "compile_def");
val _ = print ("from_data_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_data_def"))) ^ "\n");
val _ = emit "from_data_def_typed" (DB.fetch "backend" "from_data_def");
val _ = print ("from_bvi_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_bvi_def"))) ^ "\n");
val _ = emit "from_bvi_def_typed" (DB.fetch "backend" "from_bvi_def");
val _ = print ("from_bvl_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_bvl_def"))) ^ "\n");
val _ = emit "from_bvl_def_typed" (DB.fetch "backend" "from_bvl_def");
val _ = print ("from_clos_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_clos_def"))) ^ "\n");
val _ = emit "from_clos_def_typed" (DB.fetch "backend" "from_clos_def");
val _ = print ("from_flat_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_flat_def"))) ^ "\n");
val _ = emit "from_flat_def_typed" (DB.fetch "backend" "from_flat_def");
val _ = print ("from_source_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "from_source_def"))) ^ "\n");
val _ = emit "from_source_def_typed" (DB.fetch "backend" "from_source_def");
val _ = print ("compile_eq_from_source_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "compile_eq_from_source"))) ^ "\n");
val _ = emit "compile_eq_from_source_typed" (DB.fetch "backend" "compile_eq_from_source");
val _ = dt_label "backend_progs_constructors" "backend_progs";
val _ = print ("empty_progs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "empty_progs_def"))) ^ "\n");
val _ = emit "empty_progs_def_typed" (DB.fetch "backend" "empty_progs_def");
val _ = print ("keep_progs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "keep_progs_def"))) ^ "\n");
val _ = emit "keep_progs_def_typed" (DB.fetch "backend" "keep_progs_def");
val _ = print ("compile_inc_progs_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "compile_inc_progs_def"))) ^ "\n");
val _ = emit "compile_inc_progs_def_typed" (DB.fetch "backend" "compile_inc_progs_def");
val _ = print ("backend_to_word_0_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_word_0_def"))) ^ "\n");
val _ = emit "backend_to_word_0_def_typed" (DB.fetch "backend" "to_word_0_def");
val _ = print ("backend_to_word_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_word_def"))) ^ "\n");
val _ = emit "backend_to_word_def_typed" (DB.fetch "backend" "to_word_def");
val _ = print ("backend_to_word_thm_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_word_thm"))) ^ "\n");
val _ = emit "backend_to_word_thm_typed" (DB.fetch "backend" "to_word_thm");
val _ = print ("backend_to_stack_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_stack_def"))) ^ "\n");
val _ = emit "backend_to_stack_def_typed" (DB.fetch "backend" "to_stack_def");
val _ = print ("backend_to_lab_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_lab_def"))) ^ "\n");
val _ = emit "backend_to_lab_def_typed" (DB.fetch "backend" "to_lab_def");
val _ = print ("backend_to_target_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "to_target_def"))) ^ "\n");
val _ = emit "backend_to_target_def_typed" (DB.fetch "backend" "to_target_def");
val _ = print ("backend_compile_eq_to_target_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "compile_eq_to_target"))) ^ "\n");
val _ = emit "backend_compile_eq_to_target_typed" (DB.fetch "backend" "compile_eq_to_target");
val _ = print ("compile_inc_progs_for_eval_def_hypotheses=" ^
  Int.toString (length (hyp (DB.fetch "backend" "compile_inc_progs_for_eval_def"))) ^ "\n");
val _ = emit "compile_inc_progs_for_eval_def_typed" (DB.fetch "backend" "compile_inc_progs_for_eval_def");
val _ = emit "SND_flat_to_clos_inc_compile_typed"
  (REWRITE_CONV [flat_to_closTheory.inc_compile_decs_def]
    ``SND (flat_to_clos$inc_compile_decs p)``);
val _ = print "backend_proof_more_probe_end=1\n";
