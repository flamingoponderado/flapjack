load "preamble";
load "fromSexpTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open fromSexpTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="fromSexp",Name=name} of
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

val source_text = source_text_of "compiler/parsing/fromSexpScript.sml";

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


val _ = emit_exported "SEXSTR_11_typed" "SEXSTR_11";
val _ = emit_exported "SEXSTR_def_typed" "SEXSTR_def";
val _ = emit_exported "SEXSTR_distinct_typed" "SEXSTR_distinct";
val _ = emit_exported "SEXSTR_remove_typed" "SEXSTR_remove";
val _ = emit_exported "arithsexp_11_typed" "arithsexp_11";
val _ = emit_exported "arithsexp_def_typed" "arithsexp_def";
val _ = emit_exported "arithsexp_sexparith_typed" "arithsexp_sexparith";
val _ = emit_exported "decode_control_def_typed" "decode_control_def";
val _ = emit_exported "decode_encode_control_typed" "decode_encode_control";
val _ = emit_exported "decode_prim_type_def_typed" "decode_prim_type_def";
val _ = emit_exported "decode_prim_type_prim_typesexp_typed" "decode_prim_type_prim_typesexp";
val _ = emit_exported "decode_test_def_typed" "decode_test_def";
val _ = emit_exported "decode_test_testsexp_typed" "decode_test_testsexp";
val _ = emit_exported "decsexp_11_typed" "decsexp_11";
val _ = emit_exported "decsexp_def_typed" "decsexp_def";
val _ = emit_exported "decsexp_sexpdec_typed" "decsexp_sexpdec";
val _ = emit_exported "encode_control_def_typed" "encode_control_def";
val _ = emit_exported "encode_control_remove_typed" "encode_control_remove";
val _ = emit_exported "encode_decode_control_typed" "encode_decode_control";
val _ = emit_exported "expsexp_11_typed" "expsexp_11";
val _ = emit_exported "expsexp_def_typed" "expsexp_def";
val _ = emit_exported "expsexp_sexpexp_typed" "expsexp_sexpexp";
val _ = emit_exported "idsexp_11_typed" "idsexp_11";
val _ = emit_exported "idsexp_def_typed" "idsexp_def";
val _ = emit_exported "idsexp_sexpid_odestSEXSTR_typed" "idsexp_sexpid_odestSEXSTR";
val _ = emit_exported "idsexp_sexpid_odestSEXSTR_prime_typed" "idsexp_sexpid_odestSEXSTR'";
val _ = emit_exported "listsexp_11_typed" "listsexp_11";
val _ = emit_exported "listsexp_def_typed" "listsexp_def";
val _ = emit_exported "litsexp_11_typed" "litsexp_11";
val _ = emit_exported "litsexp_def_typed" "litsexp_def";
val _ = emit_exported "litsexp_sexplit_typed" "litsexp_sexplit";
val _ = emit_exported "locnsexp_11_typed" "locnsexp_11";
val _ = emit_exported "locnsexp_def_typed" "locnsexp_def";
val _ = emit_exported "locnsexp_sexplocn_typed" "locnsexp_sexplocn";
val _ = emit_exported "locnsexp_sexplocpt_typed" "locnsexp_sexplocpt";
val _ = emit_exported "locnsexp_sexplocpt0_typed" "locnsexp_sexplocpt0";
val _ = emit_exported "locssexp_11_typed" "locssexp_11";
val _ = emit_exported "locssexp_def_typed" "locssexp_def";
val _ = emit_exported "logsexp_11_typed" "logsexp_11";
val _ = emit_exported "logsexp_def_typed" "logsexp_def";
val _ = emit_exported "logsexp_sexplog_typed" "logsexp_sexplog";
val _ = emit_exported "odestSEXSTR_SEXSTR_typed" "odestSEXSTR_SEXSTR";
val _ = emit_exported "odestSEXSTR_SOME_typed" "odestSEXSTR_SOME";
val _ = emit_exported "odestSEXSTR_def_typed" "odestSEXSTR_def";
val _ = emit_exported "opsexp_11_typed" "opsexp_11";
val _ = emit_exported "opsexp_def_typed" "opsexp_def";
val _ = emit_exported "opsexp_sexpop_typed" "opsexp_sexpop";
val _ = emit_exported "optsexp_11_typed" "optsexp_11";
val _ = emit_exported "optsexp_def_typed" "optsexp_def";
val _ = emit_exported "patsexp_11_typed" "patsexp_11";
val _ = emit_exported "patsexp_def_typed" "patsexp_def";
val _ = emit_exported "patsexp_sexppat_typed" "patsexp_sexppat";
val _ = emit_exported "patsexp_sexppat0_typed" "patsexp_sexppat0";
val _ = emit_exported "prim_typesexp_11_typed" "prim_typesexp_11";
val _ = emit_exported "prim_typesexp_def_typed" "prim_typesexp_def";
val _ = emit_exported "sexparith_arithsexp_typed" "sexparith_arithsexp";
val _ = emit_exported "sexparith_def_typed" "sexparith_def";
val _ = emit_exported "sexpdec_decsexp_typed" "sexpdec_decsexp";
val _ = emit_exported "sexpdec_def_typed" "sexpdec_def";
val _ = emit_exported "sexpexp_def_typed" "sexpexp_def";
val _ = emit_exported "sexpexp_expsexp_typed" "sexpexp_expsexp";
val _ = emit_exported "sexpid_def_typed" "sexpid_def";
val _ = emit_exported "sexpid_odestSEXSTR_idsexp_typed" "sexpid_odestSEXSTR_idsexp";
val _ = emit_exported "sexplist_SOME_typed" "sexplist_SOME";
val _ = emit_exported "sexplist_def_typed" "sexplist_def";
val _ = emit_exported "sexplist_listsexp_rwt_typed" "sexplist_listsexp_rwt";
val _ = emit_exported "sexplit_def_typed" "sexplit_def";
val _ = emit_exported "sexplit_litsexp_typed" "sexplit_litsexp";
val _ = emit_exported "sexplocn_def_typed" "sexplocn_def";
val _ = emit_exported "sexplocn_locnsexp_typed" "sexplocn_locnsexp";
val _ = emit_exported "sexplocpt_def_typed" "sexplocpt_def";
val _ = emit_exported "sexplocpt_locnsexp_typed" "sexplocpt_locnsexp";
val _ = emit_exported "sexplog_def_typed" "sexplog_def";
val _ = emit_exported "sexplog_logsexp_typed" "sexplog_logsexp";
val _ = emit_exported "sexpop_def_typed" "sexpop_def";
val _ = emit_exported "sexpop_opsexp_typed" "sexpop_opsexp";
val _ = emit_exported "sexpopt_SOME_typed" "sexpopt_SOME";
val _ = emit_exported "sexpopt_def_typed" "sexpopt_def";
val _ = emit_exported "sexpopt_optsexp_typed" "sexpopt_optsexp";
val _ = emit_exported "sexppair_SOME_typed" "sexppair_SOME";
val _ = emit_exported "sexppair_def_typed" "sexppair_def";
val _ = emit_exported "sexppat_def_typed" "sexppat_def";
val _ = emit_exported "sexppat_patsexp_typed" "sexppat_patsexp";
val _ = emit_exported "sexpprim_type_testsexp_typed" "sexpprim_type_testsexp";
val _ = emit_exported "sexptest_testsexp_typed" "sexptest_testsexp";
val _ = emit_exported "sexptype_def_typed" "sexptype_def";
val _ = emit_exported "sexptype_def_def_typed" "sexptype_def_def";
val _ = emit_exported "sexptype_def_type_defsexp_typed" "sexptype_def_type_defsexp";
val _ = emit_exported "sexptype_typesexp_typed" "sexptype_typesexp";
val _ = emit_exported "testsexp_11_typed" "testsexp_11";
val _ = emit_exported "testsexp_def_typed" "testsexp_def";
val _ = emit_exported "type_defsexp_11_typed" "type_defsexp_11";
val _ = emit_exported "type_defsexp_def_typed" "type_defsexp_def";
val _ = emit_exported "type_defsexp_sexptype_def_typed" "type_defsexp_sexptype_def";
val _ = emit_exported "typesexp_11_typed" "typesexp_11";
val _ = emit_exported "typesexp_def_typed" "typesexp_def";
val _ = emit_exported "typesexp_sexptype_typed" "typesexp_sexptype";
