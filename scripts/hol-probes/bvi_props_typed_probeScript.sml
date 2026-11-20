(* Typed source declarations for bviProps (task 238).
   Exported theorems are fetched from the theory DB; `[local]` theorems are
   parsed from the pinned source text with `^antiquotation` splices expanded,
   as in bvl_props_typed_probeScript.sml. *)
load "preamble";
load "bviPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble bviPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bviProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bviProps")
  | SOME (th,_) => show label th;

(* Group 1: state projections and clock lemmas. *)
val _ = emit "initial_state_simp_typed" "initial_state_simp";
val _ = emit "initial_state_with_simp_typed" "initial_state_with_simp";
val _ = emit "inc_clock_refs_typed" "inc_clock_refs";
val _ = emit "inc_clock_code_typed" "inc_clock_code";
val _ = emit "inc_clock_global_typed" "inc_clock_global";
val _ = emit "inc_clock_ffi_typed" "inc_clock_ffi";
val _ = emit "inc_clock_clock_typed" "inc_clock_clock";
val _ = emit "dec_clock_global_typed" "dec_clock_global";
val _ = emit "dec_clock_ffi_typed" "dec_clock_ffi";
val _ = emit "dec_clock_refs_typed" "dec_clock_refs";
val _ = emit "dec_clock_with_code_typed" "dec_clock_with_code";
val _ = emit "dec_clock_code_typed" "dec_clock_code";
val _ = emit "dec_clock0_typed" "dec_clock0";
val _ = emit "inc_clock_eq_0_typed" "inc_clock_eq_0";
val _ = emit "inc_clock_ADD_typed" "inc_clock_ADD";
val _ = emit "dec_clock_inv_clock_typed" "dec_clock_inv_clock";
val _ = emit "dec_clock_inv_clock1_typed" "dec_clock_inv_clock1";
val _ = emit "evaluate_code_mono_typed" "evaluate_code_mono";

(* Group 3: evaluate-shape lemmas. *)
val _ = emit "evaluate_LENGTH_typed" "evaluate_LENGTH";
val _ = emit "evaluate_IMP_LENGTH_typed" "evaluate_IMP_LENGTH";
val _ = emit "evaluate_SING_IMP_typed" "evaluate_SING_IMP";
val _ = emit "evaluate_CONS_typed" "evaluate_CONS";
val _ = emit "evaluate_SNOC_typed" "evaluate_SNOC";
val _ = emit "evaluate_APPEND_typed" "evaluate_APPEND";

(* Group 4a: primitive-application clock and I/O-event lemmas. *)
val _ = emit "do_app_change_clock_typed" "do_app_change_clock";
val _ = emit "do_app_change_clock_err_typed" "do_app_change_clock_err";
val _ = emit "evaluate_add_clock_typed" "evaluate_add_clock";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_add_to_clock_io_events_mono_typed" "evaluate_add_to_clock_io_events_mono";

(* Group 4b: primitive-application code, oracle, error and clock lemmas. *)
val _ = emit "adj_orac_def_typed" "adj_orac_def";
val _ = emit "adj_orac_ok_def_typed" "adj_orac_ok_def";
val _ = emit "adj_orac_rel_def_typed" "adj_orac_rel_def";
val _ = emit "evaluate_inv_clock_typed" "evaluate_inv_clock";
val _ = emit "do_app_code_typed" "do_app_code";
val _ = emit "do_app_oracle_typed" "do_app_oracle";
val _ = emit "evaluate_global_mono_typed" "evaluate_global_mono";
val _ = emit "do_app_err_typed" "do_app_err";
val _ = emit "do_app_aux_const_typed" "do_app_aux_const";
val _ = emit "do_app_with_code_typed" "do_app_with_code";
val _ = emit "do_app_with_code_err_typed" "do_app_with_code_err";
val _ = emit "do_app_aux_with_clock_typed" "do_app_aux_with_clock";
val _ = emit "do_app_aux_io_events_mono_typed" "do_app_aux_io_events_mono";

(* `[local]` theorems are not exported by the theory; parse their pinned
   source statements, expanding `^x` splices to the term bound by
   `val x = ``...``;`. *)
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

val source_text = source_text_of "compiler/backend/semantics/bviPropsScript.sml";

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
           | NONE => scan rest)
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

  (* ``term`` or curly-quoted "term" (UTF-8), possibly spanning lines *)
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
          (case type_text body of
             SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
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

val _ = capture "do_app_inv_clock_typed" "do_app_inv_clock";
val _ = capture "do_app_inc_clock_IMP_typed" "do_app_inc_clock_IMP";
val _ = capture "do_app_inc_clock_typed" "do_app_inc_clock";
val _ = capture "adj_orac_simps_typed" "adj_orac_simps";
val _ = capture "evaluate_global_mono_lemma_typed" "evaluate_global_mono_lemma";
val _ = capture "dec_clock_1_inc_clock_typed" "dec_clock_1_inc_clock";
val _ = capture "dec_clock_1_inc_clock2_typed" "dec_clock_1_inc_clock2";
val _ = capture "dec_clock_inc_clock_typed" "dec_clock_inc_clock";
val _ = capture "take_drop_lem_typed" "take_drop_lem";
