load "preamble";
load "reg_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open reg_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val _ = monadsyntax.temp_add_monadsyntax();
val _ = monadsyntax.temp_enable_monad "st_ex";

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="reg_allocProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml";

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
  in (print (label ^ "="); print_term tm; print "\n") end;

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


val _ = capture "ALL_DISTINCT_set_INJ_typed" "ALL_DISTINCT_set_INJ";
val _ = capture "GT_TRANS_typed" "GT_TRANS";
val _ = capture "GT_sorted_eq_typed" "GT_sorted_eq";
val _ = capture "INJ_less_typed" "INJ_less";
val _ = capture "MEM_MAP_IMAGE_typed" "MEM_MAP_IMAGE";
val _ = capture "MEM_smerge_typed" "MEM_smerge";
val _ = capture "SORTED_HEAD_LT_typed" "SORTED_HEAD_LT";
val _ = capture "UNION_DIFF_3_typed" "UNION_DIFF_3";
val _ = capture "assign_Atemps_FOREACH_lem_typed" "assign_Atemps_FOREACH_lem";
val _ = capture "assign_Stemps_FOREACH_lem_typed" "assign_Stemps_FOREACH_lem";
val _ = capture "bg_ok_success_typed" "bg_ok_success";
val _ = capture "canonize_move_success_typed" "canonize_move_success";
val _ = capture "coalesce_parent_success_typed" "coalesce_parent_success";
val _ = capture "consistency_ok_success_typed" "consistency_ok_success";
val _ = capture "dec_deg_success_typed" "dec_deg_success";
val _ = capture "dec_degree_success_typed" "dec_degree_success";
val _ = capture "do_alloc1_success_typed" "do_alloc1_success";
val _ = capture "do_coalesce_real_success_typed" "do_coalesce_real_success";
val _ = capture "do_coalesce_success_typed" "do_coalesce_success";
val _ = capture "do_freeze_success_typed" "do_freeze_success";
val _ = capture "do_prefreeze_success_typed" "do_prefreeze_success";
val _ = capture "do_simplify_success_typed" "do_simplify_success";
val _ = capture "do_spill_success_typed" "do_spill_success";
val _ = capture "do_step_success_typed" "do_step_success";
val _ = capture "domain_eq_IMAGE_typed" "domain_eq_IMAGE";
val _ = capture "extract_color_st_ex_MAP_lem_typed" "extract_color_st_ex_MAP_lem";
val _ = capture "first_match_col_correct_typed" "first_match_col_correct";
val _ = capture "full_consistency_ok_success_typed" "full_consistency_ok_success";
val _ = capture "is_clique_FILTER_typed" "is_clique_FILTER";
val _ = capture "is_clique_subgraph_typed" "is_clique_subgraph";
val _ = capture "is_not_coalesced_succeeds_typed" "is_not_coalesced_succeeds";
val _ = capture "list_remap_domain_typed" "list_remap_domain";
val _ = capture "list_remap_wf_typed" "list_remap_wf";
val _ = capture "mk_bij_aux_domain_typed" "mk_bij_aux_domain";
val _ = capture "mk_tags_st_ex_FOREACH_lem_typed" "mk_tags_st_ex_FOREACH_lem";
val _ = capture "neg_first_match_col_correct_typed" "neg_first_match_col_correct";
val _ = capture "no_clash_LUPDATE_Fixed_typed" "no_clash_LUPDATE_Fixed";
val _ = capture "no_clash_LUPDATE_Stemp_typed" "no_clash_LUPDATE_Stemp";
val _ = capture "opt_split_typed" "opt_split";
val _ = capture "push_stack_success_typed" "push_stack_success";
val _ = capture "remove_colours_succeeds_typed" "remove_colours_succeeds";
val _ = capture "reset_move_related_success_typed" "reset_move_related_success";
val _ = capture "revive_moves_success_typed" "revive_moves_success";
val _ = capture "rpt_do_step_success_typed" "rpt_do_step_success";
val _ = capture "set_FILTER_typed" "set_FILTER";
val _ = capture "sorted_insert_correct_lem_typed" "sorted_insert_correct_lem";
val _ = capture "st_ex_FILTER_considered_var_typed" "st_ex_FILTER_considered_var";
val _ = capture "st_ex_FILTER_consistency_ok_typed" "st_ex_FILTER_consistency_ok";
val _ = capture "st_ex_FILTER_full_consistency_ok_typed" "st_ex_FILTER_full_consistency_ok";
val _ = capture "st_ex_FILTER_is_not_coalesced_typed" "st_ex_FILTER_is_not_coalesced";
val _ = capture "st_ex_FIRST_consistency_ok_bg_ok_typed" "st_ex_FIRST_consistency_ok_bg_ok";
val _ = capture "st_ex_FOREACH_update_move_related_typed" "st_ex_FOREACH_update_move_related";
val _ = capture "st_ex_PARTITION_move_related_sub_typed" "st_ex_PARTITION_move_related_sub";
val _ = capture "st_ex_PARTITION_split_degree_typed" "st_ex_PARTITION_split_degree";
val _ = capture "st_ex_list_MAX_deg_success_typed" "st_ex_list_MAX_deg_success";
val _ = capture "st_ex_list_MIN_cost_success_typed" "st_ex_list_MIN_cost_success";
val _ = capture "unspill_success_typed" "unspill_success";
