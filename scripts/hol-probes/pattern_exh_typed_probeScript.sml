load "preamble";
load "pattern_exhTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pattern_exhTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pattern_exh",Name=name} of
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

val source_text = source_text_of "compiler/backend/pattern_matching/pattern_exhScript.sml";

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

fun strip_antiquote s =
  let
    fun go [] acc = String.concat (List.rev acc)
      | go (#"^" :: rest) acc =
        (case rest of
           (c :: _) => if Char.isAlphaNum c orelse c = #"_"
                       then go rest acc
                       else go rest (String.str #"^" :: acc)
         | [] => go rest (String.str #"^" :: acc))
      | go (c :: rest) acc = go rest (String.str c :: acc)
  in go (String.explode s) [] end;

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


val _ = capture "LENGTH_anys_typed" "LENGTH_anys";
val _ = capture "LENGTH_dest_val_typed" "LENGTH_dest_val";
val _ = capture "LENGTH_expand_list_typed" "LENGTH_expand_list";
val _ = capture "MEM_add_head_typed" "MEM_add_head";
val _ = capture "MEM_ctor_keep_typed" "MEM_ctor_keep";
val _ = capture "MEM_ctor_nub_typed" "MEM_ctor_nub";
val _ = capture "MEM_mk_conses_typed" "MEM_mk_conses";
val _ = capture "MEM_mk_prods_typed" "MEM_mk_prods";
val _ = capture "MEM_mk_refs_typed" "MEM_mk_refs";
val _ = capture "MEM_mk_rows_typed" "MEM_mk_rows";
val _ = capture "MEM_spec_mats_typed" "MEM_spec_mats";
val _ = capture "MEM_tag_ctors_typed" "MEM_tag_ctors";
val _ = emit_exported "add_head_def_typed" "add_head_def";
val _ = emit_exported "anys_def_typed" "anys_def";
val _ = emit_exported "col_ctors_def_typed" "col_ctors_def";
val _ = capture "col_ctors_thm_typed" "col_ctors_thm";
val _ = capture_dt "ctor_typed" (mk_type ("ctor", []));
val _ = emit_exported "ctor_arity_def_typed" "ctor_arity_def";
val _ = emit_exported "ctor_inter_def_typed" "ctor_inter_def";
val _ = emit_exported "ctor_keep_def_typed" "ctor_keep_def";
val _ = emit_exported "ctor_nub_def_typed" "ctor_nub_def";
val _ = emit_exported "ctors_of_def_typed" "ctors_of_def";
val _ = capture "ctors_of_thm_typed" "ctors_of_thm";
val _ = capture "default_mat_MEM_typed" "default_mat_MEM";
val _ = emit_exported "default_mat_def_typed" "default_mat_def";
val _ = emit_exported "default_row_def_typed" "default_row_def";
val _ = capture "default_row_thm_typed" "default_row_thm";
val _ = emit_exported "dest_val_def_typed" "dest_val_def";
val _ = capture "dest_val_eq_SOME_typed" "dest_val_eq_SOME";
val _ = emit_exported "exh_all_def_typed" "exh_all_def";
val _ = capture "exh_all_thm_typed" "exh_all_thm";
val _ = emit_exported "exh_matrix_def_typed" "exh_matrix_def";
val _ = capture "exh_matrix_thm_typed" "exh_matrix_thm";
val _ = capture "exh_mats_append_typed" "exh_mats_append";
val _ = emit_exported "exh_rows_def_typed" "exh_rows_def";
val _ = emit_exported "exh_rows_eq_typed" "exh_rows_eq";
val _ = emit_exported "exh_rows_thm_typed" "exh_rows_thm";
val _ = emit_exported "exh_steps_def_typed" "exh_steps_def";
val _ = capture "exh_steps_list_append_typed" "exh_steps_list_append";
val _ = emit_exported "expand_def_typed" "expand_def";
val _ = capture "expand_thm_typed" "expand_thm";
val _ = capture "mat_len_append_typed" "mat_len_append";
val _ = emit_exported "mat_len_def_typed" "mat_len_def";
val _ = capture "mat_len_default_mat_typed" "mat_len_default_mat";
val _ = capture "mat_len_default_mat_less_typed" "mat_len_default_mat_less";
val _ = capture "mat_weight_append_typed" "mat_weight_append";
val _ = emit_exported "mat_weight_def_typed" "mat_weight_def";
val _ = capture "mat_weight_default_mat_typed" "mat_weight_default_mat";
val _ = capture "mat_weight_spec_mat_typed" "mat_weight_spec_mat";
val _ = capture "mat_weight_spec_mat_less_typed" "mat_weight_spec_mat_less";
val _ = capture "mat_weight_spec_row_typed" "mat_weight_spec_row";
val _ = capture "mat_weight_spec_row_less_typed" "mat_weight_spec_row_less";
val _ = capture "match_EXISTS_typed" "match_EXISTS";
val _ = capture "match_no_PTypeFailure_typed" "match_no_PTypeFailure";
val _ = emit_exported "mats_len_def_typed" "mats_len_def";
val _ = emit_exported "mats_weight_def_typed" "mats_weight_def";
val _ = capture "mats_weight_spec_mats_typed" "mats_weight_spec_mats";
val _ = emit_exported "mk_conses_def_typed" "mk_conses_def";
val _ = emit_exported "mk_prods_def_typed" "mk_prods_def";
val _ = emit_exported "mk_refs_def_typed" "mk_refs_def";
val _ = emit_exported "mk_rows_def_typed" "mk_rows_def";
val _ = emit_exported "or_rows_def_typed" "or_rows_def";
val _ = capture "or_rows_hit_typed" "or_rows_hit";
val _ = capture "or_rows_ok_typed" "or_rows_ok";
val _ = capture "pand_assoc_typed" "pand_assoc";
val _ = emit_exported "pand_def_typed" "pand_def";
val _ = capture "pand_eq_PMatchSuccess_typed" "pand_eq_PMatchSuccess";
val _ = capture "pand_eq_PTypeFailure_typed" "pand_eq_PTypeFailure";
val _ = capture "pand_simps_typed" "pand_simps";
val _ = emit_exported "pat_weight_def_typed" "pat_weight_def";
val _ = capture "pats_weight_anys_typed" "pats_weight_anys";
val _ = capture "pats_weight_append_typed" "pats_weight_append";
val _ = capture "pmatch_Any_typed" "pmatch_Any";
val _ = capture "pmatch_list_LENGTH_typed" "pmatch_list_LENGTH";
val _ = capture "pmatch_list_anys_typed" "pmatch_list_anys";
val _ = capture "pmatch_list_append_typed" "pmatch_list_append";
val _ = capture "pmatch_list_cons_typed" "pmatch_list_cons";
val _ = capture "pmatch_list_nil_typed" "pmatch_list_nil";
val _ = capture "spec_mat_MEM_typed" "spec_mat_MEM";
val _ = emit_exported "spec_mat_def_typed" "spec_mat_def";
val _ = emit_exported "spec_mats_def_typed" "spec_mats_def";
val _ = emit_exported "spec_row_def_typed" "spec_row_def";
val _ = capture "spec_row_thm_typed" "spec_row_thm";
val _ = emit_exported "tag_ctors_def_typed" "tag_ctors_def";
