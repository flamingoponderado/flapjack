load "preamble";
load "word_to_wordProofTheory";
load "word_to_wordTheory";
load "word_simpTheory";
load "word_allocTheory";
load "word_instTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="word_to_wordProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/word_to_wordProofScript.sml";

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

fun capture_dt label (thy,ctor) =
  let
    val ty = type_of (prim_mk_const {Thy=thy,Name=ctor})
    val cs = TypeBase.constructors_of ty
  in
    print (label ^ "=");
    print (String.concatWith "; "
      (map (fn c => let val (n,t) = dest_const c
         in n ^ ":" ^ type_to_string t end) cs));
    print "\n"
  end;

val _ = emit_exported "code_rel_def_typed" "code_rel_def";
val _ = emit_exported "compile_to_word_conventions_typed" "compile_to_word_conventions";
val _ = emit_exported "panLang_compile_word_to_word_thm_typed" "panLang_compile_word_to_word_thm";
val _ = emit_exported "word_to_word_compile_semantics_typed" "word_to_word_compile_semantics";
val _ = emit_exported "FST_compile_single_typed" "FST_compile_single";
val _ = emit_exported "compile_single_lem_typed" "compile_single_lem";
val _ = emit_exported "compile_word_to_word_thm_typed" "compile_word_to_word_thm";
val _ = emit_exported "no_install_no_alloc_compile_single_correct_typed" "no_install_no_alloc_compile_single_correct";
val _ = emit_exported "code_rel_ext_def_typed" "code_rel_ext_def";
val _ = emit_exported "code_rel_ext_word_to_word_typed" "code_rel_ext_word_to_word";
val _ = emit_exported "code_rel_no_share_inst_typed" "code_rel_no_share_inst";
val _ = emit_exported "code_rel_not_created_subprogs_typed" "code_rel_not_created_subprogs";
val _ = emit_exported "cond16bit_inst_select_typed" "cond16bit_inst_select";
val _ = emit_exported "cond16bit_inst_select_exp_prime_typed" "cond16bit_inst_select_exp'";
val _ = emit_exported "full_compile_single_no_share_inst_typed" "full_compile_single_no_share_inst";
val _ = emit_exported "no_mt_code_full_compile_single_typed" "no_mt_code_full_compile_single";
val _ = emit_exported "no_mt_code_rel_ext_typed" "no_mt_code_rel_ext";
val _ = emit_exported "no_mt_full_compile_single_typed" "no_mt_full_compile_single";
val _ = emit_exported "no_mt_remove_must_terminate_const_typed" "no_mt_remove_must_terminate_const";
val _ = emit_exported "remove_must_terminate_no_share_inst_typed" "remove_must_terminate_no_share_inst";
val _ = capture "code_rel_union_fromAList_typed" "code_rel_union_fromAList";
val _ = capture "compile_single_eta_typed" "compile_single_eta";
val _ = capture "find_code_thm_typed" "find_code_thm";
val _ = capture "pop_env_termdep_typed" "pop_env_termdep";
val _ = capture "rm_perm_typed" "rm_perm";
val _ = capture "compile_single_correct_typed" "compile_single_correct";

(* Derived local theorems, replayed exactly as the source derives them from
   the exported code_rel_not_created_subprogs. *)
val code_rel_P =
  Q.GEN `P` (fetch_other ("word_to_wordProof","code_rel_not_created_subprogs"));
val _ = emit_as "code_rel_no_alloc_typed"
  (code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))`
    |> REWRITE_RULE [GSYM (fetch_other ("wordConvs","no_alloc_subprogs_def"))]);
val _ = emit_as "code_rel_no_install_typed"
  (code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))`
    |> REWRITE_RULE [GSYM (fetch_other ("wordConvs","no_install_subprogs_def"))]);
