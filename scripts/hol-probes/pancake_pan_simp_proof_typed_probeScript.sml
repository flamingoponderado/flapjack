(* Typed captures for the pan_simpProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   28 names: 28 exported (fetched from the theory DB), 0 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 0 derived local theorems captured through
   their base statement, 0 datatypes.
*)
load "preamble";
load "pan_simpProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pan_simpProofTheory;
open panSemTheory pan_simpTheory panPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pan_simpProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

fun emit_as label th = emit label th;

fun fetch_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => th;

fun emit_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => emit (name ^ "_typed") th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_simpProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;

fun after_prefix pre s =
  case Substring.position pre (Substring.full s) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);

fun statement_of name =
  let
    val header = after_prefix ("\nTheorem " ^ name) source_text
    val rest = after_prefix ":\n" header
    val (stmt, _) = Substring.position "\nProof" (Substring.full rest)
  in Substring.string stmt end;

(* The source statements are quoted literally. A `^` immediately
   followed by an identifier is an SML antiquotation of a term
   variable; the capture drops the marker and keeps the variable,
   which is the term the original script substitutes. An infix
   `^` (mlstring concatenation) is followed by a space and is kept. *)
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

val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = emit_exported "compile_correct_same_state_typed" "compile_correct_same_state";
val _ = emit_exported "compile_eval_correct_typed" "compile_eval_correct";
val _ = emit_exported "decs_stcnames_compile_prog_typed" "decs_stcnames_compile_prog";
val _ = emit_exported "eval_seq_assoc_eq_evaluate_typed" "eval_seq_assoc_eq_evaluate";
val _ = emit_exported "eval_seq_assoc_not_error_typed" "eval_seq_assoc_not_error";
val _ = emit_exported "evaluate_SmartSeq_typed" "evaluate_SmartSeq";
val _ = emit_exported "evaluate_seq_assoc_typed" "evaluate_seq_assoc";
val _ = emit_exported "evaluate_seq_call_ret_eq_typed" "evaluate_seq_call_ret_eq";
val _ = emit_exported "evaluate_seq_no_error_fst_typed" "evaluate_seq_no_error_fst";
val _ = emit_exported "evaluate_seq_simp_typed" "evaluate_seq_simp";
val _ = emit_exported "evaluate_seq_skip_typed" "evaluate_seq_skip";
val _ = emit_exported "evaluate_skip_seq_typed" "evaluate_skip_seq";
val _ = emit_exported "evaluate_while_body_same_typed" "evaluate_while_body_same";
val _ = emit_exported "evaluate_while_no_error_imp_typed" "evaluate_while_no_error_imp";
val _ = emit_exported "exp_ids_compile_eq_typed" "exp_ids_compile_eq";
val _ = emit_exported "exp_ids_ret_to_tail_eq_typed" "exp_ids_ret_to_tail_eq";
val _ = emit_exported "exp_ids_seq_assoc_eq_typed" "exp_ids_seq_assoc_eq";
val _ = emit_exported "first_compile_prog_all_distinct_typed" "first_compile_prog_all_distinct";
val _ = emit_exported "functions_compile_prog_typed" "functions_compile_prog";
val _ = emit_exported "map_snd_f_eq_typed" "map_snd_f_eq";
val _ = emit_exported "ret_to_tail_correct_typed" "ret_to_tail_correct";
val _ = emit_exported "size_of_eids_compile_eq_typed" "size_of_eids_compile_eq";
val _ = emit_exported "state_rel_def_typed" "state_rel_def";
val _ = emit_exported "state_rel_imp_evaluate_decls_typed" "state_rel_imp_evaluate_decls";
val _ = emit_exported "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit_exported "state_rel_imp_semantics_decls_typed" "state_rel_imp_semantics_decls";
val _ = emit_exported "state_rel_intro_typed" "state_rel_intro";
