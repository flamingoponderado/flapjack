(* Typed captures for the loop_to_wordProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   74 names: 65 exported (fetched from the theory DB), 8 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 1 derived local theorems captured through
   their base statement, 0 datatypes.
*)
load "preamble";
load "loop_to_wordProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open loop_to_wordProofTheory;
open backend_commonTheory loopSemTheory loopPropsTheory wordLangTheory wordSemTheory wordPropsTheory pan_commonTheory pan_commonPropsTheory loop_to_wordTheory wordConvsTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="loop_to_wordProof",Name=name} of
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
  (OS.Path.concat (source_cake, "pancake/proofs/loop_to_wordProofScript.sml"));
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

val _ = emit_exported "TAKE_1_word_to_bytes_typed" "TAKE_1_word_to_bytes";
val _ = emit_exported "code_rel_def_typed" "code_rel_def";
val _ = emit_exported "code_rel_intro_typed" "code_rel_intro";
val _ = emit_exported "comp_exp_preserves_eval_typed" "comp_exp_preserves_eval";
val _ = emit_exported "comp_l_invariant_typed" "comp_l_invariant";
val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = emit_exported "cut_env_LN_IMP_typed" "cut_env_LN_IMP";
val _ = emit_exported "cut_env_mk_new_cutset_typed" "cut_env_mk_new_cutset";
val _ = emit_exported "cut_env_mk_new_cutset_IMP_typed" "cut_env_mk_new_cutset_IMP";
val _ = emit_exported "domain_make_ctxt_typed" "domain_make_ctxt";
val _ = emit_exported "domain_mk_new_cutset_not_empty_typed" "domain_mk_new_cutset_not_empty";
val _ = emit_exported "domain_toNumSet_typed" "domain_toNumSet";
val _ = emit_exported "env_to_list_IMP_typed" "env_to_list_IMP";
val _ = emit_exported "env_to_list_LN_IMP_typed" "env_to_list_LN_IMP";
val _ = emit_exported "find_var_neq_0_typed" "find_var_neq_0";
val _ = emit_exported "find_var_neq_0_ctxt_typed" "find_var_neq_0_ctxt";
val _ = emit_exported "find_var_neq_odd_typed" "find_var_neq_odd";
val _ = emit_exported "first_compile_all_distinct_typed" "first_compile_all_distinct";
val _ = emit_exported "first_compile_prog_all_distinct_typed" "first_compile_prog_all_distinct";
val _ = emit_exported "globals_rel_def_typed" "globals_rel_def";
val _ = emit_exported "globals_rel_intro_typed" "globals_rel_intro";
val _ = emit_exported "good_handlers_comp_typed" "good_handlers_comp";
val _ = emit_exported "locals_rel_ALL_DISTINCT_MAP_typed" "locals_rel_ALL_DISTINCT_MAP";
val _ = emit_exported "locals_rel_alist_insert_typed" "locals_rel_alist_insert";
val _ = emit_exported "locals_rel_alist_insert_toAList_typed" "locals_rel_alist_insert_toAList";
val _ = emit_exported "locals_rel_def_typed" "locals_rel_def";
val _ = emit_exported "locals_rel_get_var_typed" "locals_rel_get_var";
val _ = emit_exported "locals_rel_get_vars_typed" "locals_rel_get_vars";
val _ = emit_exported "locals_rel_insert_typed" "locals_rel_insert";
val _ = emit_exported "locals_rel_insert_unmapped_typed" "locals_rel_insert_unmapped";
val _ = emit_exported "locals_rel_intro_typed" "locals_rel_intro";
val _ = emit_exported "locals_rel_make_ctxt_typed" "locals_rel_make_ctxt";
val _ = emit_exported "locals_rel_mk_ctxt_ln_typed" "locals_rel_mk_ctxt_ln";
val _ = emit_exported "lookup_EL_make_ctxt_typed" "lookup_EL_make_ctxt";
val _ = emit_exported "lookup_make_ctxt_EVEN_typed" "lookup_make_ctxt_EVEN";
val _ = emit_exported "lookup_make_ctxt_range_typed" "lookup_make_ctxt_range";
val _ = emit_exported "lookup_prog_some_lookup_compile_prog_typed" "lookup_prog_some_lookup_compile_prog";
val _ = emit_exported "loop_compile_no_alloc_code_typed" "loop_compile_no_alloc_code";
val _ = emit_exported "loop_compile_no_install_code_typed" "loop_compile_no_install_code";
val _ = emit_exported "loop_compile_no_mt_code_typed" "loop_compile_no_mt_code";
val _ = emit_exported "loop_inst_ok_def_typed" "loop_inst_ok_def";
val _ = emit_exported "loop_to_word_comp_ALL_DISTINCT_typed" "loop_to_word_comp_ALL_DISTINCT";
val _ = emit_exported "loop_to_word_comp_SND_LE_typed" "loop_to_word_comp_SND_LE";
val _ = emit_exported "loop_to_word_comp_every_inst_ok_less_typed" "loop_to_word_comp_every_inst_ok_less";
val _ = emit_exported "loop_to_word_comp_extract_labels_typed" "loop_to_word_comp_extract_labels";
val _ = emit_exported "loop_to_word_comp_extract_labels_len_typed" "loop_to_word_comp_extract_labels_len";
val _ = emit_exported "loop_to_word_comp_func_every_inst_ok_less_typed" "loop_to_word_comp_func_every_inst_ok_less";
val _ = emit_exported "loop_to_word_comp_func_lab_pres_typed" "loop_to_word_comp_func_lab_pres";
val _ = emit_exported "loop_to_word_comp_func_not_created_typed" "loop_to_word_comp_func_not_created";
val _ = emit_exported "loop_to_word_comp_not_created_typed" "loop_to_word_comp_not_created";
val _ = emit_exported "loop_to_word_compile_lab_min_typed" "loop_to_word_compile_lab_min";
val _ = emit_exported "loop_to_word_compile_not_created_typed" "loop_to_word_compile_not_created";
val _ = emit_exported "loop_to_word_compile_prog_FST_eq_typed" "loop_to_word_compile_prog_FST_eq";
val _ = emit_exported "loop_to_word_compile_prog_every_inst_ok_less_typed" "loop_to_word_compile_prog_every_inst_ok_less";
val _ = emit_exported "loop_to_word_compile_prog_lab_min_typed" "loop_to_word_compile_prog_lab_min";
val _ = emit_exported "loop_to_word_compile_prog_lab_pres_typed" "loop_to_word_compile_prog_lab_pres";
val _ = emit_exported "loop_to_word_every_inst_ok_less_typed" "loop_to_word_every_inst_ok_less";
val _ = emit_exported "loop_to_word_good_handlers_typed" "loop_to_word_good_handlers";
val _ = emit_exported "make_ctxt_inj_typed" "make_ctxt_inj";
val _ = emit_exported "mem_prog_mem_compile_prog_typed" "mem_prog_mem_compile_prog";
val _ = emit_exported "set_fromNumSet_typed" "set_fromNumSet";
val _ = emit_exported "state_rel_def_typed" "state_rel_def";
val _ = emit_exported "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit_exported "state_rel_intro_typed" "state_rel_intro";
val _ = emit_exported "state_rel_with_clock_typed" "state_rel_with_clock";
val _ = capture "LASTN_ADD_CONS_typed" "LASTN_ADD_CONS";
val _ = capture "evaluate_tick_loop_tick_unfold_typed" "evaluate_tick_loop_tick_unfold";
val _ = capture "evaluate_tick_unfold_typed" "evaluate_tick_unfold";
val _ = capture "loop_to_word_compile_not_created_MEM_typed" "loop_to_word_compile_not_created_MEM";
val _ = capture "make_ctxt_APPEND_typed" "make_ctxt_APPEND";
val _ = capture "make_ctxt_NOT_MEM_typed" "make_ctxt_NOT_MEM";
val _ = capture "state_rel_IMP_typed" "state_rel_IMP";
val _ = capture "word_sh_SOME_MOD_dimword_typed" "word_sh_SOME_MOD_dimword";

(* Derived local theorems: the base statement is captured typed under
   the derived theorem name; the derivation is named in each comment,
   so the carriers are the base statement carriers. *)
(* acc_vars_acc': SWAP_FORALL_CONV then SPEC on q; the base statement carries the carriers *)
val _ = emit_as "acc_vars_acc_prime_typed" (fetch_other ("loopProps","acc_vars_acc"));
