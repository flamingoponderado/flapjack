(* Typed captures for the pan_to_wordProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   88 names: 82 exported (fetched from the theory DB), 5 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 1 derived local theorems captured through
   their base statement, 0 datatypes.
*)
load "preamble";
load "pan_to_wordProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pan_to_wordProofTheory;
open crep_inlineTheory pan_to_wordTheory pan_simpProofTheory pan_to_crepProofTheory crep_to_loopProofTheory loop_to_wordProofTheory pan_globalsProofTheory pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pan_to_wordProof",Name=name} of
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
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_wordProofScript.sml"));
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

val _ = emit_exported "FDOM_get_eids_pan_globals_compile_eq_typed" "FDOM_get_eids_pan_globals_compile_eq";
val _ = emit_exported "FLOOKUP_make_funcs_main_typed" "FLOOKUP_make_funcs_main";
val _ = emit_exported "compile_decs_exp_ids_typed" "compile_decs_exp_ids";
val _ = emit_exported "compile_decs_no_exp_ids_main_typed" "compile_decs_no_exp_ids_main";
val _ = emit_exported "compile_shape_no_name_typed" "compile_shape_no_name";
val _ = emit_exported "crep_state_def_typed" "crep_state_def";
val _ = emit_exported "dec_shapes_compile_prog_typed" "dec_shapes_compile_prog";
val _ = emit_exported "distinct_params_def_typed" "distinct_params_def";
val _ = emit_exported "every_inst_ok_arith_simp_exp_typed" "every_inst_ok_arith_simp_exp";
val _ = emit_exported "every_inst_ok_arith_simp_prog_typed" "every_inst_ok_arith_simp_prog";
val _ = emit_exported "every_inst_ok_less_comp_func_typed" "every_inst_ok_less_comp_func";
val _ = emit_exported "every_inst_ok_less_crep_to_loop_compile_typed" "every_inst_ok_less_crep_to_loop_compile";
val _ = emit_exported "every_inst_ok_less_crep_to_loop_compile_exp_typed" "every_inst_ok_less_crep_to_loop_compile_exp";
val _ = emit_exported "every_inst_ok_less_crep_to_loop_compile_prog_typed" "every_inst_ok_less_crep_to_loop_compile_prog";
val _ = emit_exported "every_inst_ok_less_fperm_typed" "every_inst_ok_less_fperm";
val _ = emit_exported "every_inst_ok_less_fperm_decs_typed" "every_inst_ok_less_fperm_decs";
val _ = emit_exported "every_inst_ok_less_optimise_typed" "every_inst_ok_less_optimise";
val _ = emit_exported "every_inst_ok_less_pan_globals_compile_typed" "every_inst_ok_less_pan_globals_compile";
val _ = emit_exported "every_inst_ok_less_pan_globals_compile_decs_typed" "every_inst_ok_less_pan_globals_compile_decs";
val _ = emit_exported "every_inst_ok_less_pan_globals_compile_decs_init_typed" "every_inst_ok_less_pan_globals_compile_decs_init";
val _ = emit_exported "every_inst_ok_less_pan_globals_compile_exp_typed" "every_inst_ok_less_pan_globals_compile_exp";
val _ = emit_exported "every_inst_ok_less_pan_globals_compile_top_typed" "every_inst_ok_less_pan_globals_compile_top";
val _ = emit_exported "every_inst_ok_less_pan_simp_compile_typed" "every_inst_ok_less_pan_simp_compile";
val _ = emit_exported "every_inst_ok_less_pan_simp_compile_prog_typed" "every_inst_ok_less_pan_simp_compile_prog";
val _ = emit_exported "every_inst_ok_less_pan_structs_compile_typed" "every_inst_ok_less_pan_structs_compile";
val _ = emit_exported "every_inst_ok_less_pan_structs_compile_decs_typed" "every_inst_ok_less_pan_structs_compile_decs";
val _ = emit_exported "every_inst_ok_less_pan_structs_compile_exp_typed" "every_inst_ok_less_pan_structs_compile_exp";
val _ = emit_exported "every_inst_ok_less_pan_structs_compile_top_typed" "every_inst_ok_less_pan_structs_compile_top";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_cexp_heads_typed" "every_inst_ok_less_pan_to_crep_cexp_heads";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_comp_field_typed" "every_inst_ok_less_pan_to_crep_comp_field";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_compile_typed" "every_inst_ok_less_pan_to_crep_compile";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_compile_exp_typed" "every_inst_ok_less_pan_to_crep_compile_exp";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_compile_prog_typed" "every_inst_ok_less_pan_to_crep_compile_prog";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_compile_to_crep_typed" "every_inst_ok_less_pan_to_crep_compile_to_crep";
val _ = emit_exported "every_inst_ok_less_pan_to_crep_load_shape_typed" "every_inst_ok_less_pan_to_crep_load_shape";
val _ = emit_exported "every_inst_ok_less_ret_to_tail_typed" "every_inst_ok_less_ret_to_tail";
val _ = emit_exported "every_inst_ok_less_seq_assoc_typed" "every_inst_ok_less_seq_assoc";
val _ = emit_exported "every_inst_ok_less_shape_val_typed" "every_inst_ok_less_shape_val";
val _ = emit_exported "every_inst_ok_less_store_globals_typed" "every_inst_ok_less_store_globals";
val _ = emit_exported "every_inst_ok_less_stores_typed" "every_inst_ok_less_stores";
val _ = emit_exported "every_inst_ok_loop_call_typed" "every_inst_ok_loop_call";
val _ = emit_exported "every_inst_ok_loop_live_typed" "every_inst_ok_loop_live";
val _ = emit_exported "every_inst_ok_nested_decs_typed" "every_inst_ok_nested_decs";
val _ = emit_exported "every_inst_w_inline_typed" "every_inst_w_inline";
val _ = emit_exported "every_prog_loop_inst_ok_nested_seq_typed" "every_prog_loop_inst_ok_nested_seq";
val _ = emit_exported "exp_ids_compile_globals_typed" "exp_ids_compile_globals";
val _ = emit_exported "exp_ids_fperm_typed" "exp_ids_fperm";
val _ = emit_exported "exp_ids_nested_seq_typed" "exp_ids_nested_seq";
val _ = emit_exported "exps_of_nested_seq_typed" "exps_of_nested_seq";
val _ = emit_exported "first_compile_prog_all_distinct_typed" "first_compile_prog_all_distinct";
val _ = emit_exported "fperm_exp_ids_typed" "fperm_exp_ids";
val _ = emit_exported "function_names_compile_prog_typed" "function_names_compile_prog";
val _ = emit_exported "function_names_structs_compile_top_typed" "function_names_structs_compile_top";
val _ = emit_exported "functions_FILTER_nil_typed" "functions_FILTER_nil";
val _ = emit_exported "functions_compile_decs_exns_typed" "functions_compile_decs_exns";
val _ = emit_exported "functions_resort_decls_typed" "functions_resort_decls";
val _ = emit_exported "get_eids_pan_simp_compile_eq_typed" "get_eids_pan_simp_compile_eq";
val _ = emit_exported "globals_allocatable_def_typed" "globals_allocatable_def";
val _ = emit_exported "good_panops_def_typed" "good_panops_def";
val _ = emit_exported "load_globals_alt_typed" "load_globals_alt";
val _ = emit_exported "lookup_first_name_compile_prog_main_typed" "lookup_first_name_compile_prog_main";
val _ = emit_exported "loop_state_def_typed" "loop_state_def";
val _ = emit_exported "loop_state_simps_typed" "loop_state_simps";
val _ = emit_exported "map_map2_fst_lemma_typed" "map_map2_fst_lemma";
val _ = emit_exported "no_labels_def_typed" "no_labels_def";
val _ = emit_exported "no_names_compile_prog_typed" "no_names_compile_prog";
val _ = emit_exported "pan_exps_of_nested_seq_typed" "pan_exps_of_nested_seq";
val _ = emit_exported "pan_to_word_compile_lab_pres_typed" "pan_to_word_compile_lab_pres";
val _ = emit_exported "pan_to_word_compile_prog_lab_min_typed" "pan_to_word_compile_prog_lab_min";
val _ = emit_exported "pan_to_word_compile_prog_no_alloc_code_typed" "pan_to_word_compile_prog_no_alloc_code";
val _ = emit_exported "pan_to_word_compile_prog_no_install_code_typed" "pan_to_word_compile_prog_no_install_code";
val _ = emit_exported "pan_to_word_compile_prog_no_mt_code_typed" "pan_to_word_compile_prog_no_mt_code";
val _ = emit_exported "pan_to_word_every_inst_ok_less_typed" "pan_to_word_every_inst_ok_less";
val _ = emit_exported "pan_to_word_good_handlers_typed" "pan_to_word_good_handlers";
val _ = emit_exported "semantics_decls_decl_structs_typed" "semantics_decls_decl_structs";
val _ = emit_exported "semantics_decls_has_main_prime_typed" "semantics_decls_has_main'";
val _ = emit_exported "semantics_size_decs_stcnames_compile_structs_typed" "semantics_size_decs_stcnames_compile_structs";
val _ = emit_exported "size_decs_stcnames_compile_decs_structs_typed" "size_decs_stcnames_compile_decs_structs";
val _ = emit_exported "size_of_eids_compile_top_typed" "size_of_eids_compile_top";
val _ = emit_exported "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit_exported "wloc_wlab_def_typed" "wloc_wlab_def";
val _ = emit_exported "wloc_wlab_wlab_wloc_typed" "wloc_wlab_wlab_wloc";
val _ = capture "FDOM_get_eids_structs_compile_decs_eq_typed" "FDOM_get_eids_structs_compile_decs_eq";
val _ = capture "FDOM_get_eids_structs_compile_eq_typed" "FDOM_get_eids_structs_compile_eq";
val _ = capture "exp_ids_structs_compile_typed" "exp_ids_structs_compile";
val _ = capture "function_names_structs_compile_decs_typed" "function_names_structs_compile_decs";
val _ = capture "size_of_eids_structs_compile_eq_typed" "size_of_eids_structs_compile_eq";

(* Derived local theorems: the base statement is captured typed under
   the derived theorem name; the derivation is named in each comment,
   so the carriers are the base statement carriers. *)
(* ALL_DISTINCT_MAP_INJ_o: ONCE_REWRITE_RULE on ALL_DISTINCT_MAP_INJ *)
val _ = emit_as "ALL_DISTINCT_MAP_INJ_o_typed" (fetch_other ("list","ALL_DISTINCT_MAP_INJ"));
