(* Typed captures for the pan_to_targetProof reviewed rows (task 171).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   56 names: 48 exported (fetched from the theory DB), 8 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 0 derived, 0 datatypes.
*)
load "preamble";
load "pan_to_targetProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pan_to_targetProofTheory;
open pan_to_targetTheory pan_to_wordProofTheory wordConvsProofTheory;
open stack_to_labProofTheory lab_to_targetProofTheory backendProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pan_to_targetProof",Name=name} of
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

val source_text = source_text_of "pancake/proofs/pan_to_targetProofScript.sml";

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

(* A `^` immediately followed by an identifier is an SML antiquotation of
   a term variable; the capture drops the marker and keeps the variable.
   An infix `^` (mlstring concatenation) is followed by a space and is
   kept. *)
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

val _ = emit_exported "option_lt_def_typed" "option_lt_def";
val _ = emit_exported "compile_prog_max_def_typed" "compile_prog_max_def";
val _ = emit_exported "const_writes_const_memory_typed" "const_writes_const_memory";
val _ = emit_exported "fun2set_update_eq_typed" "fun2set_update_eq";
val _ = emit_exported "get_var_const_memory_typed" "get_var_const_memory";
val _ = emit_exported "get_var_imm_const_memory_typed" "get_var_imm_const_memory";
val _ = emit_exported "get_vars_const_memory_typed" "get_vars_const_memory";
val _ = emit_exported "inst_const_memory_typed" "inst_const_memory";
val _ = emit_exported "mem_load_32_const_memory_typed" "mem_load_32_const_memory";
val _ = emit_exported "mem_load_byte_aux_const_memory_typed" "mem_load_byte_aux_const_memory";
val _ = emit_exported "mem_load_const_memory_typed" "mem_load_const_memory";
val _ = emit_exported "mem_store_32_const_memory_typed" "mem_store_32_const_memory";
val _ = emit_exported "mem_store_byte_aux_const_memory_typed" "mem_store_byte_aux_const_memory";
val _ = emit_exported "mem_store_const_memory_typed" "mem_store_const_memory";
val _ = emit_exported "read_bytearray_const_memory_typed" "read_bytearray_const_memory";
val _ = emit_exported "set_var_const_memory_typed" "set_var_const_memory";
val _ = emit_exported "set_vars_const_memory_typed" "set_vars_const_memory";
val _ = emit_exported "share_inst_const_memory_typed" "share_inst_const_memory";
val _ = emit_exported "unset_var_const_memory_typed" "unset_var_const_memory";
val _ = emit_exported "word_exp_const_memory_typed" "word_exp_const_memory";
val _ = emit_exported "write_bytearray_const_memory_typed" "write_bytearray_const_memory";
val _ = emit_exported "FLOOKUP_MAP_KEYS_LINV_typed" "FLOOKUP_MAP_KEYS_LINV";
val _ = emit_exported "InitGlobals_location_eq_first_name_typed" "InitGlobals_location_eq_first_name";
val _ = emit_exported "full_make_init_be_typed" "full_make_init_be";
val _ = emit_exported "good_dimindex_0w_8w_typed" "good_dimindex_0w_8w";
val _ = emit_exported "good_dimindex_div_mul_typed" "good_dimindex_div_mul";
val _ = emit_exported "word_list_exists_addresses_typed" "word_list_exists_addresses";
val _ = emit_exported "word_to_stack_compile_FST_typed" "word_to_stack_compile_FST";
val _ = emit_exported "word_semantics_memory_update_typed" "word_semantics_memory_update";
val _ = emit_exported "evaluate_stack_size_limit_const_panLang_typed" "evaluate_stack_size_limit_const_panLang";
val _ = emit_exported "inst_stack_limit_const_panLang_typed" "inst_stack_limit_const_panLang";
val _ = emit_exported "inst_stack_max_const_panLang_typed" "inst_stack_max_const_panLang";
val _ = emit_exported "inst_stack_size_const_panLang_typed" "inst_stack_size_const_panLang";
val _ = emit_exported "no_alloc_word_evaluate_typed" "no_alloc_word_evaluate";
val _ = emit_exported "option_lt_SOME_typed" "option_lt_SOME";
val _ = emit_exported "panLang_wordSem_neq_NotEnoughSpace_typed" "panLang_wordSem_neq_NotEnoughSpace";
val _ = emit_exported "share_inst_modifies_typed" "share_inst_modifies";
val _ = emit_exported "word_to_word_compile_no_install_no_alloc_typed" "word_to_word_compile_no_install_no_alloc";
val _ = emit_exported "pan_installed_def_typed" "pan_installed_def";
val _ = emit_exported "pan_installed_imp_installed_typed" "pan_installed_imp_installed";
val _ = emit_exported "pan_to_stack_first_ALL_DISTINCT_typed" "pan_to_stack_first_ALL_DISTINCT";
val _ = emit_exported "pan_to_stack_compile_lab_pres_typed" "pan_to_stack_compile_lab_pres";
val _ = emit_exported "pan_to_lab_labels_ok_typed" "pan_to_lab_labels_ok";
val _ = emit_exported "word_to_stack_good_code_lemma_typed" "word_to_stack_good_code_lemma";
val _ = emit_exported "from_pan_to_lab_no_install_typed" "from_pan_to_lab_no_install";
val _ = emit_exported "pan_to_lab_good_code_lemma_typed" "pan_to_lab_good_code_lemma";
val _ = emit_exported "pancake_good_code_def_typed" "pancake_good_code_def";
val _ = emit_exported "pan_to_target_compile_semantics_typed" "pan_to_target_compile_semantics";
val _ = capture "cut_state_with_mem_const_typed" "cut_state_with_mem_const";
val _ = capture "mem_upd_lemma_typed" "mem_upd_lemma";
val _ = capture "push_env_mem_const_typed" "push_env_mem_const";
val _ = capture "push_env_mem_upd_typed" "push_env_mem_upd";
val _ = capture "aligned_n2w_IMP_typed" "aligned_n2w_IMP";
val _ = capture "n2w_sub_alt_typed" "n2w_sub_alt";
val _ = capture "memory_swap_lemma_typed" "memory_swap_lemma";
val _ = capture "memory_swap_lemma1_typed" "memory_swap_lemma1";
