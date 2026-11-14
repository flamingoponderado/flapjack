load "preamble";
load "stack_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open stack_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;


fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="stack_allocProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/stack_allocProofScript.sml";

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


val _ = capture "EL_LENGTH_ADD_LEMMA_typed" "EL_LENGTH_ADD_LEMMA";
val _ = capture "LUPDATE_LENGTH_ADD_LEMMA_typed" "LUPDATE_LENGTH_ADD_LEMMA";
val _ = capture "MAX_SIMP_typed" "MAX_SIMP";
val _ = capture "SUBMAP_DOMSUB_both_typed" "SUBMAP_DOMSUB_both";
val _ = capture "SUBMAP_FUPDATE_both_typed" "SUBMAP_FUPDATE_both";
val _ = capture "alloc_correct_typed" "alloc_correct";
val _ = capture "enc_dec_stack_typed" "enc_dec_stack";
val _ = capture "evaluate_SetNewTrigger_typed" "evaluate_SetNewTrigger";
val _ = capture "filter_bitmap_APPEND_typed" "filter_bitmap_APPEND";
val _ = capture "filter_bitmap_map_bitmap_IMP_typed" "filter_bitmap_map_bitmap_IMP";
val _ = capture "find_code_IMP_lookup_typed" "find_code_IMP_lookup";
val _ = capture "gc_thm_typed" "gc_thm";
val _ = capture "get_bits_intro_typed" "get_bits_intro";
val _ = capture "get_var_imm_case_typed" "get_var_imm_case";
val _ = capture "isWord_thm_typed" "isWord_thm";
val _ = capture "is_fwd_ptr_iff_typed" "is_fwd_ptr_iff";
val _ = capture "lookup_IMP_lookup_compile_typed" "lookup_IMP_lookup_compile";
val _ = capture "lower_2w_eq_typed" "lower_2w_eq";
val _ = capture "lt_dimindex_MOD_dimword_typed" "lt_dimindex_MOD_dimword";
val _ = capture "map_bitmap_APPEND_typed" "map_bitmap_APPEND";
val _ = capture "prog_comp_lemma_typed" "prog_comp_lemma";
val _ = capture "split_num_forall_to_10_typed" "split_num_forall_to_10";
val _ = capture "with_same_regs_lemma_typed" "with_same_regs_lemma";
val _ = capture "word_gc_fun_thm_typed" "word_gc_fun_thm";
val _ = capture "word_gc_move_bitmap_unroll_typed" "word_gc_move_bitmap_unroll";
val _ = capture "word_gc_move_bitmaps_unroll_typed" "word_gc_move_bitmaps_unroll";
val _ = capture "word_gc_move_loop_code_thm_typed" "word_gc_move_loop_code_thm";
val _ = capture "word_gc_move_roots_APPEND_typed" "word_gc_move_roots_APPEND";
val _ = capture "word_gc_move_roots_bitmaps_typed" "word_gc_move_roots_bitmaps";
val _ = capture "word_gen_gc_move_bitmap_unroll_typed" "word_gen_gc_move_bitmap_unroll";
val _ = capture "word_gen_gc_move_bitmaps_unroll_typed" "word_gen_gc_move_bitmaps_unroll";
val _ = capture "word_gen_gc_move_data_code_thm_typed" "word_gen_gc_move_data_code_thm";
val _ = capture "word_gen_gc_move_loop_code_thm_typed" "word_gen_gc_move_loop_code_thm";
val _ = capture "word_gen_gc_move_refs_code_thm_typed" "word_gen_gc_move_refs_code_thm";
val _ = capture "word_gen_gc_move_roots_APPEND_typed" "word_gen_gc_move_roots_APPEND";
val _ = capture "word_gen_gc_move_roots_bitmaps_typed" "word_gen_gc_move_roots_bitmaps";
val _ = capture "word_gen_gc_partial_move_bitmap_unroll_typed" "word_gen_gc_partial_move_bitmap_unroll";
val _ = capture "word_gen_gc_partial_move_bitmaps_unroll_typed" "word_gen_gc_partial_move_bitmaps_unroll";
val _ = capture "word_gen_gc_partial_move_data_code_thm_typed" "word_gen_gc_partial_move_data_code_thm";
val _ = capture "word_gen_gc_partial_move_ref_list_code_thm_typed" "word_gen_gc_partial_move_ref_list_code_thm";
val _ = capture "word_gen_gc_partial_move_ref_list_ok_typed" "word_gen_gc_partial_move_ref_list_ok";
val _ = capture "word_gen_gc_partial_move_roots_APPEND_typed" "word_gen_gc_partial_move_roots_APPEND";
val _ = capture "word_gen_gc_partial_move_roots_bitmaps_typed" "word_gen_gc_partial_move_roots_bitmaps";
val _ = capture "word_lsr_dimindex_typed" "word_lsr_dimindex";
val _ = capture "word_msb_IMP_bit_length_typed" "word_msb_IMP_bit_length";
val _ = capture "word_sub_0_eq_typed" "word_sub_0_eq";
