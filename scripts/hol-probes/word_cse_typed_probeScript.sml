load "preamble";
load "word_cseProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;


fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="word_cseProof",Name=name} of
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

val source_text = source_text_of "compiler/backend/proofs/word_cseProofScript.sml";

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
  in (print (label ^ "="); print_without_macros tm; print "\n") end;

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


val _ = capture "ALL_DISTINCT_MAP_FST_FILTER_typed" "ALL_DISTINCT_MAP_FST_FILTER";
val _ = capture "MAP_FST_lemma_typed" "MAP_FST_lemma";
val _ = capture "MAP_SND_lemma_typed" "MAP_SND_lemma";
val _ = capture "can_mem_arith_ODD_reads_typed" "can_mem_arith_ODD_reads";
val _ = capture "canonicalArith_reads_self_or_fresh_typed" "canonicalArith_reads_self_or_fresh";
val _ = capture "canonicalRegs_prime_self_or_fresh_typed" "canonicalRegs'_self_or_fresh";
val _ = capture "canonicalRegs_prime_self_or_fresh_wf_typed" "canonicalRegs'_self_or_fresh_wf";
val _ = capture "canonicalRegs_self_or_fresh_typed" "canonicalRegs_self_or_fresh";
val _ = capture "canonicalRegs_self_or_fresh_wf_typed" "canonicalRegs_self_or_fresh_wf";
val _ = capture "data_inv_alist_insert_locals_typed" "data_inv_alist_insert_locals";
val _ = capture "data_inv_cons_gets_typed" "data_inv_cons_gets";
val _ = capture "data_inv_filter_gets_typed" "data_inv_filter_gets";
val _ = capture "data_inv_insert_canonical_pair_typed" "data_inv_insert_canonical_pair";
val _ = capture "data_inv_insert_gets_typed" "data_inv_insert_gets";
val _ = capture "data_inv_insert_instrs_Arith_typed" "data_inv_insert_instrs_Arith";
val _ = capture "data_inv_insert_instrs_Const_typed" "data_inv_insert_instrs_Const";
val _ = capture "data_inv_insert_instrs_LocValue_typed" "data_inv_insert_instrs_LocValue";
val _ = capture "data_inv_insert_instrs_OpCurrHeap_typed" "data_inv_insert_instrs_OpCurrHeap";
val _ = capture "data_inv_insert_loads_typed" "data_inv_insert_loads";
val _ = capture "data_inv_insert_pair_typed" "data_inv_insert_pair";
val _ = capture "data_inv_invalidate_regs_typed" "data_inv_invalidate_regs";
val _ = capture "data_inv_move_pairs_typed" "data_inv_move_pairs";
val _ = capture "data_inv_reinsert_canonical_typed" "data_inv_reinsert_canonical";
val _ = capture "evaluate_arith_agree_typed" "evaluate_arith_agree";
val _ = capture "evaluate_arith_clock_typed" "evaluate_arith_clock";
val _ = capture "evaluate_arith_memory_typed" "evaluate_arith_memory";
val _ = capture "evaluate_arith_unset_var_typed" "evaluate_arith_unset_var";
val _ = capture "evaluate_load_agree_typed" "evaluate_load_agree";
val _ = capture "evaluate_load_change_addr_typed" "evaluate_load_change_addr";
val _ = capture "evaluate_load_clock_typed" "evaluate_load_clock";
val _ = capture "evaluate_load_unset_var_typed" "evaluate_load_unset_var";
val _ = capture "get_set_vars_in_typed" "get_set_vars_in";
val _ = capture "get_set_vars_in_2_typed" "get_set_vars_in_2";
val _ = capture "get_set_vars_not_in_typed" "get_set_vars_not_in";
val _ = capture "if_eq_rw_typed" "if_eq_rw";
val _ = capture "in_names_set_insert_self_typed" "in_names_set_insert_self";
val _ = capture "in_names_set_register_reads_typed" "in_names_set_register_reads";
val _ = capture "lookup_invalidate_regs_typed" "lookup_invalidate_regs";
val _ = capture "lookup_invalidate_regs_mono_typed" "lookup_invalidate_regs_mono";
val _ = capture "lookup_set_vars_not_in_typed" "lookup_set_vars_not_in";
val _ = capture "wf_data_cons_gets_typed" "wf_data_cons_gets";
val _ = capture "wf_data_filter_gets_typed" "wf_data_filter_gets";
val _ = capture "wf_data_insert_gets_typed" "wf_data_insert_gets";
val _ = capture "wf_data_insert_instrs_Arith_typed" "wf_data_insert_instrs_Arith";
val _ = capture "wf_data_insert_instrs_Const_typed" "wf_data_insert_instrs_Const";
val _ = capture "wf_data_insert_instrs_LocValue_typed" "wf_data_insert_instrs_LocValue";
val _ = capture "wf_data_insert_instrs_OpCurrHeap_typed" "wf_data_insert_instrs_OpCurrHeap";
val _ = capture "wf_data_insert_loads_typed" "wf_data_insert_loads";
val _ = capture "wf_data_move_pairs_typed" "wf_data_move_pairs";
val _ = capture "wf_data_reinsert_canonical_typed" "wf_data_reinsert_canonical";
val _ = capture "with_locals_insert_typed" "with_locals_insert";
