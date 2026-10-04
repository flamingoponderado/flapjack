(* Typed source parse of the [local] word_cseProof lemmas that the word_cse
   MoveLemmas rows port (word_cseProofScript.sml:1953-2251). Locals are not
   exported, so each statement is read literally from the pinned source text
   (between its `Theorem name[...]:` header and `Proof`) and parsed in the
   context of the loaded original word_cseProofTheory and its ancestors, then
   printed with show_types. This captures the inferred carriers of the source
   statement; it does not re-prove it. *)
load "preamble"; load "word_cseProofTheory";
open HolKernel Parse boolLib bossLib preamble
  wordLangTheory wordSemTheory wordPropsTheory word_cseTheory alistTheory
  totoTheory reg_allocTheory word_simpTheory wordConvsTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "compiler/backend/proofs/word_cseProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);
fun statement_of name =
  let
    val rest = after_prefix ("\nTheorem " ^ name ^ "[") source_text
    val body = after_prefix ":\n" rest
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;
fun capture label name =
  let val tm = Parse.Term [QUOTE (statement_of name)]
  in (print (label ^ "="); print_term tm; print "\n") end;
val _ = capture "MAP_FST_lemma_source_statement_typed" "MAP_FST_lemma";
val _ = capture "MAP_SND_lemma_source_statement_typed" "MAP_SND_lemma";
val _ = capture "get_set_vars_not_in_source_statement_typed" "get_set_vars_not_in";
val _ = capture "get_set_vars_in_source_statement_typed" "get_set_vars_in";
val _ = capture "get_set_vars_in_2_source_statement_typed" "get_set_vars_in_2";
val _ = capture "lookup_set_vars_not_in_source_statement_typed" "lookup_set_vars_not_in";
val _ = capture "list_insert_insert_source_statement_typed" "list_insert_insert";
val _ = capture "data_inv_insert_canonical_pair_source_statement_typed" "data_inv_insert_canonical_pair";
val _ = capture "data_inv_insert_pair_source_statement_typed" "data_inv_insert_pair";
val _ = capture "data_inv_move_pairs_source_statement_typed" "data_inv_move_pairs";
val _ = capture "if_eq_rw_source_statement_typed" "if_eq_rw";
val _ = capture "evaluate_arith_clock_source_statement_typed" "evaluate_arith_clock";
val _ = capture "evaluate_load_clock_source_statement_typed" "evaluate_load_clock";
