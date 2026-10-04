(* Typed source parse of the [local] wordConvsProof copy_prop lemmas that the
   CopyProp rows port (wordConvsProofScript.sml:1873-2176). Locals are not
   exported, so each statement is read literally from the pinned source text
   (between its `Theorem name[...]:` header and `Proof`) and parsed in the
   context of the loaded original wordConvsProofTheory and its ancestors, then
   printed with show_types. This captures the inferred carriers of the source
   statement; it does not re-prove it. *)
load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse boolLib bossLib preamble
  wordLangTheory word_to_wordTheory wordConvsTheory word_simpTheory word_allocTheory
  word_instTheory word_unreachTheory word_removeTheory word_cseTheory word_elimTheory
  word_copyTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "compiler/backend/proofs/wordConvsProofScript.sml"));
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
val _ = capture "copy_prop_not_created_subprogs_source_statement_typed" "copy_prop_not_created_subprogs";
val _ = capture "copy_prop_prog_not_alloc_var_source_statement_typed" "copy_prop_prog_not_alloc_var";
val _ = capture "copy_prop_prog_not_alloc_var_aux1_source_statement_typed" "copy_prop_prog_not_alloc_var_aux1";
val _ = capture "copy_prop_prog_not_alloc_var_aux2_source_statement_typed" "copy_prop_prog_not_alloc_var_aux2";
val _ = capture "every_inst_distinct_tar_reg_copy_prop_aux_source_statement_typed" "every_inst_distinct_tar_reg_copy_prop_aux";
val _ = capture "extract_labels_copy_prop_aux_source_statement_typed" "extract_labels_copy_prop_aux";
val _ = capture "flat_exp_conventions_copy_prop_aux_source_statement_typed" "flat_exp_conventions_copy_prop_aux";
val _ = capture "full_inst_ok_less_copy_prop_aux_source_statement_typed" "full_inst_ok_less_copy_prop_aux";
val _ = capture "pre_alloc_conventions_copy_prop_aux_source_statement_typed" "pre_alloc_conventions_copy_prop_aux";
val _ = capture "wf_cutsets_copy_prop_aux_source_statement_typed" "wf_cutsets_copy_prop_aux";
val _ = capture "word_get_code_labels_copy_prop_source_statement_typed" "word_get_code_labels_copy_prop";
val _ = capture "word_good_handlers_copy_prop_source_statement_typed" "word_good_handlers_copy_prop";
