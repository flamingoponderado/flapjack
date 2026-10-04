(* Typed captures for the PR1213 word_to_word local rows
   (word_to_wordProofScript.sml). [local] theorems are not exported: the five
   statement-form locals are read literally from the pinned source (between the
   `Theorem name[...]:` header and `Proof`) and parsed with show_types in the
   loaded word_to_wordProofTheory context (a typed source parse, not re-proved).
   code_rel_no_alloc/code_rel_no_install are `Theorem x[local] = <ML>` aliases:
   their literal ML derivations (guarded against the source text) are replayed on
   the exported code_rel_not_created_subprogs and the resulting conclusions are
   printed with show_types. cond16bit_inst_select_exp' is exported and printed
   directly. *)
load "preamble"; load "word_to_wordProofTheory";
open HolKernel Parse boolLib bossLib preamble wordLangTheory wordConvsTheory
  word_to_wordTheory word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
fun read_source rel =
  let val st = TextIO.openIn (OS.Path.concat (source_cake, rel))
      val tx = TextIO.inputAll st
  in (TextIO.closeIn st; tx) end;
fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);
fun statement_of source header =
  let
    val rest = after_prefix header source
    val body = after_prefix ":\n" rest
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;
fun guard source name lit = if String.isSubstring lit source then ()
  else raise Fail (name ^ " literal source changed");
val src = read_source "compiler/backend/proofs/word_to_wordProofScript.sml";
fun capture label name =
  let val tm = Parse.Term [QUOTE (statement_of src ("\nTheorem " ^ name ^ "["))]
  in (print (label ^ "="); print_term tm; print "\n") end;
fun capture_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = capture "rm_perm_source_statement_typed" "rm_perm";
val _ = capture "find_code_thm_source_statement_typed" "find_code_thm";
val _ = capture "pop_env_termdep_source_statement_typed" "pop_env_termdep";
val _ = capture "compile_single_eta_source_statement_typed" "compile_single_eta";
val _ = capture "code_rel_union_fromAList_source_statement_typed" "code_rel_union_fromAList";
val _ = guard src "code_rel_P" "Theorem code_rel_P[local] = Q.GEN `P` code_rel_not_created_subprogs;";
val code_rel_P = Q.GEN `P` code_rel_not_created_subprogs;
val _ = guard src "code_rel_no_alloc" "Theorem code_rel_no_alloc[local] = code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))`\n    |> REWRITE_RULE [GSYM no_alloc_subprogs_def]";
val _ = capture_thm "code_rel_no_alloc_replay_statement_typed"
  (code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))` |> REWRITE_RULE [GSYM no_alloc_subprogs_def]);
val _ = guard src "code_rel_no_install" "Theorem code_rel_no_install[local] = code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))`\n    |> REWRITE_RULE [GSYM no_install_subprogs_def]";
val _ = capture_thm "code_rel_no_install_replay_statement_typed"
  (code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))` |> REWRITE_RULE [GSYM no_install_subprogs_def]);
val _ = capture_thm "cond16bit_inst_select_exp_prime_statement" cond16bit_inst_select_exp';
