(* Typed captures for the tagged wordConvs declarations whose statements changed
   in task 155 (the applied instruction predicate moved from the retired
   width-general spelling to the reviewed exact port through
   HolInst.ofWordLangInst).  Exported theorems are printed with show_types from
   the loaded theories; the [local] word_alloc_two_reg_inst_lem is read literally
   from the pinned source and parsed with show_types in the loaded
   wordConvsProofTheory context (a typed source parse, not re-proved). *)
load "preamble"; load "wordConvsProofTheory"; load "word_to_wordProofTheory";
open HolKernel Parse boolLib bossLib preamble wordConvsTheory wordConvsProofTheory
  word_to_wordTheory word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");

fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then NONE
                 else SOME (Substring.string (Substring.triml (String.size pre) rest));

fun statement_of rel name =
  let
    val text = TextIO.inputAll (TextIO.openIn (OS.Path.concat (source_cake, rel)))
    fun first [] = raise Fail ("missing " ^ name)
      | first (h :: t) = (case after_prefix h text of SOME r => r | NONE => first t)
    val rest = first ["\nTheorem " ^ name ^ "[", "\nTheorem  " ^ name ^ "[",
                      "\nTriviality " ^ name, "\nTriviality  " ^ name]
    val body = case after_prefix ":\n" rest of SOME b => b | NONE => raise Fail ("no statement " ^ name)
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;

fun capture label rel name =
  let val tm = Parse.Term [QUOTE (statement_of rel name)]
  in (print (label ^ "="); print_term tm; print "\n") end;

fun capture_thm label th = (print (label ^ "="); print_term (concl th); print "\n");

val _ = capture_thm "three_to_two_reg_prog_two_reg_inst_typed"
  three_to_two_reg_prog_two_reg_inst;
val _ = capture_thm "word_alloc_two_reg_inst_typed" word_alloc_two_reg_inst;
val _ = capture "word_alloc_two_reg_inst_lem_typed"
  "compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_two_reg_inst_lem";
val _ = capture_thm "compile_to_word_conventions_typed" compile_to_word_conventions;

val _ = OS.Process.exit OS.Process.success;
