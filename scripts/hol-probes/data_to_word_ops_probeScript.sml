(* Typed source declarations for the word-op classification and stub names in
   cakeml/compiler/backend/data_to_wordScript.sml. *)
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "word_op_type_axiom_typed" data_to_wordTheory.word_op_type_Axiom;
val _ = show "lookup_word_op_def_typed" data_to_wordTheory.lookup_word_op_def;
val _ = show "stub_names_def_typed" data_to_wordTheory.stub_names_def;
