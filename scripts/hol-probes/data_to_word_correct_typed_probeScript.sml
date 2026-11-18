(* The exported original simulation theorem, including all inferred types. *)
load "data_to_wordProofTheory";
open HolKernel Parse bossLib data_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "data_compile_correct_hypotheses=";
  print (Int.toString (length (hyp data_compile_correct))); print "\n");
val _ = (print "data_compile_correct_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl data_compile_correct);
  print "\n");
