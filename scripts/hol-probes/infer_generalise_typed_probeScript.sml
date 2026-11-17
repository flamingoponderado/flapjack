(* Typed HOL source for the mutual inference generalization definition. *)
load "preamble";
load "inferTheory";
open HolKernel Parse boolLib bossLib;
open preamble inferTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

val _ = (print "generalise_type=";
  print (type_to_string (type_of ``infer$generalise``)); print "\n");
val _ = (print "generalise_list_type=";
  print (type_to_string (type_of ``infer$generalise_list``)); print "\n");
val _ = (print "generalise_def_typed=";
  print_term (concl (DB.fetch "infer" "generalise_def")); print "\n");
