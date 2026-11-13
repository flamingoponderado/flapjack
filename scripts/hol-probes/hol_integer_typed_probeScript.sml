(* Typed HOL integerTheory int_div and int_mod constants at the pinned HOL
   revision, captured by type_of. *)
load "bossLib";
load "integerTheory";
open HolKernel Parse boolLib bossLib integerTheory;
val _ = Globals.linewidth := 1000;
fun show_type label c =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_type (type_of c);
   print "\n");
val _ = show_type "int_div_type" ``integer$int_div``;
val _ = show_type "int_mod_type" ``integer$int_mod``;
