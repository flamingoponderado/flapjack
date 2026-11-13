(* Typed HOL stringTheory statements at the pinned HOL revision: isLower_def,
   isUpper_def, isAlpha_def and char_size_def, printed with show_types. *)
load "bossLib";
load "stringTheory";
open HolKernel Parse boolLib bossLib stringTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "islower_def_typed" stringTheory.isLower_def;
val _ = show_thm "isupper_def_typed" stringTheory.isUpper_def;
val _ = show_thm "isalpha_def_typed" stringTheory.isAlpha_def;
val _ = show_thm "char_size_def_typed" stringTheory.char_size_def;
