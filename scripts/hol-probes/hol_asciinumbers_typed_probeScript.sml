(* Typed HOL ASCIInumbersTheory statements at the pinned HOL revision: HEX,
   n2s_def and num_to_dec_string_def, printed with show_types. *)
load "bossLib";
load "ASCIInumbersTheory";
open HolKernel Parse boolLib bossLib ASCIInumbersTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "hex_typed" ASCIInumbersTheory.HEX;
val _ = show_thm "n2s_def_typed" ASCIInumbersTheory.n2s_def;
val _ = show_thm "num_to_dec_string_def_typed" ASCIInumbersTheory.num_to_dec_string_def;
