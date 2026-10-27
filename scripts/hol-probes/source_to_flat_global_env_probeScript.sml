load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
val _ = show_type "globals_type=" ``λ(s:source_to_flatProof$global_env). s.v``;
val _ = show_type "constructors_type=" ``λ(s:source_to_flatProof$global_env). s.c``;
val _ = show_type "types_type=" ``λ(s:source_to_flatProof$global_env). s.tys``;
