load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_eval label tm =
  (print label; Lib.with_flag (Globals.show_types,true) print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "source_opref_typed=" ``semanticPrimitives$do_app ([],ffi) Opref [Litv (IntLit 7)]``;
val _ = show_eval "flat_opref_typed=" ``flatSem$do_app
  (st with refs := [Refv (flatSem$Litv (IntLit 0))]) (Src Opref) [flatSem$Litv (IntLit 7)]``;
