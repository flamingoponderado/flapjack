load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_eval label tm =
  (print label; Lib.with_flag (Globals.show_types,true) print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "source_deref_typed=" ``semanticPrimitives$do_app
  ([Refv (Litv (IntLit 7))],ffi) Opderef [Loc F 0]``;
val _ = show_eval "flat_deref_typed=" ``flatSem$do_app
  (st with refs := [Refv (flatSem$Litv (IntLit 0)); Refv (flatSem$Litv (IntLit 7))])
  (El 0) [flatSem$Loc F 1]``;
val _ = show_eval "source_bad_typed=" ``semanticPrimitives$do_app
  ([W8array []],ffi) Opderef [Loc F 0]``;
val _ = show_eval "flat_bad_typed=" ``flatSem$do_app
  (st with refs := [Refv (flatSem$Litv (IntLit 0)); W8array []]) (El 0) [flatSem$Loc F 1]``;
