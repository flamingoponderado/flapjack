load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_eval label tm =
  (print label; Lib.with_flag (Globals.show_types,true) print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "source_assign_typed=" ``semanticPrimitives$do_app
  ([Refv (Litv (IntLit 7))],ffi) Opassign [Loc F 0; Litv (IntLit 9)]``;
val _ = show_eval "flat_assign_typed=" ``flatSem$do_app
  (st with refs := [Refv (flatSem$Litv (IntLit 0)); Refv (flatSem$Litv (IntLit 7))])
  (Src Opassign) [flatSem$Loc F 1; flatSem$Litv (IntLit 9)]``;
val _ = show_eval "source_bad_typed=" ``semanticPrimitives$do_app
  ([W8array []],ffi) Opassign [Loc F 0; Litv (IntLit 9)]``;
val _ = show_eval "flat_bad_typed=" ``flatSem$do_app
  (st with refs := [Refv (flatSem$Litv (IntLit 0)); W8array []])
  (Src Opassign) [flatSem$Loc F 1; flatSem$Litv (IntLit 9)]``;
