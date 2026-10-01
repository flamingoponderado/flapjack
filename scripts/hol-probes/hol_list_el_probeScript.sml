(* Original HOL listTheory HD and EL at the pinned HOL revision: types and
   in-range values (HD [] and out-of-range EL are unspecified, so not probed). *)
load "bossLib";
open HolKernel Parse boolLib bossLib listTheory;
val _ = Globals.linewidth := 1000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label c = (print (label ^ "="); print_type (type_of c); print "\n");
val _ = observe_type "hd_type" ``list$HD``;
val _ = observe_type "el_type" ``list$EL``;
val _ = observe "hd_cons" ``HD [3n; 4]``;
val _ = observe "hd_bool" ``HD [F; T]``;
val _ = observe "el_zero" ``EL 0 [5n; 6; 7]``;
val _ = observe "el_last" ``EL 2 [5n; 6; 7]``;
val _ = observe "el_nested" ``EL 1 [[1n]; [2; 3]]``;
val _ = observe "el_large" ``EL 1 [18446744073709551616n; 18446744073709551617]``;
