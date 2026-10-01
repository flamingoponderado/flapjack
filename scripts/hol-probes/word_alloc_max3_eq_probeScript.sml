(* max3_eq is local: replay its literal statement and proof rather than DB.fetch. *)
load "bossLib";
load "miscTheory";
open HolKernel Parse boolLib bossLib miscTheory arithmeticTheory;
val _ = Globals.linewidth := 1000;
val original_max3_eq = prove (``!x y z. max3 x y z = MAX x (MAX y z)``,
  simp[MAX_DEF,max3_def]);
val _ = print "max3_eq_statement=";
val _ = print_term (concl original_max3_eq);
val _ = print "\n";
fun observe label term =
  (print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n");
val _ = observe "max3_zero" ``max3 0 0 0 = 0``;
val _ = observe "max3_x" ``max3 9 4 2 = 9``;
val _ = observe "max3_y" ``max3 2 9 4 = 9``;
val _ = observe "max3_z_after_x" ``max3 4 2 9 = 9``;
val _ = observe "max3_z_after_y" ``max3 2 4 9 = 9``;
val _ = observe "max3_xy_tie" ``max3 9 9 2 = 9``;
val _ = observe "max3_xz_tie" ``max3 9 2 9 = 9``;
val _ = observe "max3_yz_tie" ``max3 2 9 9 = 9``;
val _ = observe "max3_large" ``max3 18446744073709551617 9 18446744073709551616 = 18446744073709551617``;
